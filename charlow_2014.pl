% static semantics

beta_reduce(lambda(Var: InType, Scope: OutType): (InType->OutType),
			Var: InType,
			Scope: OutType).

denotes(pn(Name), Name: e).
denotes(n(Noun), lambda(X: e, NofX: t): (e->t)) :- NofX =.. [Noun, X].
denotes(vi(Verb), lambda(X: e, VofX: t): (e->t)) :- VofX =.. [Verb, X].
denotes(vt(Verb), lambda(Y: e, lambda(X: e, Scope: t): (e->t)): (e->(e->t))) :- Scope =.. [Verb, X, Y].

% alternative semantics

denotes(indef(Pred), A:IT) :-
	denotes(Pred, lambda(X:IT, Scope:OT): (IT->OT)),
	findall(X, Scope, Alts),
	member(A, Alts).

% dynamic semantics

denotes_s(Node, Denot) --> {denotes(Node, Denot)}.
denotes_s(dref(Node), Denot, S0, [Denot|S1]) :- denotes_s(Node, Denot, S0, S1).
denotes_s(pro(Index), X, S, S) :- nth0(Index, S, X).
denotes_s(s(L, and, R), (DL, DR):t) --> {L =.. [s|_], R =.. [s|_]}, denotes_s(L, DL:t), denotes_s(R, DR:t).

denotes_s(Node, Denot) -->
	{Node =.. [Root, L, R]},
	denotes_s(L, DL),
	denotes_s(R, DR),
	{(beta_reduce(DL, DR, Denot) ; beta_reduce(DR, DL, Denot))}.

% model

man(X) :- member(X, [john, bill]).
woman(X) :- member(X, [mary, sally]).

came_in(X) :- member(X, [john, bill, mary]).
sat_down(X) :- member(X, [john, sally]).

saw(john, mary).
saw(bill, mary).
saw(mary, john).
greeted(john, mary).

% check if true/false on the model

truth(D:t) :- call(D).

% sample queries

q0(D, S) :- denotes_s(s(dref(pn(john)), vp(vt(saw), pro(1))), Denot, [mary:e], S).

q1(D, S) :- denotes_s(
						s(
							s(
								dref(pn(john)),
								vp(
									vt(saw),
									dref(pn(mary)))),
							and,
							s(
								pro(1),
								vp(
									vt(greeted),
									pro(0)))),
						D, [], S).

q2(D, S) :- denotes_s(
						s(
							s(
								dref(indef(n(man))),
								vi(came_in)),
							and,
							s(
								pro(0),
								vi(sat_down))),
						D, [], S).

q3(D, S) :- denotes_s(
						s(
							s(
								dref(indef(n(woman))),
								vi(came_in)),
							and,
							s(
								pro(0),
								vi(sat_down))),
						D, [], S).
