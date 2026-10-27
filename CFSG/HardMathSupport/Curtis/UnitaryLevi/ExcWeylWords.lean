module

public import CFSG.LieType.Chevalley.LatticeWeylGroup

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

variable (τ : Tag)

@[expose] noncomputable def Smat (i : Fin τ.rank) : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
  1 - Matrix.of fun k j => if k = i then τ.cartan i j else 0

theorem reflect_eq_mulVec (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    reflect τ i v = (Smat τ i).mulVec v := by
  ext k
  simp [reflect, Smat, Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.one_apply,
    sub_mul, Finset.sum_sub_distrib, Pi.single_apply]


theorem wordSmul (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    ((l.map (simple τ)).prod) • v = ((l.map (Smat τ)).prod).mulVec v := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, simple_smul, reflect_eq_mulVec,
      Matrix.mulVec_mulVec, List.map_cons, List.prod_cons]

theorem word_eq_of_matrix_eq (l l' : List (Fin τ.rank))
    (h : (l.map (Smat τ)).prod = (l'.map (Smat τ)).prod) :
    (l.map (simple τ)).prod = (l'.map (simple τ)).prod := by
  apply weylToAut_injective (τ := τ)
  refine Units.ext (LinearMap.ext fun v => ?_)
  rw [weylToAut_apply, weylToAut_apply, wordSmul, wordSmul, h]


@[expose] def wordW (l : List (Fin τ.rank)) : WeylGroup τ := (l.map (simple τ)).prod

theorem wordW_append (l l' : List (Fin τ.rank)) : wordW τ (l ++ l') = wordW τ l * wordW τ l' := by
  simp [wordW, List.map_append, List.prod_append]

theorem wordW_replicate (l : List (Fin τ.rank)) (n : ℕ) :
    wordW τ (List.replicate n l).flatten = wordW τ l ^ n := by
  induction n with
  | zero => simp [wordW]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, wordW_append, ih, pow_succ']

theorem wordW_smul (l : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    wordW τ l • v = ((l.map (Smat τ)).prod).mulVec v := wordSmul τ l v

theorem wordW_eq_of_matrix (l l' : List (Fin τ.rank))
    (h : (l.map (Smat τ)).prod = (l'.map (Smat τ)).prod) : wordW τ l = wordW τ l' :=
  word_eq_of_matrix_eq τ l l' h

theorem matrix_eq_of_wordW_eq (l l' : List (Fin τ.rank)) (h : wordW τ l = wordW τ l') :
    (l.map (Smat τ)).prod = (l'.map (Smat τ)).prod := by
  ext i j
  have := congrFun (congrArg (fun w : WeylGroup τ => w • (Pi.single j 1 : Fin τ.rank → ℤ)) h) i
  simpa [wordW_smul, Matrix.mulVec_single] using this

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
