module

public import CFSG.RankThree.Lattice.SteinbergBIListMatrix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Blueprint.Chevalley

@[expose] def reflV (i : Fin Tag.E6.rank) (x : Fin Tag.E6.rank → ZMod 3) :
    Fin Tag.E6.rank → ZMod 3 :=
  fun j => x j - (Tag.E6.cartan i j : ZMod 3) * x i

@[expose] def gWord : List (Fin Tag.E6.rank) := [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3]

@[expose] def gAct (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ZMod 3 :=
  gWord.foldr reflV x

@[expose] def x0 : Fin Tag.E6.rank → ZMod 3 := Pi.single 3 1

private theorem reflV_add (i : Fin Tag.E6.rank) (x y : Fin Tag.E6.rank → ZMod 3) :
    reflV i (x + y) = reflV i x + reflV i y := by
  funext j
  simp only [reflV, Pi.add_apply]
  ring

private theorem reflV_smul (i : Fin Tag.E6.rank) (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    reflV i (c • x) = c • reflV i x := by
  funext j
  simp only [reflV, Pi.smul_apply, smul_eq_mul]
  ring

private theorem foldr_reflV_add (l : List (Fin Tag.E6.rank)) (x y : Fin Tag.E6.rank → ZMod 3) :
    l.foldr reflV (x + y) = l.foldr reflV x + l.foldr reflV y := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, ih, reflV_add]

private theorem foldr_reflV_smul (l : List (Fin Tag.E6.rank)) (c : ZMod 3)
    (x : Fin Tag.E6.rank → ZMod 3) : l.foldr reflV (c • x) = c • l.foldr reflV x := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, ih, reflV_smul]

private theorem gAct_add (x y : Fin Tag.E6.rank → ZMod 3) : gAct (x + y) = gAct x + gAct y :=
  foldr_reflV_add gWord x y

private theorem gAct_smul (c : ZMod 3) (x : Fin Tag.E6.rank → ZMod 3) :
    gAct (c • x) = c • gAct x :=
  foldr_reflV_smul gWord c x

private theorem basis_pow_nine :
    ∀ j : Fin Tag.E6.rank, gAct^[9] (Pi.single j 1) = Pi.single j 1 := by
  decide +kernel

private theorem gAct_pow_nine_aux (x : Fin Tag.E6.rank → ZMod 3) : gAct^[9] x = x := by
  obtain ⟨g, hg⟩ : ∃ g : Module.End (ZMod 3) (Fin Tag.E6.rank → ZMod 3), ∀ y, g y = gAct y :=
    ⟨{ toFun := gAct, map_add' := gAct_add, map_smul' := fun c y => gAct_smul c y }, fun _ => rfl⟩
  have hfun : ⇑g = gAct := funext hg
  have hpow : g ^ 9 = 1 := (Pi.basisFun (ZMod 3) (Fin Tag.E6.rank)).ext fun j => by
    rw [Pi.basisFun_apply, Module.End.one_apply, Module.End.pow_apply, hfun]
    exact basis_pow_nine j
  calc gAct^[9] x = (g ^ 9) x := by rw [Module.End.pow_apply, hfun]
    _ = x := by rw [hpow, Module.End.one_apply]

private theorem gAct_eq_self_iff_aux :
    ∀ x : Fin Tag.E6.rank → ZMod 3, gAct x = x ↔ ∃ c : ZMod 3, x = c • x0 := by
  decide +kernel

theorem gAct_pow_nine (x : Fin Tag.E6.rank → ZMod 3) : gAct^[9] x = x :=
  gAct_pow_nine_aux x

theorem gAct_eq_self_iff (x : Fin Tag.E6.rank → ZMod 3) : gAct x = x ↔ ∃ c : ZMod 3, x = c • x0 :=
  gAct_eq_self_iff_aux x

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
