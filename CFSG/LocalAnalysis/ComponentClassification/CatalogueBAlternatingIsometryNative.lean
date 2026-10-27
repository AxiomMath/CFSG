module

public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBAlternatingIsometry

open CFSG.Assembly.LowTwoRank

@[expose] def symplecticRingEquiv {K F : Type*} [Field K] [Field F]
    (m : ℕ) (e : K ≃+* F) :
    TauCeti.GLSymplectic (Fin m) K ≃* TauCeti.GLSymplectic (Fin m) F where
  toFun := TauCeti.GLSymplectic.map (Fin m) e.toRingHom
  invFun := TauCeti.GLSymplectic.map (Fin m) e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  right_inv A := by
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  map_mul' := (TauCeti.GLSymplectic.map (Fin m) e.toRingHom).map_mul

theorem symplecticRingEquiv_apply {K F : Type*} [Field K] [Field F]
    (m : ℕ) (e : K ≃+* F) (A : TauCeti.GLSymplectic (Fin m) K)
    (i j : Fin m ⊕ Fin m) :
    (symplecticRingEquiv m e A).val.val i j = e (A.val.val i j) := by
  change (TauCeti.GLSymplectic.map (Fin m) e.toRingHom A).val.val i j = _
  rw [TauCeti.GLSymplectic.coe_map]
  rfl

private theorem symplectic_quasisimple_typeZero (K : Type) [Field K]
    (m : ℕ) (hm : 1 ≤ m)
    (h : (Infinite K ∨ 4 ≤ Nat.card K) ∨
      (Nat.card K = 3 ∧ 2 ≤ m) ∨ (Nat.card K = 2 ∧ 3 ≤ m)) :
    CFSG.IsQuasisimple (TauCeti.GLSymplectic (Fin m) K) := by
  let : Group.IsPerfect (TauCeti.GLSymplecticFin m K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin K m h
  let : Group.IsPerfect (TauCeti.GLSymplectic (Fin m) K) :=
    Group.IsPerfect.ofSurjective
      (f := (TauCeti.GLSymplecticFin.mulEquivGLSymplectic m K).toMonoidHom)
      (TauCeti.GLSymplecticFin.mulEquivGLSymplectic m K).surjective
  have hs : IsSimpleGroup (StatedProj (StatedSp m K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K m hm h
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic] at hs
  have hz := CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq (n := m) (K := K)
  apply CatalogueBAlternating.quasisimple_iff_native.mpr
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  let : IsSimpleGroup (StatedProj (TauCeti.GLSymplectic (Fin m) K)) := hs
  exact (QuotientGroup.quotientMulEquivOfEq hz).isSimpleGroup

theorem symplectic_quasisimple (K : Type*) [Field K] [Finite K]
    (m : ℕ) (hm : 1 ≤ m) (hodd : Odd (Nat.card K))
    (hexception : m ≠ 1 ∨ Nat.card K ≠ 3) :
    CFSG.IsQuasisimple (TauCeti.GLSymplectic (Fin m) K) := by
  let F := Shrink.{0} K
  have hcard : Nat.card F = Nat.card K := Nat.card_congr (Shrink.ringEquiv.{0} K).toEquiv
  have htwo : 2 ≤ Nat.card K := Nat.succ_le_iff.mpr Finite.one_lt_card
  have hne2 : Nat.card K ≠ 2 := by
    intro h2
    rw [h2] at hodd
    norm_num at hodd
  have hcases : (Infinite F ∨ 4 ≤ Nat.card F) ∨
      (Nat.card F = 3 ∧ 2 ≤ m) ∨ (Nat.card F = 2 ∧ 3 ≤ m) := by
    by_cases h3 : Nat.card K = 3
    · exact Or.inr (Or.inl ⟨hcard.trans h3, by rcases hexception with hm1 | hne3 <;> omega⟩)
    · exact Or.inl (Or.inr (by omega))
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv
      (symplecticRingEquiv m (Shrink.ringEquiv.{0} K).symm)
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (symplectic_quasisimple_typeZero F m hm hcases)))

end CFSG.ComponentClassification.CatalogueBAlternatingIsometry
