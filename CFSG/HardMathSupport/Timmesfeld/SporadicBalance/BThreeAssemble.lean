module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BTwoBLocal
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeAInv

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Monster.GMS
  CFSG.Blueprint.NativeSporadic CFSG.Monster.B CFSG.Monster.Existence CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Amalgam

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

theorem orderOf_conj_eq_self {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using MulEquiv.orderOf_eq (MulAut.conj g) x

end Generic

section Reps


theorem gLAPPrimeCoreOf_B_eq_bot_of_inverted_by_babyInv_zero {x d : B} (hx : orderOf x = 3)
    (hd : BabyInv 0 d) (hinv : d * x * d⁻¹ = x⁻¹) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set B)) = ⊥ := by
  have hcls : ∀ t : B, BabyInv 0 t → IsConj t (babyRep 1) := fun t ht =>
    babyTableIII.2 0 t (babyRep 1) ht babyInv_zero_babyRep_one
  obtain ⟨v, hv⟩ := (babyInv_zero_iff_clabelS hcls d).1 hd
  have hx' : orderOf (babyToShat x) = 3 := by
    rw [← hx]
    with_reducible_and_instances exact MulEquiv.orderOf_eq babyToShat x
  have hS : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({babyToShat x} : Set Shat)) = ⊥ := by
    refine gLAPPrimeCoreOf_eq_bot_of_inverted_by_label hx' (x := v) ?_
    rw [hv, ← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  with_reducible_and_instances exact gLAPPrimeCoreOf_centralizer_eq_bot_of_mulEquiv babyToShat hS

theorem oPrimeCoreTrivialAt_B_three_of_reps (r : Fin 4 → B)
    (hcls : ∀ s : B, orderOf s = 3 → ∃ i, IsConj s (r i))
    (h0 : ∃ d : B, BabyInv 0 d ∧ d * r 0 * d⁻¹ = (r 0)⁻¹)
    (h13 : 3 ^ 13 ∣ Nat.card (Subgroup.centralizer ({r 1} : Set B)))
    (hK : ∃ a b : B, a ∈ Subgroup.centralizer ({r 1} : Set B) ∧
      b ∈ Subgroup.centralizer ({r 1} : Set B) ∧ BabyInv 1 a ∧ BabyInv 1 b ∧ BabyInv 1 (a * b))
    (h2 : IsConj (r 2) (r 0)) (h3 : IsConj (r 3) (r 1)) :
    OPrimeCoreTrivialAt 3 B := by
  have hA : ∀ s : B, orderOf s = 3 → IsConj s (r 0) →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)) = ⊥ := by
    intro s hs hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    rw [← gLAPPrimeCoreOf_centralizer_conj g s, hg]
    obtain ⟨d, hd, hinv⟩ := h0
    have hr : orderOf (r 0) = 3 := by rw [← hg, orderOf_conj_eq_self]; exact hs
    exact gLAPPrimeCoreOf_B_eq_bot_of_inverted_by_babyInv_zero hr hd hinv
  have hB : ∀ s : B, orderOf s = 3 → IsConj s (r 1) →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set B)) = ⊥ := by
    intro s hs hc
    obtain ⟨g, hg⟩ := isConj_iff.1 hc
    rw [← gLAPPrimeCoreOf_centralizer_conj g s, hg]
    obtain ⟨a, b, haC, hbC, ha, hb, hab⟩ := hK
    have hr : orderOf (r 1) = 3 := by rw [← hg, orderOf_conj_eq_self]; exact hs
    exact gLAPPrimeCoreOf_B_eq_bot_of_three_central_twoB hr h13 haC hbC ha hb hab
  intro s hs
  obtain ⟨i, hi⟩ := hcls s hs
  fin_cases i
  · exact hA s hs hi
  · exact hB s hs hi
  · exact hA s hs (hi.trans h2)
  · exact hB s hs (hi.trans h3)

end Reps

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
