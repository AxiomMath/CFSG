module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankTwoCoverUnitaryAbelian
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverNorm

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open scoped commutatorElement
open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

variable {J : Type*} [Group J]

theorem commutatorElement_mul_right_of_central {x y y' : J}
    (hy' : ∀ g, g * ⁅x, y'⁆ = ⁅x, y'⁆ * g) :
    ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  have h2 : x * y' * x⁻¹ = ⁅x, y'⁆ * y' := by rw [commutatorElement_def]; group
  calc ⁅x, y * y'⁆ = (x * y * x⁻¹) * (x * y' * x⁻¹) * y'⁻¹ * y⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅x, y⁆ * (y * ⁅x, y'⁆) * y⁻¹ := by rw [h1, h2]; group
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := by rw [hy' y]; group

@[expose] noncomputable def coverPairing (a ω : J ⧸ Subgroup.center J) : ZMod 2 :=
  neOneIndicator ⁅Quotient.out a, Quotient.out ω⁆

theorem coverPairing_mk (x y : J) :
    coverPairing (x : J ⧸ Subgroup.center J) (y : J ⧸ Subgroup.center J) =
      neOneIndicator ⁅x, y⁆ := by
  rw [coverPairing, commutatorElement_eq_of_mk_eq (QuotientGroup.out_eq' _).symm
    (QuotientGroup.out_eq' _).symm]

theorem coverPairing_conj (a ω d : J ⧸ Subgroup.center J) :
    coverPairing (d⁻¹ * a * d) ω = coverPairing a (d * ω * d⁻¹) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective d
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, coverPairing_mk, coverPairing_mk]
  have heq : ⁅g⁻¹ * x * g, y⁆ = g⁻¹ * ⁅x, g * y * g⁻¹⁆ * g := by
    rw [commutatorElement_def, commutatorElement_def]; group
  have hiff : ⁅g⁻¹ * x * g, y⁆ = 1 ↔ ⁅x, g * y * g⁻¹⁆ = 1 := by
    rw [heq]
    constructor
    · intro h
      calc ⁅x, g * y * g⁻¹⁆ = g * (g⁻¹ * ⁅x, g * y * g⁻¹⁆ * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]; group
  by_cases h : ⁅x, g * y * g⁻¹⁆ = 1
  · rw [h, hiff.mpr h]
  · have h' : ⁅g⁻¹ * x * g, y⁆ ≠ 1 := fun h'' => h (hiff.mp h'')
    simp [neOneIndicator, h, h']

variable {Q : Subgroup J} {u : J}

theorem commutatorElement_mem_center_of_inCenterOf {x y : J} (hx : x ∈ Q)
    (hy : InCenterOf (centralImage Q) (y : J ⧸ Subgroup.center J)) :
    ⁅x, y⁆ ∈ Subgroup.center J := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, commutatorElement_eq_one_iff_mul_comm]
  exact (hy.2 _ (Subgroup.mem_map_of_mem _ hx)).eq

theorem commutatorElement_sq_of_inCenterOf {x y : J} (hx : x ∈ Q)
    (hy : InCenterOf (centralImage Q) (y : J ⧸ Subgroup.center J))
    (hy2 : (y : J ⧸ Subgroup.center J) * (y : J ⧸ Subgroup.center J) = 1) :
    ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
  have hc := Subgroup.mem_center_iff.mp (commutatorElement_mem_center_of_inCenterOf hx hy)
  have hyy : y * y ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hy2
  rw [← commutatorElement_sq_of_central hc, commutatorElement_def,
    Subgroup.mem_center_iff.mp hyy x, mul_inv_cancel_right, mul_inv_cancel]

theorem eq_or_eq_one_of_center (hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = u)
    {s t : J} (hs : s ∈ Subgroup.center J) (ht : t ∈ Subgroup.center J) (hs2 : s * s = 1)
    (ht2 : t * t = 1) : s = 1 ∨ t = 1 ∨ s = t := by
  rcases hu s hs hs2 with h | h
  · exact Or.inl h
  · rcases hu t ht ht2 with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))

variable (hZQ : Subgroup.center J ≤ Q) (hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = u)
include hZQ hu

theorem coverPairing_mul_left {a a' ω : J ⧸ Subgroup.center J} (ha : a ∈ centralImage Q)
    (ha' : a' ∈ centralImage Q) (hω : InCenterOf (centralImage Q) ω) (hω2 : ω * ω = 1) :
    coverPairing (a * a') ω = coverPairing a ω + coverPairing a' ω := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω
  have hx : x ∈ Q := (mk_mem_centralImage_iff hZQ).mp ha
  have hx' : x' ∈ Q := (mk_mem_centralImage_iff hZQ).mp ha'
  have hc := commutatorElement_mem_center_of_inCenterOf hx hω
  have hc' := commutatorElement_mem_center_of_inCenterOf hx' hω
  rw [← QuotientGroup.mk_mul, coverPairing_mk, coverPairing_mk, coverPairing_mk,
    commutatorElement_mul_left_of_central (Subgroup.mem_center_iff.mp hc'),
    neOneIndicator_mul (eq_or_eq_one_of_center hu hc' hc
      (commutatorElement_sq_of_inCenterOf hx' hω hω2)
      (commutatorElement_sq_of_inCenterOf hx hω hω2))
      (commutatorElement_sq_of_inCenterOf hx' hω hω2), add_comm]

theorem coverPairing_mul_right {a ω ω' : J ⧸ Subgroup.center J} (ha : a ∈ centralImage Q)
    (hω : InCenterOf (centralImage Q) ω) (hω' : InCenterOf (centralImage Q) ω')
    (hω2 : ω * ω = 1) (hω'2 : ω' * ω' = 1) :
    coverPairing a (ω * ω') = coverPairing a ω + coverPairing a ω' := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective ω'
  have hx : x ∈ Q := (mk_mem_centralImage_iff hZQ).mp ha
  have hc := commutatorElement_mem_center_of_inCenterOf hx hω
  have hc' := commutatorElement_mem_center_of_inCenterOf hx hω'
  rw [← QuotientGroup.mk_mul, coverPairing_mk, coverPairing_mk, coverPairing_mk,
    commutatorElement_mul_right_of_central (Subgroup.mem_center_iff.mp hc'),
    neOneIndicator_mul (eq_or_eq_one_of_center hu hc hc'
      (commutatorElement_sq_of_inCenterOf hx hω hω2)
      (commutatorElement_sq_of_inCenterOf hx hω' hω'2))
      (commutatorElement_sq_of_inCenterOf hx hω hω2)]

omit hu in
theorem coverPairing_eq_zero_of_inCenterOf
    (hab : ∀ x y : J, x ∈ Q → y ∈ Q → InCenterOf (centralImage Q) (x : J ⧸ Subgroup.center J) →
      InCenterOf (centralImage Q) (y : J ⧸ Subgroup.center J) → x * y = y * x)
    {a ω : J ⧸ Subgroup.center J} (ha : InCenterOf (centralImage Q) a)
    (hω : InCenterOf (centralImage Q) ω) : coverPairing a ω = 0 := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [coverPairing_mk, commutatorElement_eq_one_iff_mul_comm.mpr
    (hab x y ((mk_mem_centralImage_iff hZQ).mp ha.1) ((mk_mem_centralImage_iff hZQ).mp hω.1)
      ha hω), neOneIndicator_one]

end CFSG.ProperTwoGeneratedCore.Lemma37
