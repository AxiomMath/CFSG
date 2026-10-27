module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNHolt

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

section Double

variable {Y : Subgroup X} {c : X} (hY : ∀ y ∈ Y, ∀ y' ∈ Y, Commute y (c⁻¹ * y' * c))

@[expose] def doubleHom : ↥Y →* X :=
  MonoidHom.mk' (fun y => (y : X) * (c⁻¹ * (y : X) * c)) fun u v => by
    simp only [Subgroup.coe_mul]
    calc (u : X) * v * (c⁻¹ * (u * v) * c) = u * (v * (c⁻¹ * u * c)) * (c⁻¹ * v * c) := by
          group
      _ = u * (c⁻¹ * u * c * v) * (c⁻¹ * v * c) := by rw [(hY v v.2 u u.2).eq]
      _ = u * (c⁻¹ * u * c) * (v * (c⁻¹ * v * c)) := by group

omit [Finite X] in
theorem doubleHom_apply (y : ↥Y) : doubleHom hY y = y * (c⁻¹ * y * c) := rfl

omit [Finite X] in
theorem commute_doubleHom_self (hc : c * c = 1) (y : ↥Y) : Commute c (doubleHom hY y) := by
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc
  have h1 := (hY y y.2 y y.2).eq
  rw [doubleHom_apply]
  show c * ((y : X) * (c⁻¹ * y * c)) = (y : X) * (c⁻¹ * y * c) * c
  calc c * ((y : X) * (c⁻¹ * y * c)) = (c⁻¹ * y * c) * y * (c * c) * c := by
        rw [hci, hc, mul_one]; group
    _ = (y : X) * (c⁻¹ * y * c) * c := by rw [hc, mul_one, ← h1]

omit [Finite X] in
theorem commute_doubleHom {h : X} (hhc : Commute h c) (y : ↥Y) (hhy : Commute h y) :
    Commute h (doubleHom hY y) := by
  rw [doubleHom_apply]
  exact hhy.mul_right ((hhc.inv_right.mul_right hhy).mul_right hhc)

omit [Finite X] in
theorem doubleHom_injective {P : Subgroup X} (hYP : ∀ y ∈ Y, c⁻¹ * y * c ∈ P)
    (hP : ∀ y ∈ Y, y ∈ P → y = 1) : Function.Injective (doubleHom hY) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  rw [doubleHom_apply, mul_eq_one_iff_eq_inv] at hy
  refine Subtype.ext (hP y y.2 ?_)
  rw [hy]
  exact inv_mem (hYP y y.2)

end Double

omit [Finite X] in
theorem isElemTwo_range {E : Subgroup X} (hE : IsElemTwo E) (ψ : ↥E →* X) :
    IsElemTwo ψ.range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hE.1 u u.2 v v.2)
  · rintro _ ⟨u, rfl⟩
    rw [← map_mul]
    have : u * u = 1 := Subtype.ext (hE.2 u u.2)
    rw [this, map_one]

omit [Finite X] in
theorem card_range_of_injective {E : Subgroup X} {ψ : ↥E →* X} (hψ : Function.Injective ψ) :
    Nat.card ψ.range = Nat.card E :=
  Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv.symm

theorem card_sup_zpowers {H : Subgroup X} {c : X} (hc : orderOf c = 2) (hcH : c ∉ H)
    (hN : c ∈ normalizer (H : Set X)) : Nat.card ↥(H ⊔ zpowers c) = 2 * Nat.card H := by
  have h1 := GrS4.card_sup_mul_inf_eq_mul_of_normalizes (H := zpowers c) (K := H)
    (zpowers_le.mpr hN)
  have h2 : zpowers c ⊓ H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    by_contra hne
    exact hcH (eq_of_mem_zpowers_of_ne_one hc hx1 hne ▸ hx2)
  rw [h2, card_bot, mul_one, Nat.card_zpowers, hc, sup_comm] at h1
  exact h1

omit [Finite X] in
theorem conjugate_eq_conjugate_iff {K : Subgroup X} {g k : X} :
    conjugate K g = conjugate K k ↔ g * k⁻¹ ∈ normalizer (K : Set X) := by
  constructor
  · intro h
    apply mem_normalizer_of_conjugate_eq
    rw [← conjugate_conjugate, h, conjugate_conjugate, mul_inv_cancel, conjugate_one]
  · intro h
    rw [show g = g * k⁻¹ * k by group, ← conjugate_conjugate, conjugate_eq_of_mem_normalizer h]

theorem eq_zpowers_of_card_two {H : Subgroup X} (hH : Nat.card H = 2) {f : X} (hfH : f ∈ H)
    (hf1 : f ≠ 1) : H = zpowers f := by
  have hf2 : orderOf f = 2 := by
    have h1 := Subgroup.orderOf_dvd_natCard H hfH
    rw [hH] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hf1
    · exact h
  exact (eq_of_le_of_card_ge (zpowers_le.mpr hfH) (by rw [Nat.card_zpowers, hf2, hH])).symm

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

theorem commute_conj {T : Subgroup X} (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X))
    {x y g k : X} (hx : x ∈ T ⊓ K) (hy : y ∈ T ⊓ K) (hg : g ∈ T) (hk : k ∈ T)
    (hne : conjugate K g ≠ conjugate K k) : Commute (g⁻¹ * x * g) (k⁻¹ * y * k) := by
  have hgK := conj_mem_conjugate (mem_inf.mp hx).2 g
  have hkK := conj_mem_conjugate (mem_inf.mp hy).2 k
  have hc := GrS5.commutator_le_inf_oddIn (conjugate_le_of_mem h.le_normalizer (hTM hg))
    (conjugate_le_of_mem h.le_normalizer (hTM hk))
    (isPComponent_conjugate_subgroupOf (hTM hg) h.isPComponent_K)
    (isPComponent_conjugate_subgroupOf (hTM hk) h.isPComponent_K) hne
  have h1 := (mem_inf.mp (hc (commutator_mem_commutator hgK hkK))).1
  have hgT : g⁻¹ * x * g ∈ T := mul_mem (mul_mem (inv_mem hg) (mem_inf.mp hx).1) hg
  have hkT : k⁻¹ * y * k ∈ T := mul_mem (mul_mem (inv_mem hk) (mem_inf.mp hy).1) hk
  have h2 : ⁅g⁻¹ * x * g, k⁻¹ * y * k⁆ ∈ T := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hgT hkT) (inv_mem hgT)) (inv_mem hkT)
  exact commutatorElement_eq_one_iff_mul_comm.mp (HeDiag.eq_one_of_mem_oddIn hT2 h2 h1)

theorem commute_conj_one {T : Subgroup X} (hT2 : IsPGroup 2 T)
    (hTM : T ≤ normalizer (W : Set X)) {x y k : X} (hx : x ∈ T ⊓ K) (hy : y ∈ T ⊓ K)
    (hk : k ∈ T) (hne : conjugate K k ≠ K) : Commute x (k⁻¹ * y * k) := by
  have h1 := h.commute_conj hT2 hTM hx hy (one_mem T) hk (by rw [conjugate_one]; exact hne.symm)
  rwa [inv_one, one_mul, mul_one] at h1

theorem conj_mem_coreActionKernel {T : Subgroup X} (hTM : T ≤ normalizer (W : Set X))
    {x k : X} (hx : x ∈ K) (hk : k ∈ T) (hne : conjugate K k ≠ K) :
    k⁻¹ * x * k ∈ coreActionKernel K :=
  le_coreActionKernel_of_ne h.le_normalizer (conjugate_le_of_mem h.le_normalizer (hTM hk))
    h.isPComponent_K (isPComponent_conjugate_subgroupOf (hTM hk) h.isPComponent_K)
    (Ne.symm hne) (conj_mem_conjugate hx k)

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
