module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Second

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace GMS43

namespace Hyp

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}
  {T V₁ U₁ : Subgroup G} {y d : G} (h : Hyp L f t T V₁ U₁ y d)
include h

theorem relIndex_le_of_relIndex_eq_two (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t)
    (hTV : (T ⊓ L ⊔ zpowers t).relIndex T = 2) {S : Subgroup G} (hSp : IsPGroup 2 S)
    (hSN : S ≤ normalizer (U₁ : Set G)) (hES : U₁ ⊔ T ≤ S) {X : Subgroup G} (hXS : X ≤ S)
    (hX2 : ∀ x ∈ X, x * x = 1) :
    U₁.relIndex X ≤ 4 ∧ (X ⊓ (U₁ ⊔ T) ≤ U₁ → U₁.relIndex X ≤ 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUS : U₁ ≤ S := le_sup_left.trans hES
  have : (U₁.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hUS).mpr hSN
  set N := U₁.subgroupOf S with hN
  set π : S →* S ⧸ N := QuotientGroup.mk' N with hπ
  have hQp : IsPGroup 2 (S ⧸ N) := hSp.to_quotient N
  have heq : ∀ a b : S, π a = π b ↔ (a : G)⁻¹ * b ∈ U₁ := fun a b => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      mem_subgroupOf]
    rfl
  have heq1 : ∀ a : S, π a = 1 ↔ (a : G) ∈ U₁ := fun a => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
  have hcard : ∀ Y : Subgroup G, Y ≤ S → Nat.card ((Y.subgroupOf S).map π) = U₁.relIndex Y := by
    intro Y hY
    rw [← relIndex_ker, hπ, QuotientGroup.ker_mk', hN, relIndex_subgroupOf hY]
  have hsq : ∀ Y : Subgroup G, (∀ y ∈ Y, y * y ∈ U₁) →
      ∀ v ∈ (Y.subgroupOf S).map π, v * v = 1 := by
    rintro Y hY _ ⟨a, ha, rfl⟩
    rw [← map_mul, heq1]
    exact hY _ (mem_subgroupOf.mp ha)
  set Vb := ((U₁ ⊔ T).subgroupOf S).map π with hVb
  have htS : t ∈ S := hES (mem_sup_right h.mem_T)
  set j := π ⟨t, htS⟩ with hj
  have hjV : j ∈ Vb := ⟨⟨t, htS⟩, mem_subgroupOf.mpr (mem_sup_right h.mem_T), rfl⟩
  have hV2 : ∀ v ∈ Vb, v * v = 1 :=
    hsq _ fun w hw => h.mul_self_mem_of_relIndex_eq_two hTV hx hw
  have hV4 : Nat.card Vb = 4 := by
    rw [hVb, hcard _ hES, h.relIndex_sup_eq, h.relIndex_U_T, hTV]
  have hC : centralizer ({j} : Set (S ⧸ N)) ≤ Vb := by
    intro c hc
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective N c
    have hcomm : π s * j = j * π s := mem_centralizer_singleton_iff.mp hc
    have h1 : π (s * ⟨t, htS⟩ * s⁻¹) = π ⟨t, htS⟩ := by
      rw [map_mul, map_mul, map_inv, ← hj, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := (heq _ _).mp h1.symm
    have h3 : t * ((s : G) * t * (s : G)⁻¹) ∈ U₁ := by
      have h4 : ((⟨t, htS⟩ : S) : G)⁻¹ * ((s * ⟨t, htS⟩ * s⁻¹ : S) : G) =
          t⁻¹ * ((s : G) * t * (s : G)⁻¹) := rfl
      rw [h4, h.t_inv] at h2
      exact h2
    exact ⟨s, mem_subgroupOf.mpr (h.mem_sup_of_mul_conj_mem hSp hES s.2 h3), rfl⟩
  have hX2' : ∀ v ∈ (X.subgroupOf S).map π, v * v = 1 :=
    hsq X fun x hx => by rw [hX2 x hx]; exact one_mem _
  refine ⟨?_, fun hXE => ?_⟩
  · rw [← hcard X hXS]
    exact card_le_four_of_centralizer_le hQp hV4 hV2 hjV hC hX2'
  · rw [← hcard X hXS]
    refine card_le_two_of_inf_eq_bot hQp hV4 hV2 hjV hC hX2' ?_
    rw [eq_bot_iff]
    rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    rw [mem_bot, heq1]
    have h1 := (heq b a).mp hab
    have haS₀ : (a : G) ∈ U₁ ⊔ T := by
      rw [show (a : G) = b * ((b : G)⁻¹ * a) by group]
      exact mul_mem (mem_subgroupOf.mp hb) (mem_sup_left h1)
    exact hXE (mem_inf.mpr ⟨mem_subgroupOf.mp ha, haS₀⟩)

theorem false_of_relIndex_le_two (hx : ∃ x ∈ U₁ ⊔ T, x * x = 1 ∧ x ∉ U₁ ⊔ zpowers t)
    (hTV : (T ⊓ L ⊔ zpowers t).relIndex T ≤ 2) : False := by
  obtain ⟨S, hsyl, hES⟩ := h.exists_isSylowOf_le_normalizer
  have h2 : (T ⊓ L ⊔ zpowers t).relIndex T = 2 := by
    rcases h.relIndex_eq_two_or_four_le hx with h2 | h4
    · exact h2
    · omega
  refine h.false_of_commutator_bound (le_sup_left.trans hES) hsyl fun U hU g hUS hUE => ?_
  have hX2 := h.rightConjugate_mul_self hU g
  obtain ⟨h4, h2'⟩ := h.relIndex_le_of_relIndex_eq_two hx h2 hsyl.isPGroup hsyl.le hES hUS hX2
  have h8 := h.eight_le
  by_cases hX0 : rightConjugate U g ⊓ (U₁ ⊔ T) ≤ U₁
  · obtain ⟨w, hwX, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hUE
    have hw0 : w ∉ U₁ ⊔ T := fun hw0 => hwE (hX0 (mem_inf.mpr ⟨hwX, hw0⟩))
    have hC := h.card_inf_centralizer_sq_le_of_not_mem hsyl.isPGroup hsyl.le hES (hUS hwX) hw0
    refine ⟨w, hwX, lt_card_commutator_of_mul_lt h.comm (hsyl.le (hUS hwX)) ?_⟩
    rw [h.card_U₁]
    have hr := h2' hX0
    set c := Nat.card (U₁ ⊓ centralizer ({w} : Set G) : Subgroup G)
    set r := U₁.relIndex (rightConjugate U g)
    set q := 2 ^ f
    by_contra hle
    push Not at hle
    have h1 : (q ^ 2) ^ 2 ≤ (c * r) ^ 2 := Nat.pow_le_pow_left hle 2
    have hr2 : r ^ 2 ≤ 4 := by nlinarith
    have h3 : (c * r) ^ 2 ≤ q ^ 3 * 4 := by
      rw [mul_pow]
      exact Nat.mul_le_mul hC hr2
    have h5 : q ^ 3 * q ≤ q ^ 3 * 4 := by
      calc q ^ 3 * q = (q ^ 2) ^ 2 := by ring
        _ ≤ _ := h1.trans h3
    have hq3 : 0 < q ^ 3 := by positivity
    have := Nat.le_of_mul_le_mul_left h5 hq3
    omega
  · obtain ⟨w, hw, hwE⟩ := IsConcreteLE.not_le_iff_exists.mp hX0
    obtain ⟨hwX, hw0⟩ := mem_inf.mp hw
    have hC := h.card_inf_centralizer_le hw0 hwE
    refine ⟨w, hwX, lt_card_commutator_of_mul_lt h.comm (hsyl.le (hUS hwX)) ?_⟩
    rw [h.card_U₁]
    calc _ ≤ 2 ^ f * 4 := Nat.mul_le_mul hC h4
      _ < 2 ^ f * 2 ^ f := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      _ = (2 ^ f) ^ 2 := (sq _).symm

end Hyp

end GMS43

end CFSG.SeitzReduction.RankOne
