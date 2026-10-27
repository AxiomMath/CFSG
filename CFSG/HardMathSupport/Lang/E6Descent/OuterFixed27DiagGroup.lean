module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

open scoped Pointwise

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent.DiagGroup

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_sup_right_of_le_normalizer (D C : Subgroup G) (h : D ≤ Subgroup.normalizer (C : Set G)) :
    C.relIndex (D ⊔ C) = C.relIndex D := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact (Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient D C h).toEquiv).symm

theorem relIndex_sup_sup (C M D : Subgroup G) (hMC : M ≤ C) (hDC : D ≤ Subgroup.normalizer (C : Set G))
    (hDM : D ≤ Subgroup.normalizer (M : Set G)) (hinf : D ⊓ C = D ⊓ M) :
    (D ⊔ M).relIndex (D ⊔ C) = M.relIndex C := by
  have hNA : D ⊔ M ≤ D ⊔ C := sup_le_sup_left hMC D
  have e1 := relIndex_sup_right_of_le_normalizer D C hDC
  have e2 := relIndex_sup_right_of_le_normalizer D M hDM
  have e3 := Subgroup.relIndex_mul_relIndex M (D ⊔ M) (D ⊔ C) le_sup_right hNA
  have e4 := Subgroup.relIndex_mul_relIndex M C (D ⊔ C) hMC le_sup_right
  have e5 : C.relIndex D = M.relIndex D := by
    rw [← Subgroup.inf_relIndex_right C D, ← Subgroup.inf_relIndex_right M D, inf_comm C D,
      inf_comm M D, hinf]
  have hne : C.relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [e1] at e4
  rw [e2, ← e5] at e3
  have : C.relIndex D * (D ⊔ M).relIndex (D ⊔ C) = C.relIndex D * M.relIndex C := by
    rw [mul_comm (C.relIndex D) (M.relIndex C), e4, ← e3, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) this

theorem exists_conj_mem_mul (C M D : Subgroup G) (hMC : M ≤ C) (hDC : D ≤ Subgroup.normalizer (C : Set G))
    (hDM : D ≤ Subgroup.normalizer (M : Set G)) (hinf : D ⊓ C = D ⊓ M) (hM3 : ¬ 3 ∣ M.relIndex C) {x : G}
    (hx : x ∈ D ⊔ C) (hx3 : x ^ 3 = 1) :
    ∃ u ∈ D ⊔ C, ∃ d ∈ D, ∃ m ∈ M, u⁻¹ * x * u = d * m := by
  classical
  have hidx := relIndex_sup_sup C M D hMC hDC hDM hinf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A := D ⊔ C with hA
  set x' : A := ⟨x, hx⟩ with hx'
  have hx'3 : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hpg : IsPGroup 3 (Subgroup.zpowers x') := by
    rintro ⟨g, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (x' ^ k) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'3, one_zpow]
  have hcard : ¬ 3 ∣ Nat.card (A ⧸ (D ⊔ M).subgroupOf A) := by
    have h : Nat.card (A ⧸ (D ⊔ M).subgroupOf A) = (D ⊔ M).relIndex (D ⊔ C) := rfl
    rw [h, hidx]
    exact hM3
  obtain ⟨Q, hQ⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card (A ⧸ (D ⊔ M).subgroupOf A) hcard
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective Q
  have hfix := hQ ⟨x', Subgroup.mem_zpowers x'⟩
  change ((x' * z : A) : A ⧸ (D ⊔ M).subgroupOf A) = (z : A ⧸ (D ⊔ M).subgroupOf A) at hfix
  rw [QuotientGroup.eq] at hfix
  have h2 : z⁻¹ * x' * z ∈ (D ⊔ M).subgroupOf A := by
    have := inv_mem hfix
    simpa [mul_assoc] using this
  have h3 : (z : G)⁻¹ * x * z ∈ D ⊔ M := Subgroup.mem_subgroupOf.1 h2
  have h4 : (z : G)⁻¹ * x * z ∈ (D : Set G) * (M : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D M hDM]
    exact h3
  obtain ⟨d, hd, m, hm, hdm⟩ := h4
  exact ⟨z, z.2, d, hd, m, hm, hdm.symm⟩

theorem card_centralizer_inf_conj (C : Subgroup G) {u : G}
    (hu : u ∈ Subgroup.normalizer (C : Set G)) (x : G) :
    Nat.card ↥(Subgroup.centralizer {u⁻¹ * x * u} ⊓ C) =
      Nat.card ↥(Subgroup.centralizer {x} ⊓ C) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj u).toEquiv fun c => ?_)
  have he : (MulAut.conj u).toEquiv c = u * c * u⁻¹ := rfl
  rw [he, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  have hC : c ∈ C ↔ u * c * u⁻¹ ∈ C := Subgroup.mem_normalizer_iff.1 hu c
  refine and_congr ?_ hC
  constructor
  · intro h
    calc u * c * u⁻¹ * x = u * (c * (u⁻¹ * x * u)) * u⁻¹ := by group
      _ = u * (u⁻¹ * x * u * c) * u⁻¹ := by rw [h]
      _ = x * (u * c * u⁻¹) := by group
  · intro h
    calc c * (u⁻¹ * x * u) = u⁻¹ * (u * c * u⁻¹ * x) * u := by group
      _ = u⁻¹ * (x * (u * c * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * x * u * c := by group

theorem twentySeven_dvd_card_centralizer (C A F : Subgroup G) {y : G} (hy3 : y ^ 3 = 1)
    (hyA : y ∈ A) (hFA : F ≤ A) (hCA : C.relIndex A ≤ 3)
    (hF3 : ∀ f ∈ F, f ^ 3 = 1) (hFy : ∀ f ∈ F, f * y = y * f)
    (hF27 : 27 ≤ Nat.card F) (hF81 : y ∈ F → 81 ≤ Nat.card F) :
    27 ∣ Nat.card ↥(Subgroup.centralizer {y} ⊓ C) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R : Subgroup G :=
    { carrier := {r | ∃ f ∈ F, ∃ k : ℕ, r = f * y ^ k}
      one_mem' := ⟨1, one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨f, hf, k, rfl⟩ ⟨f', hf', k', rfl⟩
        refine ⟨f * f', mul_mem hf hf', k + k', ?_⟩
        have hc : ∀ n : ℕ, y ^ n * f' = f' * y ^ n := fun n =>
          (Commute.pow_right (hFy f' hf') n).eq.symm
        calc f * y ^ k * (f' * y ^ k') = f * (y ^ k * f') * y ^ k' := by group
          _ = f * (f' * y ^ k) * y ^ k' := by rw [hc k]
          _ = f * f' * y ^ (k + k') := by rw [pow_add]; group
      inv_mem' := by
        rintro _ ⟨f, hf, k, rfl⟩
        refine ⟨f⁻¹, inv_mem hf, 2 * k, ?_⟩
        have hyk : (y ^ k)⁻¹ = y ^ (2 * k) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show k + 2 * k = 3 * k by ring, pow_mul, hy3,
            one_pow]
        have hc : (y ^ k)⁻¹ * f⁻¹ = f⁻¹ * (y ^ k)⁻¹ :=
          (Commute.pow_right (hFy f⁻¹ (inv_mem hf)) k).inv_right.eq.symm
        calc (f * y ^ k)⁻¹ = (y ^ k)⁻¹ * f⁻¹ := by rw [mul_inv_rev]
          _ = f⁻¹ * (y ^ k)⁻¹ := hc
          _ = f⁻¹ * y ^ (2 * k) := by rw [hyk] }
  have hFR : F ≤ R := fun f hf => ⟨f, hf, 0, by simp⟩
  have hyR : y ∈ R := ⟨1, one_mem _, 1, by simp⟩
  have hRA : R ≤ A := by
    rintro _ ⟨f, hf, k, rfl⟩
    exact mul_mem (hFA hf) (pow_mem hyA k)
  have hR3 : ∀ r ∈ R, r ^ 3 = 1 := by
    rintro _ ⟨f, hf, k, rfl⟩
    have hcomm : Commute f (y ^ k) := Commute.pow_right (hFy f hf) k
    rw [hcomm.mul_pow, hF3 f hf, one_mul, ← pow_mul, mul_comm, pow_mul, hy3, one_pow]
  have hRcent : R ≤ Subgroup.centralizer {y} := by
    rintro _ ⟨f, hf, k, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : y * f = f * y := (hFy f hf).symm
    calc f * y ^ k * y = f * y * y ^ k := by group
      _ = y * f * y ^ k := by rw [h1]
      _ = y * (f * y ^ k) := by group
  have pgrp : ∀ S : Subgroup G, S ≤ R → IsPGroup 3 S := fun S hS g =>
    ⟨1, Subtype.ext (by simpa using hR3 g (hS g.2))⟩
  obtain ⟨n, hn⟩ := (pgrp R le_rfl).exists_card_eq
  obtain ⟨m, hm⟩ := (pgrp F hFR).exists_card_eq
  have hRF : Nat.card F ≤ Nat.card R := Subgroup.card_le_of_le hFR
  have hR81 : 81 ≤ Nat.card R := by
    by_cases hyF : y ∈ F
    · exact (hF81 hyF).trans hRF
    · have hne : F ≠ R := fun h => hyF (h ▸ hyR)
      have hlt : Nat.card F < Nat.card R := by
        refine lt_of_le_of_ne hRF fun h => hne ?_
        exact Subgroup.eq_of_le_of_card_ge hFR h.symm.le
      have hlt' : 3 ^ m < 3 ^ n := by rw [← hm, ← hn]; exact hlt
      have hmn : m + 1 ≤ n := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt'
      have h27m : 27 ≤ 3 ^ m := hm ▸ hF27
      rw [hn]
      calc 81 ≤ 3 * 3 ^ m := by omega
        _ = 3 ^ (m + 1) := by ring
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hmn
  have hrel : C.relIndex R * Nat.card ↥(C ⊓ R) = Nat.card R := Subgroup.relIndex_mul_card C R
  have hrel3 : C.relIndex R ≤ 3 :=
    (Subgroup.relIndex_le_of_le_right hRA Subgroup.index_ne_zero_of_finite).trans hCA
  have hT27 : 27 ≤ Nat.card ↥(C ⊓ R) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card R < 81 := by
      calc Nat.card R = C.relIndex R * Nat.card ↥(C ⊓ R) := hrel.symm
        _ ≤ 3 * 26 := Nat.mul_le_mul hrel3 (by omega)
        _ < 81 := by norm_num
    omega
  have hTle : (C ⊓ R) ≤ R := inf_le_right
  obtain ⟨t, ht⟩ := (pgrp (C ⊓ R) hTle).exists_card_eq
  have h27 : 27 ∣ Nat.card ↥(C ⊓ R) := by
    rw [ht] at hT27 ⊢
    have h3t : 3 ≤ t := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ t ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (pow_dvd_pow 3 h3t)
  have hTZ : (C ⊓ R) ≤ Subgroup.centralizer {y} ⊓ C :=
    le_inf (inf_le_right.trans hRcent) inf_le_left
  exact h27.trans (Subgroup.card_dvd_of_le hTZ)

end CFSG.HardMathSupport.Lang.E6Descent.DiagGroup
