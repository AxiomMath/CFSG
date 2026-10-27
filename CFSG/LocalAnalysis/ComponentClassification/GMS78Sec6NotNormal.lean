module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Main
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Model
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6Quot

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_rightConjugate_iff (H : Subgroup G) (n g : G) :
    g ∈ normalizer (rightConjugate H n : Set G) ↔ n * g * n⁻¹ ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff, mem_normalizer_iff]
  constructor
  · intro h x
    have h1 := h (n⁻¹ * x * n)
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff] at h1
    have e1 : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    have e2 : n * (g * (n⁻¹ * x * n) * g⁻¹) * n⁻¹ = n * g * n⁻¹ * x * (n * g * n⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro h x
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
    have e2 : n * (g * x * g⁻¹) * n⁻¹ = n * g * n⁻¹ * (n * x * n⁻¹) * (n * g * n⁻¹)⁻¹ := by
      group
    rw [e2]
    exact h _

omit [Finite G] in
theorem mem_centralizer_rightConjugate_iff (H : Subgroup G) (n g : G) :
    g ∈ centralizer (rightConjugate H n : Set G) ↔ n * g * n⁻¹ ∈ centralizer (H : Set G) := by
  rw [mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h x hx
    have hx' : n⁻¹ * x * n ∈ rightConjugate H n := by
      rw [mem_rightConjugate_iff]
      simpa [mul_assoc] using hx
    have h1 := h _ hx'
    calc x * (n * g * n⁻¹) = n * ((n⁻¹ * x * n) * g) * n⁻¹ := by group
      _ = n * (g * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
      _ = n * g * n⁻¹ * x := by group
  · intro h x hx
    have h1 := h _ ((mem_rightConjugate_iff H n x).mp hx)
    calc x * g = n⁻¹ * ((n * x * n⁻¹) * (n * g * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * g * n⁻¹) * (n * x * n⁻¹)) * n := by rw [h1]
      _ = g * x := by group

omit [Finite G] in
theorem u3X₀_map_conj (L K : Subgroup G) (c : G) :
    (u3X₀ L K).map (MulAut.conj c).toMonoidHom =
      u3X₀ (L.map (MulAut.conj c).toMonoidHom) (K.map (MulAut.conj c).toMonoidHom) := by
  show (⁅L ⊓ centralizer (K : Set G), L ⊓ centralizer (K : Set G)⁆).map _ =
    ⁅L.map (MulAut.conj c).toMonoidHom ⊓ centralizer ((K.map (MulAut.conj c).toMonoidHom :
      Subgroup G) : Set G), L.map (MulAut.conj c).toMonoidHom ⊓
      centralizer ((K.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G)⁆
  rw [map_commutator, Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective,
    centralizer_map_mulEquiv]

omit [Finite G] in
theorem nonempty_rankTwoQuot_map_conj (X : Subgroup G) (c : G) :
    Nonempty (rankTwoQuot (X.map (MulAut.conj c).toMonoidHom) ≃* rankTwoQuot X) :=
  ⟨quotCenterCongr (X.equivMapOfInjective _ (MulAut.conj c).injective).symm⟩

omit [Finite G] in
theorem card_center_map_conj (X : Subgroup G) (c : G) :
    Nat.card (center (X.map (MulAut.conj c).toMonoidHom)) = Nat.card (center X) :=
  Nat.card_congr
    (Subgroup.centerCongr (X.equivMapOfInjective _ (MulAut.conj c).injective).symm).toEquiv

omit [Finite G] in
theorem mem_map_conj_iff (H : Subgroup G) (g x : G) :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem exists_odd_sup_eq {P D : Subgroup G} (hP : IsSylowOf 2 P D)
    (hDN : D ≤ normalizer (P : Set G)) : ∃ M ≤ D, Odd (Nat.card M) ∧ P ⊔ M = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPD : P ≤ D := hP.le
  set N : Subgroup D := P.subgroupOf D with hNdef
  have hNn : N.Normal := (normal_subgroupOf_iff_le_normalizer hPD).mpr hDN
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNdef, ← hQ]
    exact Q.card_coprime_index
  obtain ⟨H', hH'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨H'.map D.subtype, map_subtype_le _, ?_, ?_⟩
  · have h1 := hH'.card_mul_card
    have h2 := N.card_mul_index
    have h3 : Nat.card H' = N.index :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
    rw [Subgroup.card_map_of_injective D.subtype_injective, h3]
    have hnd : ¬ 2 ∣ N.index := by
      rw [hNdef, ← hQ]
      exact Q.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  · have h4 := congrArg (Subgroup.map D.subtype) hH'.sup_eq_top
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      subgroupOf_map_subtype, inf_eq_left.mpr hPD] at h4
    exact h4

theorem isSylowOf_inf_of_sup_eq {P H D : Subgroup G} (hP : IsSylowOf 2 P H)
    (hDN : D ≤ normalizer (P : Set G)) (hsup : D ⊔ P = H) : IsSylowOf 2 (P ⊓ D) D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨-, hP2, hndvd⟩ := hP
  refine ⟨inf_le_right, hP2.to_inf_left, ?_⟩
  rw [Subgroup.inf_relIndex_right]
  have := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hDN
  have e : P.relIndex D = P.relIndex (D ⊔ P) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient D P hDN).toEquiv
  rw [e, hsup]
  exact hndvd

omit [Finite G] in
theorem eq_one_of_pow_two_pow_of_mem_odd {H : Type*} [Group H] {S : Subgroup H}
    (hS : Odd (Nat.card S)) {g : H} (hg : g ∈ S) {k : ℕ} (hk : g ^ 2 ^ k = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hg
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases i with _ | i
  · rwa [pow_zero, orderOf_eq_one_iff] at hi
  · rw [hi, pow_succ] at h2
    exact absurd (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans h2))
      (Nat.not_even_iff_odd.mpr hS)

end CFSG.ComponentClassification.GMS78
