module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M11Std.Sign

public section

namespace CFSG.EvenSporadicStandard.RuStd

open Subgroup Equiv Equiv.Perm MulAction
open scoped Classical

variable {G : Type} [Group G] [Finite G]

theorem two_dvd_card_support_of_mul_self {α : Type*} [Fintype α] [DecidableEq α] {σ : Perm α}
    (h2 : σ * σ = 1) : 2 ∣ σ.support.card := by
  by_cases h1 : σ = 1
  · simp [h1]
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) h1
    obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two)
    rw [hord] at hn
    rw [← sum_cycleType, hn]
    simp [Multiset.sum_replicate]

noncomputable abbrev cosetPerm (K : Subgroup G) (z : G) : Perm (G ⧸ K) :=
  MulAction.toPermHom G (G ⧸ K) z

omit [Finite G] in
theorem card_support_cosetPerm (K : Subgroup G) [Fintype (G ⧸ K)] (z : G) :
    (cosetPerm K z).support.card = Nat.card {q : G ⧸ K // z • q ≠ q} := by
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun q => by simp [Equiv.Perm.mem_support])

theorem even_card_moved (K : Subgroup G) {z : G} (hz : z * z = 1) :
    2 ∣ Nat.card {q : G ⧸ K // z • q ≠ q} := by
  have := Fintype.ofFinite (G ⧸ K)
  rw [← card_support_cosetPerm K z]
  refine two_dvd_card_support_of_mul_self ?_
  rw [← map_mul, hz, map_one]

theorem four_dvd_card_moved [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (K : Subgroup G) {z : G} (hz : z * z = 1) :
    4 ∣ Nat.card {q : G ⧸ K // z • q ≠ q} := by
  have := Fintype.ofFinite (G ⧸ K)
  set φ : G →* ℤˣ := (sign : Perm (G ⧸ K) →* ℤˣ).comp (MulAction.toPermHom G (G ⧸ K)) with hφ
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
      obtain ⟨a, b, hab⟩ := hnonab
      exact hab (hinj (by rw [map_mul, map_mul, mul_comm]))
    · exact h
  have hsign : sign (cosetPerm K z) = 1 := by
    have : z ∈ φ.ker := by rw [hker]; trivial
    exact this
  have h2 : cosetPerm K z * cosetPerm K z = 1 := by rw [← map_mul, hz, map_one]
  rw [← card_support_cosetPerm K z]
  exact CFSG.EvenSporadicStandard.M11Std.four_dvd_card_support_of_sign_eq_one h2 hsign

omit [Finite G] in
theorem smul_mk_eq_iff (K : Subgroup G) (z t : G) :
    z • (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk t ↔ t⁻¹ * z * t ∈ K := by
  rw [← K.inv_mem_iff, show z • (QuotientGroup.mk t : G ⧸ K) = QuotientGroup.mk (z * t) from rfl,
    QuotientGroup.eq]
  simp [mul_assoc]

omit [Finite G] in
theorem card_conjTo_eq (K : Subgroup G) (z : G) :
    Nat.card {t : G // t⁻¹ * z * t ∈ K} =
      Nat.card K * Nat.card {q : G ⧸ K // z • q = q} := by
  have e1 : {t : G // t⁻¹ * z * t ∈ K} ≃ K × {q : G ⧸ K // z • q = q} :=
    (Equiv.subtypeEquivRight (q := fun t : G => t ∈ QuotientGroup.mk ⁻¹'
      {q : G ⧸ K | z • q = q}) fun t => (smul_mk_eq_iff K z t).symm).trans
      (QuotientGroup.preimageMkEquivSubgroupProdSet K _)
  rw [Nat.card_congr e1, Nat.card_prod]

noncomputable def conjTo (z y : G) : G :=
  if h : IsConj z y then Classical.choose (isConj_iff.1 h) else 1

omit [Finite G] in
theorem conjTo_spec {z y : G} (h : IsConj z y) : conjTo z y * z * (conjTo z y)⁻¹ = y := by
  have := Classical.choose_spec (isConj_iff.1 h)
  simp only [conjTo, h, ↓reduceDIte]
  exact this

omit [Finite G] in
theorem conj_mul_cen {z c w : G} (hc : c ∈ centralizer ({z} : Set G)) :
    (w * c) * z * (w * c)⁻¹ = w * z * w⁻¹ := by
  have h : c * z = z * c := mem_centralizer_singleton_iff.1 hc
  calc (w * c) * z * (w * c)⁻¹ = w * (c * z) * c⁻¹ * w⁻¹ := by group
    _ = w * (z * c) * c⁻¹ * w⁻¹ := by rw [h]
    _ = w * z * w⁻¹ := by group

omit [Finite G] in
theorem mem_cen_of_conj {z t w : G} (h : w * z * w⁻¹ = t⁻¹ * z * t) :
    w⁻¹ * t⁻¹ ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  have : (w⁻¹ * t⁻¹) * z * (w⁻¹ * t⁻¹)⁻¹ = z := by
    calc (w⁻¹ * t⁻¹) * z * (w⁻¹ * t⁻¹)⁻¹ = w⁻¹ * (t⁻¹ * z * t) * w := by group
      _ = w⁻¹ * (w * z * w⁻¹) * w := by rw [h]
      _ = z := by group
  calc (w⁻¹ * t⁻¹) * z = ((w⁻¹ * t⁻¹) * z * (w⁻¹ * t⁻¹)⁻¹) * (w⁻¹ * t⁻¹) := by group
    _ = z * (w⁻¹ * t⁻¹) := by rw [this]

omit [Finite G] in
theorem card_conjTo_eq' (K : Subgroup G) (z : G) :
    Nat.card {t : G // t⁻¹ * z * t ∈ K} =
      Nat.card {y : G // y ∈ K ∧ IsConj z y} * Nat.card (centralizer ({z} : Set G)) := by
  have hconj : ∀ t : G, IsConj z (t⁻¹ * z * t) := fun t => isConj_iff.2 ⟨t⁻¹, by group⟩
  let e2 : {t : G // t⁻¹ * z * t ∈ K} ≃
      {y : G // y ∈ K ∧ IsConj z y} × centralizer ({z} : Set G) :=
    { toFun := fun t =>
        (⟨t.1⁻¹ * z * t.1, t.2, hconj t.1⟩,
          ⟨(conjTo z (t.1⁻¹ * z * t.1))⁻¹ * t.1⁻¹,
            mem_cen_of_conj (conjTo_spec (hconj t.1))⟩)
      invFun := fun p => ⟨((conjTo z p.1.1) * p.2.1)⁻¹, by
        have h1 := conjTo_spec p.1.2.2
        have h2 := conj_mul_cen (w := conjTo z p.1.1) p.2.2
        simp only [inv_inv]
        rw [h2, h1]
        exact p.1.2.1⟩
      left_inv := fun t => by
        apply Subtype.ext
        simp
      right_inv := fun p => by
        have h1 := conjTo_spec p.1.2.2
        have h2 := conj_mul_cen (w := conjTo z p.1.1) p.2.2
        have hy : (((conjTo z p.1.1 * p.2.1)⁻¹)⁻¹ * z * (conjTo z p.1.1 * p.2.1)⁻¹) = p.1.1 := by
          simp only [inv_inv]
          rw [h2, h1]
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · exact hy
        · show (conjTo z (((conjTo z p.1.1 * p.2.1)⁻¹)⁻¹ * z * (conjTo z p.1.1 * p.2.1)⁻¹))⁻¹ *
              ((conjTo z p.1.1 * p.2.1)⁻¹)⁻¹ = p.2.1
          rw [hy]
          group }
  rw [Nat.card_congr e2, Nat.card_prod]

omit [Finite G] in
theorem card_fixed_mul_card (K : Subgroup G) (z : G) :
    Nat.card {q : G ⧸ K // z • q = q} * Nat.card K =
      Nat.card {y : G // y ∈ K ∧ IsConj z y} * Nat.card (centralizer ({z} : Set G)) := by
  rw [← card_conjTo_eq' K z, card_conjTo_eq K z, mul_comm]

end CFSG.EvenSporadicStandard.RuStd
