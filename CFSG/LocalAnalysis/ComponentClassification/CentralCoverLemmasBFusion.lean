module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.ComponentClassification.CentralCover

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

private theorem commute_conj_iff {g s x : G} :
    s * (g * x * g⁻¹) = g * x * g⁻¹ * s ↔ g⁻¹ * s * g * x = x * (g⁻¹ * s * g) := by
  constructor <;> intro h
  · calc g⁻¹ * s * g * x = g⁻¹ * (s * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * s) * g := by rw [h]
      _ = x * (g⁻¹ * s * g) := by group
  · calc s * (g * x * g⁻¹) = g * (g⁻¹ * s * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * s := by group

private theorem mem_normalizer_of_characteristic {A C : Subgroup G} (hAC : A ≤ C)
    (hchar : (A.subgroupOf C).Characteristic) {g : G} (hg : g ∈ normalizer (C : Set G)) :
    g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff] at hg ⊢
  have hinv : ∀ x : C, g⁻¹ * x * g ∈ C := fun x =>
    (hg _).mpr (by convert x.2 using 1; group)
  let φ : C ≃* C :=
    { toFun := fun x => ⟨g * x * g⁻¹, (hg x).mp x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hinv x⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun x => Subtype.ext (by simp only; group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcomap := characteristic_iff_comap_eq.mp hchar φ
  intro h
  constructor
  · intro hh
    have hmem : (⟨h, hAC hh⟩ : C) ∈ (A.subgroupOf C).comap φ.toMonoidHom := by
      rw [hcomap]
      exact hh
    exact hmem
  · intro hh
    have hmem : (⟨h, (hg h).mpr (hAC hh)⟩ : C) ∈ (A.subgroupOf C).comap φ.toMonoidHom := hh
    rw [hcomap] at hmem
    exact hmem

private theorem exists_mem_conj_eq_of_mem_normalizer {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) (k : ℕ) :
    ∃ d ∈ A, ∀ z ∈ A, g ^ (Nat.card (OuterAutomorphisms.Outer A) * k) * z *
      (g ^ (Nat.card (OuterAutomorphisms.Outer A) * k))⁻¹ = d * z * d⁻¹ := by
  set M := normalizer (A : Set G)
  set B : Subgroup M := A.subgroupOf M
  let ω : M →* OuterAutomorphisms.Outer B :=
    (QuotientGroup.mk' (OuterAutomorphisms.inner B)).comp MulAut.conjNormal
  have hcard : Nat.card (OuterAutomorphisms.Outer B) = Nat.card (OuterAutomorphisms.Outer A) :=
    Nat.card_congr (OuterAutomorphisms.equivalence (subgroupOfEquivOfLe le_normalizer)).toEquiv
  have hω : ω (⟨g, hg⟩ ^ (Nat.card (OuterAutomorphisms.Outer A) * k)) = 1 := by
    rw [map_pow, ← hcard, pow_mul, pow_card_eq_one', one_pow]
  obtain ⟨d, hd⟩ := (QuotientGroup.eq_one_iff _).mp hω
  refine ⟨((d : M) : G), d.2, fun z hz => ?_⟩
  have hzM : z ∈ M := le_normalizer hz
  have hval := congrArg (fun φ : MulAut B => (((φ ⟨⟨z, hzM⟩, hz⟩ : B) : M) : G)) hd
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    MulAut.conjNormal_apply, SubgroupClass.coe_pow] at hval
  exact hval.symm

private theorem pow_conj_eq_of_mod_three_eq_two {g t p : G} (htt : t * t = 1) (htp : Commute t p)
    (hgt : g⁻¹ * t * g = t * p) (hgp : g⁻¹ * p * g = t) {r : ℕ} (hr : r % 3 = 2) :
    (g ^ r)⁻¹ * t * g ^ r = p := by
  have hgtp : g⁻¹ * (t * p) * g = p := by
    calc g⁻¹ * (t * p) * g = (g⁻¹ * t * g) * (g⁻¹ * p * g) := by group
      _ = p := by rw [hgt, hgp, mul_assoc, ← htp.eq, ← mul_assoc, htt, one_mul]
  have hconj : ∀ u v : G, (u * v)⁻¹ * t * (u * v) = v⁻¹ * (u⁻¹ * t * u) * v := by
    intro u v
    group
  have hg3 : Commute (g ^ 3) t := by
    have h : (g ^ 3)⁻¹ * t * g ^ 3 = t := by
      calc (g ^ 3)⁻¹ * t * g ^ 3 = g⁻¹ * (g⁻¹ * (g⁻¹ * t * g) * g) * g := by
            simp only [pow_three, mul_inv_rev, mul_assoc]
        _ = t := by rw [hgt, hgtp, hgp]
    calc g ^ 3 * t = g ^ 3 * ((g ^ 3)⁻¹ * t * g ^ 3) := by rw [h]
      _ = t * g ^ 3 := by group
  obtain ⟨q, rfl⟩ : ∃ q, r = 3 * q + 2 := ⟨r / 3, by omega⟩
  have hq : ((g ^ 3) ^ q)⁻¹ * t * (g ^ 3) ^ q = t := by
    rw [mul_assoc, ← (hg3.pow_left q).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [pow_add, pow_mul, hconj, hq, pow_two, hconj, hgt, hgtp]

theorem two_inverting_four_roots_characteristic_factor_force_fusion [Finite G] {t p a b : G}
    (ht : orderOf t = 2) (hp : orderOf p = 2) (htp : Commute t p)
    (ha : a ^ 2 = t) (hb : b ^ 2 = p) (hpa : a⁻¹ * p * a = t * p) (htb : b⁻¹ * t * b = t * p)
    {A : Subgroup G} (hAC : A ≤ centralizer (closure ({t, p} : Set G) : Set G))
    (hAchar : (A.subgroupOf (centralizer (closure ({t, p} : Set G) : Set G))).Characteristic)
    (hAeven : Even (Nat.card A)) (hAout : ¬ 3 ∣ Nat.card (OuterAutomorphisms.Outer A))
    (hfus : ∀ z ∈ A, orderOf z = 2 → IsConj (p * z) p) (hpt : IsConj p t) :
    (∃ z ∈ A, orderOf z = 2 ∧ IsConj (t * z) t) ∧
      {x : G | IsConj x t} ∩ t • (A : Set G) ≠ {t} := by
  set C : Subgroup G := centralizer (closure ({t, p} : Set G) : Set G) with hC
  have hmemC : ∀ x, x ∈ C ↔ t * x = x * t ∧ p * x = x * p := by
    intro x
    rw [hC, centralizer_closure, mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hpp : p * p = 1 := by rw [← pow_two, ← hp, pow_orderOf_eq_one]
  have hat : a⁻¹ * t * a = t := by rw [← ha]; group
  have hbp : b⁻¹ * p * b = p := by rw [← hb]; group
  set g := a * b with hg
  have hgt : g⁻¹ * t * g = t * p := by
    calc g⁻¹ * t * g = b⁻¹ * (a⁻¹ * t * a) * b := by rw [hg]; group
      _ = t * p := by rw [hat, htb]
  have hgp : g⁻¹ * p * g = t := by
    calc g⁻¹ * p * g = b⁻¹ * (a⁻¹ * p * a) * b := by rw [hg]; group
      _ = (b⁻¹ * t * b) * (b⁻¹ * p * b) := by rw [hpa]; group
      _ = t := by rw [htb, hbp, mul_assoc, hpp, mul_one]
  have hgtp : g⁻¹ * (t * p) * g = p := by
    calc g⁻¹ * (t * p) * g = (g⁻¹ * t * g) * (g⁻¹ * p * g) := by group
      _ = p := by rw [hgt, hgp, mul_assoc, ← htp.eq, ← mul_assoc, htt, one_mul]
  have hgC : g ∈ normalizer (C : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    rw [hmemC, hmemC, commute_conj_iff, commute_conj_iff, hgt, hgp]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h1⟩
      simp only [mul_assoc]
      rw [h2, ← mul_assoc, h1, mul_assoc]
    · rintro ⟨h1, h2⟩
      simp only [mul_assoc] at h1
      refine ⟨h2, ?_⟩
      calc p * x = t * (t * (p * x)) := by rw [← mul_assoc, htt, one_mul]
        _ = t * (x * (t * p)) := by rw [h1]
        _ = (t * x) * (t * p) := by rw [mul_assoc]
        _ = x * p := by rw [h2, mul_assoc, ← mul_assoc t t p, htt, one_mul]
  have hgA : g ∈ normalizer (A : Set G) := mem_normalizer_of_characteristic hAC hAchar hgC
  set N := Nat.card (OuterAutomorphisms.Outer A) with hN
  obtain ⟨d, hdA, hd⟩ := exists_mem_conj_eq_of_mem_normalizer hgA (2 * N)
  rw [← hN] at hd
  have hr : (N * (2 * N)) % 3 = 2 := by
    have h3 : N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases h3 with h | h <;> simp [Nat.mul_mod, h]
  have hgr := pow_conj_eq_of_mod_three_eq_two htt htp hgt hgp hr
  set e := d⁻¹ * g ^ (N * (2 * N)) with he
  have he1 : ∀ z ∈ A, e⁻¹ * z * e = z := by
    intro z hz
    have hz' := hd z hz
    calc e⁻¹ * z * e = (g ^ (N * (2 * N)))⁻¹ * (d * z * d⁻¹) * g ^ (N * (2 * N)) := by
          rw [he]; group
      _ = z := by rw [← hz']; group
  have hdt : d * t = t * d := ((hmemC d).mp (hAC hdA)).1.symm
  have he2 : e⁻¹ * t * e = p := by
    calc e⁻¹ * t * e = (g ^ (N * (2 * N)))⁻¹ * (d * t * d⁻¹) * g ^ (N * (2 * N)) := by
          rw [he]; group
      _ = p := by rw [hdt, mul_inv_cancel_right, hgr]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (even_iff_two_dvd.mp hAeven)
  have hz2 : orderOf (z : G) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hconj : IsConj (t * z) (p * z) := by
    refine isConj_iff.mpr ⟨e⁻¹, ?_⟩
    calc e⁻¹ * (t * z) * e⁻¹⁻¹ = (e⁻¹ * t * e) * (e⁻¹ * z * e) := by group
      _ = p * z := by rw [he2, he1 z z.2]
  have htz : IsConj (t * z) t := (hconj.trans (hfus z z.2 hz2)).trans hpt
  refine ⟨⟨z, z.2, hz2, htz⟩, fun hset => ?_⟩
  have hmem : t * (z : G) ∈ {x : G | IsConj x t} ∩ t • (A : Set G) :=
    ⟨htz, Set.smul_mem_smul_set z.2⟩
  rw [hset, Set.mem_singleton_iff, mul_eq_left] at hmem
  rw [hmem, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

end CFSG.ComponentClassification.CentralCover
