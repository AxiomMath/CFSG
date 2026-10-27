module

public import CFSG.GH74.Generic.S45.Defs

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section Transport

variable {G H : Type} [Group G] [Group H]

theorem map_centralizer_equiv (e : G ≃* H) (R : Subgroup G) :
    (centralizer (R : Set G)).map e.toMonoidHom =
      centralizer ((R.map e.toMonoidHom : Subgroup H) : Set H) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hy r hr
    show e r * e y = e y * e r
    rw [← map_mul, ← map_mul, h]
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    show e.symm x ∈ centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have h := Subgroup.mem_centralizer_iff.1 hx (e r) ⟨r, hr, rfl⟩
    apply e.injective
    simpa using h

theorem card_centralizer_equiv (e : G ≃* H) (R : Subgroup G) :
    Nat.card ↥(centralizer ((R.map e.toMonoidHom : Subgroup H) : Set H)) =
      Nat.card ↥(centralizer (R : Set G)) := by
  rw [← map_centralizer_equiv e R, Subgroup.card_map_of_injective e.injective]

theorem card_normalizer_equiv (e : G ≃* H) (R : Subgroup G) :
    Nat.card ↥(normalizer ((R.map e.toMonoidHom : Subgroup H) : Set H)) =
      Nat.card ↥(normalizer (R : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq R e, Subgroup.card_map_of_injective e.injective]

end Transport

theorem KBase.of_mulEquiv {G H : Type} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (h : KBase G) : KBase H := by
  obtain ⟨hs, hAut, hSyl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := hs
    exact e.symm.isSimpleGroup
  · intro α hα
    let α' : MulAut G := (MulAut.congr e).symm α
    have hmap : (zpowers α).map ((MulAut.congr e).symm : MulAut H →* MulAut G) = zpowers α' :=
      MonoidHom.map_zpowers _ α
    have hα' : IsPGroup 2 ↥(zpowers α') := by
      rw [← hmap]
      exact hα.map _
    obtain ⟨g, hg⟩ := hAut α' hα'
    refine ⟨e g, ?_⟩
    have hαeq : α = MulAut.congr e α' := ((MulAut.congr e).apply_symm_apply α).symm
    rw [hαeq, ← hg]
    apply MulEquiv.ext
    intro y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  · intro R
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let R' : Sylow 2 G := R.comapOfInjective e.toMonoidHom e.injective
      (fun x _ => ⟨e.symm x, by simp⟩)
    have hR'c : (R' : Subgroup G) = (R : Subgroup H).comap e.toMonoidHom :=
      Sylow.coe_comapOfInjective _ _ _ _
    have hRR' : (R' : Subgroup G).map e.toMonoidHom = (R : Subgroup H) := by
      rw [hR'c]
      exact Subgroup.map_comap_eq_self_of_surjective e.surjective _
    have hmem : ∀ x : H, x ∈ (R : Subgroup H) → e.symm x ∈ (R' : Subgroup G) := by
      intro x hx
      rw [hR'c]
      show e (e.symm x) ∈ (R : Subgroup H)
      simpa using hx
    obtain ⟨hc, hsq, hcard, hNC⟩ := hSyl R'
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b
      have h1 := hc ⟨e.symm a.1, hmem a.1 a.2⟩ ⟨e.symm b.1, hmem b.1 b.2⟩
      apply Subtype.ext
      have h2 := congrArg (fun u : ↥(R' : Subgroup G) => e (u : G)) h1
      simpa using h2
    · intro a
      have h1 := hsq ⟨e.symm a.1, hmem a.1 a.2⟩
      apply Subtype.ext
      have h2 := congrArg (fun u : ↥(R' : Subgroup G) => e (u : G)) h1
      simpa using h2
    · rw [← hRR', Subgroup.card_map_of_injective e.injective]
      exact hcard
    · rw [← hRR', card_normalizer_equiv e (R' : Subgroup G), card_centralizer_equiv e (R' : Subgroup G)]
      exact hNC

theorem comm_of_sq_eq_one {K : Type*} [Group K] {x y : K} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y * (x * y) = 1) : x * y = y * x := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [h1, h2]

theorem kBase_of_data {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K) (hAut : AutTwoInner K)
    (t : K) (ht : orderOf t = 2) (hconj : ∀ x : K, orderOf x = 2 → ∃ g : K, g * x * g⁻¹ = t)
    (hS : ∀ S : Sylow 2 K, t ∈ (S : Subgroup K) →
      Nat.card (S : Subgroup K) = 8 ∧ (∀ x ∈ (S : Subgroup K), x * x = 1) ∧
      centralizer ((S : Subgroup K) : Set K) = (S : Subgroup K) ∧
      Nat.card ↥(normalizer ((S : Subgroup K) : Set K)) = 168) : KBase K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hs, hAut, ?_⟩
  intro R
  have ht2 : IsPGroup 2 ↥(zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S₀, hS₀⟩ := ht2.exists_le_sylow
  have hS₀t : t ∈ (S₀ : Subgroup K) := hS₀ (mem_zpowers t)
  have hS₀8 := (hS S₀ hS₀t).1
  have hR8 : Nat.card (R : Subgroup K) = 8 := by
    rw [R.card_eq_multiplicity, ← S₀.card_eq_multiplicity]
    exact hS₀8
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(R : Subgroup K)) 2
    (by rw [hR8]; norm_num)
  have hu' : orderOf (u : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  obtain ⟨g, hg⟩ := hconj (u : K) hu'
  let S : Sylow 2 K := g • R
  have hSmem : ∀ x : K, x ∈ (S : Subgroup K) ↔ g⁻¹ * x * g ∈ (R : Subgroup K) := by
    intro x
    have h1 : ((g • R : Sylow 2 K) : Subgroup K) = MulAut.conj g • (R : Subgroup K) :=
      Sylow.coe_subgroup_smul
    show x ∈ ((g • R : Sylow 2 K) : Subgroup K) ↔ _
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hStmem : t ∈ (S : Subgroup K) := by
    rw [hSmem, ← hg]
    have : g⁻¹ * (g * (u : K) * g⁻¹) * g = u := by group
    rw [this]
    exact u.2
  obtain ⟨hS8, hSsq, hSC, hSN⟩ := hS S hStmem
  have hSRmem : ∀ x : K, x ∈ (R : Subgroup K) ↔ g * x * g⁻¹ ∈ (S : Subgroup K) := by
    intro x
    rw [hSmem]
    have : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [this]
  have hRS : (R : Subgroup K).map (MulAut.conj g).toMonoidHom = (S : Subgroup K) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hSRmem y).1 hy
    · intro hx
      refine ⟨g⁻¹ * x * g, (hSmem x).1 hx, ?_⟩
      show g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  have hcomm : ∀ a b : K, a ∈ (R : Subgroup K) → b ∈ (R : Subgroup K) → a * b = b * a := by
    intro a b ha hb
    have hsa := hSsq _ ((hSRmem a).1 ha)
    have hsb := hSsq _ ((hSRmem b).1 hb)
    have hsab := hSsq _ (mul_mem ((hSRmem a).1 ha) ((hSRmem b).1 hb))
    have hxy := comm_of_sq_eq_one hsa hsb hsab
    have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := hxy
        _ = g * (b * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (hcomm a b ha hb)
  · rintro ⟨a, ha⟩
    apply Subtype.ext
    have h1 := hSsq (g * a * g⁻¹) ((hSRmem a).1 ha)
    have e : g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
    rw [e] at h1
    have h3 : a * a = g⁻¹ * (g * (a * a) * g⁻¹) * g := by group
    show a * a = 1
    rw [h3, h1]
    group
  · exact hR8
  · have h1 := card_normalizer_equiv (MulAut.conj g) (R : Subgroup K)
    rw [hRS] at h1
    have h2 := card_centralizer_equiv (MulAut.conj g) (R : Subgroup K)
    rw [hRS, hSC] at h2
    rw [← h1, ← h2, hSN, hS8]

end CFSG.GH74.Generic.S45
