module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegree64CentralLift

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

open Subgroup Module Matrix SymplecticFlag CFSG.Assembly.LowTwoRank RadicalLabels FusionOrbits
open LinearMap (BilinForm)
open scoped Pointwise

local notation "M₃" => Matrix (Fin 3) (Fin 3) (ZMod 2)

theorem zmod_two_jMat_add : ∀ c y y' c' x x' : ZMod 2,
    jMat c y y' + jMat c' x x' = jMat (c + c') (y + x) (y' + x') := by
  decide

@[expose] def swapMat : M₃ := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem swapMat_mul_self : swapMat * swapMat = 1 := by
  decide

@[expose] def swapGL : GL (Fin 3) (ZMod 2) :=
  ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

theorem swapMat_alt3Mat : swapMat * alt3Mat 1 0 0 * swapMatᵀ = alt3Mat 0 0 1 := by
  decide

theorem zmod_two_jMat_ne_alt3Mat : ∀ c y y' : ZMod 2, jMat c y y' ≠ alt3Mat 0 0 1 := by
  decide

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e) (hb : b.IsAlt)
  (hnd : b.Nondegenerate)

local notation "𝔼" => pairOrth b (e (Sum.inl 0)) (e (Sum.inr 0))

variable {G : Type} [Group G] {L : Subgroup G} (φ : L ≃* bilinIsometryGroup b) {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)

local notation "𝒜₁" => pullSub φ (pointRadical b hb (e (Sum.inl 0)) (e (Sum.inr 0)))
local notation "𝒜₂" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℬ₁" => ptSub φ z hb e
local notation "ℛ" => radSub φ z e
local notation "𝒩₁" => normalizer ((ptSub φ z hb e : Subgroup G) : Set G)
local notation "𝒩₂" => normalizer ((radSub φ z e : Subgroup G) : Set G)

include he in
theorem card_pullSub_radA : Nat.card 𝒜₂ = 64 := by
  rw [card_pullSub, card_pointwiseStabilizer_lagrangianOf he]
  norm_num

theorem tauHom_nu {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    {d : G} (hd : d ∈ D₂) : tauHom φ he (Multiplicative.ofAdd (ν₂ d)) = z⁻¹ * (d⁻¹ * z * d) := by
  rw [hν₂z d hd, radHom_one_eq φ he hzC hz, inv_mul_cancel_left]

include hinf in
theorem nu_mul {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    {d d' : G} (hd : d ∈ D₂) (hd' : d' ∈ D₂) : ν₂ (d * d') = ν₂ d + ν₂ d' := by
  have h1 := hν₂z _ (mul_mem hd hd')
  have h2 : (d * d')⁻¹ * z * (d * d') = d'⁻¹ * (d⁻¹ * z * d) * d' := by group
  rw [h2, hν₂z d hd, hpure d' hd' (ν₂ d) 1, one_smul] at h1
  exact (congrArg Prod.fst (Multiplicative.ofAdd.injective
    (radHom_injective φ he hzC hz hinf h1))).symm

theorem nu_eq_zero_iff {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) {d : G} (hd : d ∈ D₂) : ν₂ d = 0 ↔ d ∈ ℛ := by
  rw [← hD₂H, mem_inf, mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨hd, ?_⟩
    have h1 := tauHom_nu he φ hzC hz hν₂z hd
    rw [h, ofAdd_zero, map_one] at h1
    have h2 : d⁻¹ * z * d = z := by
      calc d⁻¹ * z * d = z * (z⁻¹ * (d⁻¹ * z * d)) := by group
        _ = z := by rw [← h1, mul_one]
    calc d * z = d * (d⁻¹ * z * d) := by rw [h2]
      _ = z * d := by group
  · rintro ⟨-, h⟩
    have h1 := tauHom_nu he φ hzC hz hν₂z hd
    have h2 : z⁻¹ * (d⁻¹ * z * d) = 1 := by
      rw [mul_assoc, ← h]
      group
    rw [h2, ← map_one (tauHom φ he), ← ofAdd_zero] at h1
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)

theorem nu_conj_levi {D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂) (g : GL (Fin 3) (ZMod 2)) {d : G}
    (hd : d ∈ D₂) :
    ν₂ (leviHom φ he g * d * (leviHom φ he g)⁻¹) = symThreeCongr g (ν₂ d) := by
  have hD := hD₂n _ (leviHom_mem_normalizer_radSub φ he hzC hz g) d hd
  have h1 := tauHom_nu he φ hzC hz hν₂z hD
  have h2 := gamma_conj (z := z) (x := d) (leviHom_mul_z φ he hzC g)
  have h3 : z⁻¹ * ((leviHom φ he g * d * (leviHom φ he g)⁻¹)⁻¹ * z *
      (leviHom φ he g * d * (leviHom φ he g)⁻¹)) =
      leviHom φ he g * tauHom φ he (Multiplicative.ofAdd (ν₂ d)) * (leviHom φ he g)⁻¹ := by
    calc z⁻¹ * ((leviHom φ he g * d * (leviHom φ he g)⁻¹)⁻¹ * z *
        (leviHom φ he g * d * (leviHom φ he g)⁻¹)) =
        z⁻¹ * (leviHom φ he g * d * (leviHom φ he g)⁻¹)⁻¹ * z *
          (leviHom φ he g * d * (leviHom φ he g)⁻¹) := by group
      _ = leviHom φ he g * (z⁻¹ * d⁻¹ * z * d) * (leviHom φ he g)⁻¹ := h2
      _ = leviHom φ he g * (z⁻¹ * (d⁻¹ * z * d)) * (leviHom φ he g)⁻¹ := by group
      _ = _ := by rw [tauHom_nu he φ hzC hz hν₂z hd]
  rw [h3, leviHom_conj_tauHom'] at h1
  exact Multiplicative.ofAdd.injective (tauHom_injective φ he h1)

include he in
theorem altSub_le_radA : altSub φ he ≤ 𝒜₂ := by
  rintro _ ⟨B, -, rfl⟩
  exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩

omit hnd in
include he in
theorem mem_ptA_inf_altSub_iff {x : G} :
    x ∈ 𝒜₁ ⊓ altSub φ he ↔
      ∃ y y' : ZMod 2, tauHom φ he (Multiplicative.ofAdd (jSym 0 y y')) = x := by
  constructor
  · intro hx
    obtain ⟨hxA, B, hB, rfl⟩ := mem_inf.1 hx
    obtain ⟨c, y, y', hc⟩ := (mem_ptA_inf_radA_iff he hb φ).1
      (mem_inf.2 ⟨hxA, altSub_le_radA he φ ⟨B, hB, rfl⟩⟩)
    have h1 := Multiplicative.ofAdd.injective (tauHom_injective φ he hc)
    rw [← h1] at hB
    have h2 := congrFun hB 0
    change c = 0 at h2
    subst h2
    exact ⟨y, y', hc⟩
  · rintro ⟨y, y', rfl⟩
    refine mem_inf.2 ⟨(mem_inf.1 ((mem_ptA_inf_radA_iff he hb φ).2 ⟨0, y, y', rfl⟩)).1,
      ⟨_, ?_, rfl⟩⟩
    funext k
    fin_cases k <;> rfl

omit hnd in
include he in
theorem card_ptA_inf_altSub : Nat.card (𝒜₁ ⊓ altSub φ he : Subgroup G) = 4 := by
  have hinj : Function.Injective fun p : ZMod 2 × ZMod 2 =>
      tauHom φ he (Multiplicative.ofAdd (jSym 0 p.1 p.2)) := by
    rintro ⟨y, y'⟩ ⟨x, x'⟩ h
    have h1 := congrArg Subtype.val (Multiplicative.ofAdd.injective (tauHom_injective φ he h))
    have h2 := congrFun (congrFun h1 0) 1
    have h3 := congrFun (congrFun h1 0) 2
    change y = x at h2
    change y' = x' at h3
    rw [h2, h3]
  have hrange : Set.range (fun p : ZMod 2 × ZMod 2 =>
      tauHom φ he (Multiplicative.ofAdd (jSym 0 p.1 p.2))) =
        ((𝒜₁ ⊓ altSub φ he : Subgroup G) : Set G) := by
    ext x
    rw [SetLike.mem_coe, mem_ptA_inf_altSub_iff he hb φ]
    constructor
    · rintro ⟨⟨y, y'⟩, rfl⟩
      exact ⟨y, y', rfl⟩
    · rintro ⟨y, y', rfl⟩
      exact ⟨(y, y'), rfl⟩
  have h := Nat.card_range_of_injective hinj
  rw [hrange, Nat.card_prod, Nat.card_zmod] at h
  exact h

omit hnd in
include he hzC hz in
theorem zpowers_ptB₁_le : zpowers (ptB₁ he hb φ hzC hz) ≤ 𝒜₁ ⊓ 𝒜₂ := by
  rw [zpowers_le, ptB₁_eq_tauHom]
  exact (mem_ptA_inf_radA_iff he hb φ).2 ⟨1, 0, 0, rfl⟩

omit hnd in
include he hzC hz in
theorem zpowers_ptB₁_inf_altSub : zpowers (ptB₁ he hb φ hzC hz) ⊓ altSub φ he = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h1, h2⟩ := mem_inf.1 hx
  rcases FusionOrbits.eq_one_or_eq_of_mem_zpowers (orderOf_ptB₁ he hb φ hzC hz) h1 with h | h
  · rw [h]
    exact one_mem _
  · rw [h] at h2
    exact absurd h2 (ptB₁_not_mem_altSub he hb φ hzC hz)

omit hnd in
include he hzC hz in
theorem zpowers_sup_ptA_inf_altSub :
    zpowers (ptB₁ he hb φ hzC hz) ⊔ (𝒜₁ ⊓ altSub φ he) = 𝒜₁ ⊓ 𝒜₂ := by
  refine le_antisymm (sup_le (zpowers_ptB₁_le he hb φ hzC hz)
    (inf_le_inf_left _ (altSub_le_radA he φ))) fun x hx => ?_
  obtain ⟨c, y, y', rfl⟩ := (mem_ptA_inf_radA_iff he hb φ).1 hx
  have h : tauHom φ he (Multiplicative.ofAdd (jSym c y y')) =
      tauHom φ he (Multiplicative.ofAdd (jSym c 0 0)) *
        tauHom φ he (Multiplicative.ofAdd (jSym 0 y y')) := by
    rw [← map_mul, ← ofAdd_add]
    congr 2
    apply Subtype.ext
    change jMat c y y' = jMat c 0 0 + jMat 0 y y'
    rw [zmod_two_jMat_add, add_zero, zero_add, zero_add]
  rw [h]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right ((mem_ptA_inf_altSub_iff he hb φ).2
    ⟨y, y', rfl⟩))
  rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
  · have h0 : jSym 0 0 0 = 0 := Subtype.ext (by decide)
    rw [h0, ofAdd_zero, map_one]
    exact one_mem _
  · rw [← ptB₁_eq_tauHom he hb φ hzC hz]
    exact mem_zpowers _

section Intersections

theorem conj_mem_ptA_inf_radA {C₁ D₁ D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁) (hC₁D : C₁ ≤ D₁)
    {k : G} (hk : k ∈ C₁ ⊓ D₂) : z⁻¹ * (k⁻¹ * z * k) ∈ 𝒜₁ ⊓ 𝒜₂ := by
  refine mem_inf.2 ⟨hγD₁ k (hC₁D (mem_inf.1 hk).1), ?_⟩
  rw [← tauHom_nu he φ hzC hz hν₂z (mem_inf.1 hk).2]
  exact (mem_pullSub_iff φ he).2 ⟨_, rfl⟩

theorem nu_eq_jSym {C₁ D₁ D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁) (hC₁D : C₁ ≤ D₁)
    {k : G} (hk : k ∈ C₁ ⊓ D₂) : ∃ c y y' : ZMod 2, ν₂ k = jSym c y y' := by
  obtain ⟨c, y, y', h⟩ := (mem_ptA_inf_radA_iff he hb φ).1
    (conj_mem_ptA_inf_radA he hb φ hzC hz hν₂z hγD₁ hC₁D hk)
  rw [← tauHom_nu he φ hzC hz hν₂z (mem_inf.1 hk).2] at h
  exact ⟨c, y, y', (Multiplicative.ofAdd.injective (tauHom_injective φ he h)).symm⟩

include he hnd hzC hinf in
theorem C₁_inf_D₂_inf_centralizer {C₁ D₁ D₂ : Subgroup G}
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) :
    (C₁ ⊓ D₂) ⊓ centralizer ({z} : Set G) = 𝒜₁ ⊓ 𝒜₂ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxCD, hxz⟩ := mem_inf.1 hx
    obtain ⟨hxC, hxD⟩ := mem_inf.1 hxCD
    have hxB : x ∈ ℬ₁ := by
      rw [← hD₁H]
      exact mem_inf.2 ⟨hC₁D hxC, hxz⟩
    have hxA : x ∈ 𝒜₁ := by
      rw [← hC₁B]
      exact mem_inf.2 ⟨hxC, hxB⟩
    have hxR : x ∈ ℛ := by
      rw [← hD₂H]
      exact mem_inf.2 ⟨hxD, hxz⟩
    exact mem_inf.2 ⟨hxA, mem_radA_of_mem_radSub φ hzC hinf hxR ((ptA_facts he hb hnd φ).1 hxA)⟩
  · intro x hx
    obtain ⟨hxA, hxR⟩ := mem_inf.1 hx
    have hxC : x ∈ C₁ := by
      have h : x ∈ C₁ ⊓ ℬ₁ := by
        rw [hC₁B]
        exact hxA
      exact (mem_inf.1 h).1
    have hxD : x ∈ D₂ ⊓ centralizer ({z} : Set G) := by
      rw [hD₂H]
      exact mem_sup_left hxR
    exact mem_inf.2 ⟨mem_inf.2 ⟨hxC, (mem_inf.1 hxD).1⟩, (mem_inf.1 hxD).2⟩

theorem conjClass_C₁_inf_D₂ [Finite G] {C₁ D₁ D₂ : Subgroup G} (hRD₂ : ℛ ≤ D₂)
    (hC₁z : zpowers z ⊔ C₁ = D₁) (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hJ : ∀ k ∈ C₁ ⊓ D₂, z⁻¹ * (k⁻¹ * z * k) ∈ 𝒜₁ ⊓ 𝒜₂) :
    conjClass (C₁ ⊓ D₂) z = z • ((𝒜₁ ⊓ 𝒜₂ : Subgroup G) : Set G) := by
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass_iff_right.1 hx
    refine ⟨z⁻¹ * (k⁻¹ * z * k), hJ k hk, ?_⟩
    change z * (z⁻¹ * (k⁻¹ * z * k)) = k⁻¹ * z * k
    group
  · rintro _ ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq_of_sup hb φ hKz hC₁z hzC₁ hzD₂ hj
    change z * j ∈ conjClass (C₁ ⊓ D₂) z
    exact mem_conjClass_iff_right.2 ⟨k, hk, hkz⟩

include hnd hzC hinf hz in
theorem card_C₁_inf_D₂ [Finite G] {C₁ D₁ D₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j) :
    Nat.card (C₁ ⊓ D₂ : Subgroup G) = 64 := by
  rw [card_eq_card_conjClass_mul _ z, conjClass_C₁_inf_D₂ hb φ hRD₂ hC₁z hzC₁ hKz
      (fun k hk => conj_mem_ptA_inf_radA he hb φ hzC hz hν₂z hγD₁ hC₁D hk),
    card_smul_set, SetLike.coe_sort_coe, card_ptA_inf_radA he hb φ,
    C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B,
    card_ptA_inf_radA he hb φ]

theorem conjClass_C₁_inf_F₂ [Finite G] {C₁ D₁ D₂ F₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hRD₂ : ℛ ≤ D₂) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁z : zpowers z ⊔ C₁ = D₁) (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he) :
    conjClass (C₁ ⊓ F₂) z = z • ((𝒜₁ ⊓ altSub φ he : Subgroup G) : Set G) := by
  have hzD₂ : z ∈ D₂ := hRD₂ (mem_sup_right (mem_zpowers z))
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass_iff_right.1 hx
    obtain ⟨hkC, hkF⟩ := mem_inf.1 hk
    obtain ⟨hkD, hkI⟩ := (hF₂ k).1 hkF
    refine ⟨z⁻¹ * (k⁻¹ * z * k), mem_inf.2 ⟨(mem_inf.1 (conj_mem_ptA_inf_radA he hb φ hzC hz
      hν₂z hγD₁ hC₁D (mem_inf.2 ⟨hkC, hkD⟩))).1, hkI⟩, ?_⟩
    change z * (z⁻¹ * (k⁻¹ * z * k)) = k⁻¹ * z * k
    group
  · rintro _ ⟨j, hj, rfl⟩
    have hjJ : j ∈ 𝒜₁ ⊓ 𝒜₂ := inf_le_inf_left _ (altSub_le_radA he φ) hj
    obtain ⟨k, hk, hkz⟩ := exists_mem_inf_conj_eq_of_sup hb φ hKz hC₁z hzC₁ hzD₂ hjJ
    have hkF : k ∈ F₂ := by
      refine (hF₂ k).2 ⟨(mem_inf.1 hk).2, ?_⟩
      rw [hkz, inv_mul_cancel_left]
      exact (mem_inf.1 hj).2
    change z * j ∈ conjClass (C₁ ⊓ F₂) z
    exact mem_conjClass_iff_right.2 ⟨k, mem_inf.2 ⟨(mem_inf.1 hk).1, hkF⟩, hkz⟩

include hnd hzC hinf in
theorem C₁_inf_F₂_inf_centralizer {C₁ D₁ D₂ F₂ : Subgroup G}
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he) :
    (C₁ ⊓ F₂) ⊓ centralizer ({z} : Set G) = 𝒜₁ ⊓ 𝒜₂ := by
  have hFD : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hK := C₁_inf_D₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B
  apply le_antisymm
  · rw [← hK]
    exact inf_le_inf_right _ (inf_le_inf_left _ hFD)
  · intro x hx
    rw [← hK] at hx
    obtain ⟨hxCD, hxz⟩ := mem_inf.1 hx
    obtain ⟨hxC, hxD⟩ := mem_inf.1 hxCD
    have hxF : x ∈ F₂ := by
      refine (hF₂ x).2 ⟨hxD, ?_⟩
      have h : x⁻¹ * z * x = z := by
        rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hxz, inv_mul_cancel_left]
      rw [h, inv_mul_cancel]
      exact one_mem _
    exact mem_inf.2 ⟨mem_inf.2 ⟨hxC, hxF⟩, hxz⟩

include hnd hzC hinf hz in
theorem card_C₁_inf_F₂ [Finite G] {C₁ D₁ D₂ F₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he) :
    Nat.card (C₁ ⊓ F₂ : Subgroup G) = 32 := by
  rw [card_eq_card_conjClass_mul _ z, conjClass_C₁_inf_F₂ he hb φ hzC hz hν₂z hRD₂ hγD₁ hC₁D
      hC₁z hzC₁ hKz hF₂, card_smul_set, SetLike.coe_sort_coe, card_ptA_inf_altSub he hb φ,
    C₁_inf_F₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B hF₂,
    card_ptA_inf_radA he hb φ]

theorem sq_eq_one_of_mem_C₁_inf_F₂ {C₁ F₂ : Subgroup G}
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hF₂sq : ∀ f ∈ F₂, f ^ 2 ∈ altSub φ he) {m : G} (hm : m ∈ C₁ ⊓ F₂) : m ^ 2 = 1 := by
  have h : m ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz) ⊓ altSub φ he :=
    mem_inf.2 ⟨hC₁sq m (mem_inf.1 hm).1, hF₂sq m (mem_inf.1 hm).2⟩
  rw [zpowers_ptB₁_inf_altSub he hb φ hzC hz, mem_bot] at h
  exact h

theorem comm_of_sq_eq_one {X : Subgroup G} (hX : ∀ x ∈ X, x ^ 2 = 1) {x y : G} (hx : x ∈ X)
    (hy : y ∈ X) : x * y = y * x := by
  have hinv : ∀ w ∈ X, w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hX w hw)
  calc x * y = (x * y)⁻¹ := (hinv _ (mul_mem hx hy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv x hx, hinv y hy]

omit hb in
include he in
theorem sq_eq_one_of_mem_radA {a : G} (ha : a ∈ 𝒜₂) : a ^ 2 = 1 := by
  obtain ⟨B, rfl⟩ := (mem_pullSub_iff φ he).1 ha
  rw [sq, ← map_mul, ← ofAdd_toAdd B, ← ofAdd_add, symThree_add_self, ofAdd_zero, map_one]

include hnd hzC hinf hz in
theorem card_C₁_inf_F₂_sup_radA [Finite G] {C₁ D₁ D₂ F₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he)
    (hcomm₂ : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d) :
    Nat.card (C₁ ⊓ F₂ ⊔ 𝒜₂ : Subgroup G) = 256 := by
  have hFD : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hMN : C₁ ⊓ F₂ ≤ normalizer (𝒜₂ : Set G) := fun m hm =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (hcomm₂ m (hFD (mem_inf.1 hm).2) a ha).symm)
  have hset := coe_mul_of_left_le_normalizer_right (C₁ ⊓ F₂) 𝒜₂ hMN
  have hMconj := conjClass_C₁_inf_F₂ he hb φ hzC hz hν₂z hRD₂ hγD₁ hC₁D hC₁z hzC₁ hKz hF₂
  have hconj : conjClass (C₁ ⊓ F₂ ⊔ 𝒜₂) z = z • ((𝒜₁ ⊓ altSub φ he : Subgroup G) : Set G) := by
    refine Set.Subset.antisymm ?_ (hMconj ▸ conjClass_mono le_sup_left z)
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass_iff_right.1 hx
    have hk' : k ∈ ((C₁ ⊓ F₂ ⊔ 𝒜₂ : Subgroup G) : Set G) := hk
    rw [hset] at hk'
    obtain ⟨m, hm, a, ha, rfl⟩ := hk'
    have hm' : m⁻¹ * z * m ∈ conjClass (C₁ ⊓ F₂) z := mem_conjClass_iff_right.2 ⟨m, hm, rfl⟩
    rw [hMconj] at hm'
    obtain ⟨j, hj, hjm⟩ := hm'
    have hjA : j ∈ 𝒜₂ := altSub_le_radA he φ (mem_inf.1 hj).2
    have haz : a * z = z * a := mul_comm_z hzC (pullSub_le φ _ ha)
    have haj : a * j = j * a := radA_comm he φ ha hjA
    refine ⟨j, hj, ?_⟩
    change z * j = (m * a)⁻¹ * z * (m * a)
    have hjm' : m⁻¹ * z * m = z * j := hjm.symm
    calc z * j = a⁻¹ * (a * z) * j := by group
      _ = a⁻¹ * (z * a) * j := by rw [haz]
      _ = a⁻¹ * z * (a * j) := by group
      _ = a⁻¹ * z * (j * a) := by rw [haj]
      _ = a⁻¹ * (z * j) * a := by group
      _ = a⁻¹ * (m⁻¹ * z * m) * a := by rw [hjm']
      _ = (m * a)⁻¹ * z * (m * a) := by group
  have hcent : (C₁ ⊓ F₂ ⊔ 𝒜₂) ⊓ centralizer ({z} : Set G) = 𝒜₂ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxX, hxz⟩ := mem_inf.1 hx
      have hx' : x ∈ ((C₁ ⊓ F₂ ⊔ 𝒜₂ : Subgroup G) : Set G) := hxX
      rw [hset] at hx'
      obtain ⟨m, hm, a, ha, rfl⟩ := hx'
      have haz : a ∈ centralizer ({z} : Set G) :=
        mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ ha))
      have hmz : m ∈ centralizer ({z} : Set G) := by
        have h := mul_mem hxz (inv_mem haz)
        rwa [mul_inv_cancel_right] at h
      have hmJ : m ∈ 𝒜₁ ⊓ 𝒜₂ := by
        rw [← C₁_inf_F₂_inf_centralizer he hb hnd φ hzC hinf hD₂H hD₁H hC₁D hC₁B hF₂]
        exact mem_inf.2 ⟨hm, hmz⟩
      exact mul_mem (mem_inf.1 hmJ).2 ha
    · intro a ha
      exact mem_inf.2 ⟨mem_sup_right ha,
        mem_centralizer_singleton_iff.2 (mul_comm_z hzC (pullSub_le φ _ ha))⟩
  rw [card_eq_card_conjClass_mul _ z, hconj, card_smul_set, SetLike.coe_sort_coe,
    card_ptA_inf_altSub he hb φ, hcent, card_pullSub_radA he φ]

include hnd hzC hinf hz in
theorem C₁_inf_F₂_le [Finite G] {C₁ D₁ D₂ F₂ E₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he)
    (hcomm₂ : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hF₂sq : ∀ f ∈ F₂, f ^ 2 ∈ altSub φ he)
    (hY : ∀ Y : Subgroup G, Y ≤ F₂ → IsMulCommutative Y →
      4 ≤ Subgroup.relIndex 𝒜₂ (Y ⊔ 𝒜₂) → Y ≤ E₂) : C₁ ⊓ F₂ ≤ E₂ := by
  have hsq := fun m (hm : m ∈ C₁ ⊓ F₂) =>
    sq_eq_one_of_mem_C₁_inf_F₂ he hb φ hzC hz hC₁sq hF₂sq hm
  have hc : IsMulCommutative (C₁ ⊓ F₂ : Subgroup G) :=
    ⟨⟨fun x y => Subtype.ext (comm_of_sq_eq_one hsq x.2 y.2)⟩⟩
  refine hY _ inf_le_right hc ?_
  have h := Subgroup.relIndex_mul_card (H := 𝒜₂) (K := C₁ ⊓ F₂ ⊔ 𝒜₂)
  rw [inf_of_le_left (le_sup_right : 𝒜₂ ≤ C₁ ⊓ F₂ ⊔ 𝒜₂), card_pullSub_radA he φ,
    card_C₁_inf_F₂_sup_radA he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z
      hzC₁ hKz hF₂ hcomm₂] at h
  omega

end Intersections

include hnd hzC hinf hz in
theorem sq_eq_one_of_mem_E₂ [Finite G] {C₁ D₁ D₂ F₂ E₂ : Subgroup G}
    {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    (hD₂n : ∀ n ∈ 𝒩₂, ∀ d ∈ D₂, n * d * n⁻¹ ∈ D₂)
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ) (hRD₂ : ℛ ≤ D₂)
    (hD₁H : D₁ ⊓ centralizer ({z} : Set G) = ℬ₁) (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁)
    (hC₁D : C₁ ≤ D₁) (hC₁B : C₁ ⊓ ℬ₁ = 𝒜₁) (hC₁z : zpowers z ⊔ C₁ = D₁)
    (hzC₁ : ∀ c ∈ C₁, z * c * z⁻¹ ∈ C₁)
    (hKz : ∀ j ∈ 𝒜₁ ⊓ 𝒜₂, ∃ k ∈ D₁ ⊓ D₂, k⁻¹ * z * k = z * j)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he)
    (hcomm₂ : ∀ d ∈ D₂, ∀ a ∈ 𝒜₂, d * a = a * d)
    (hC₁sq : ∀ c ∈ C₁, c ^ 2 ∈ zpowers (ptB₁ he hb φ hzC hz))
    (hF₂sq : ∀ f ∈ F₂, f ^ 2 ∈ altSub φ he)
    (hE₂F : E₂ ≤ F₂) (hE₂c : IsMulCommutative E₂) (hE₂card : Nat.card E₂ = 512)
    (hE₂uniq : ∀ E' : Subgroup G, E' ≤ F₂ → IsMulCommutative E' → Nat.card E' = 512 → E' = E₂)
    (hE₂R : E₂ ⊓ ℛ = 𝒜₂)
    (hY : ∀ Y : Subgroup G, Y ≤ F₂ → IsMulCommutative Y →
      4 ≤ Subgroup.relIndex 𝒜₂ (Y ⊔ 𝒜₂) → Y ≤ E₂) {x : G} (hx : x ∈ E₂) : x ^ 2 = 1 := by
  have hFD : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hAE : 𝒜₂ ≤ E₂ := by
    rw [← hE₂R]
    exact inf_le_left
  have hME := C₁_inf_F₂_le he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B hC₁z hzC₁
    hKz hF₂ hcomm₂ hC₁sq hF₂sq hY
  have hcomm : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂c.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let S : Subgroup G :=
    { carrier := {x | x ∈ E₂ ∧ x ^ 2 = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hcomm x hx.1 y hy.1) 2), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow 2⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hSE : S ≤ E₂ := fun x hx => hx.1
  have hMS : C₁ ⊓ F₂ ⊔ 𝒜₂ ≤ S := sup_le
    (fun m hm => ⟨hME hm, sq_eq_one_of_mem_C₁_inf_F₂ he hb φ hzC hz hC₁sq hF₂sq hm⟩)
    (fun a ha => ⟨hAE ha, sq_eq_one_of_mem_radA he φ ha⟩)
  have hj : tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)) ∈ 𝒜₁ ⊓ altSub φ he :=
    (mem_ptA_inf_altSub_iff he hb φ).2 ⟨1, 0, rfl⟩
  have hzj : z * tauHom φ he (Multiplicative.ofAdd (jSym 0 1 0)) ∈ conjClass (C₁ ⊓ F₂) z := by
    rw [conjClass_C₁_inf_F₂ he hb φ hzC hz hν₂z hRD₂ hγD₁ hC₁D hC₁z hzC₁ hKz hF₂]
    exact Set.smul_mem_smul_set hj
  obtain ⟨m, hm, hmz⟩ := mem_conjClass_iff_right.1 hzj
  have hmD : m ∈ D₂ := hFD (mem_inf.1 hm).2
  have hmν : ν₂ m = jSym 0 1 0 := by
    have h := tauHom_nu he φ hzC hz hν₂z hmD
    rw [hmz, inv_mul_cancel_left] at h
    exact Multiplicative.ofAdd.injective (tauHom_injective φ he h)
  set g := leviHom φ he swapGL with hg
  have hgN : g ∈ 𝒩₂ := leviHom_mem_normalizer_radSub φ he hzC hz swapGL
  have hgz : g * z = z * g := leviHom_mul_z φ he hzC swapGL
  have hF₂g : ∀ f ∈ F₂, g * f * g⁻¹ ∈ F₂ := by
    intro f hf
    obtain ⟨hfD, hfI⟩ := (hF₂ f).1 hf
    refine (hF₂ _).2 ⟨hD₂n g hgN f hfD, ?_⟩
    have h1 := gamma_conj (z := z) (x := f) hgz
    have h2 : z⁻¹ * ((g * f * g⁻¹)⁻¹ * z * (g * f * g⁻¹)) = g * (z⁻¹ * (f⁻¹ * z * f)) * g⁻¹ := by
      calc z⁻¹ * ((g * f * g⁻¹)⁻¹ * z * (g * f * g⁻¹)) =
          z⁻¹ * (g * f * g⁻¹)⁻¹ * z * (g * f * g⁻¹) := by group
        _ = g * (z⁻¹ * f⁻¹ * z * f) * g⁻¹ := h1
        _ = g * (z⁻¹ * (f⁻¹ * z * f)) * g⁻¹ := by group
    rw [h2]
    obtain ⟨B, hB, hBx⟩ := hfI
    rw [← hBx, hg, leviHom_conj_tauHom']
    refine ⟨_, ?_, rfl⟩
    change symThreeDiag ((swapGL : M₃) * (B : M₃) * (swapGL : M₃)ᵀ) = 0
    rw [symThreeDiag_congr _ _ B.2, hB, mulVec_zero]
  have hE₂g : ∀ x ∈ E₂, g * x * g⁻¹ ∈ E₂ := by
    have heq := hE₂uniq (E₂.map (MulAut.conj g).toMonoidHom)
      (by rintro _ ⟨x, hx, rfl⟩; exact hF₂g x (hE₂F hx))
      (by
        have := hE₂c
        exact ⟨⟨fun x y => by
          obtain ⟨_, ⟨x', hx', rfl⟩⟩ := x
          obtain ⟨_, ⟨y', hy', rfl⟩⟩ := y
          apply Subtype.ext
          change g * x' * g⁻¹ * (g * y' * g⁻¹) = g * y' * g⁻¹ * (g * x' * g⁻¹)
          calc g * x' * g⁻¹ * (g * y' * g⁻¹) = g * (x' * y') * g⁻¹ := by group
            _ = g * (y' * x') * g⁻¹ := by rw [hcomm x' hx' y' hy']
            _ = g * y' * g⁻¹ * (g * x' * g⁻¹) := by group⟩⟩)
      (by rw [card_map_of_injective (MulAut.conj g).injective, hE₂card])
    intro x hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  set m₃ := g * m * g⁻¹ with hm₃
  have hm₃S : m₃ ∈ S := by
    refine ⟨hE₂g m (hME hm), ?_⟩
    rw [hm₃, conj_pow, sq_eq_one_of_mem_C₁_inf_F₂ he hb φ hzC hz hC₁sq hF₂sq hm, mul_one,
      mul_inv_cancel]
  have hm₃ν : ν₂ m₃ = ⟨alt3Mat 0 0 1, (mem_binarySymMatrices.2 (by decide))⟩ := by
    rw [hm₃, hg, nu_conj_levi he φ hzC hz hν₂z hD₂n swapGL hmD, hmν]
    apply Subtype.ext
    exact swapMat_alt3Mat
  have hm₃M : m₃ ∉ C₁ ⊓ F₂ ⊔ 𝒜₂ := by
    intro h
    have hMN : C₁ ⊓ F₂ ≤ normalizer (𝒜₂ : Set G) := fun m' hm' => by
      refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha => ?_)
      exact (hcomm₂ m' (hFD (mem_inf.1 hm').2) a ha).symm
    have h' : m₃ ∈ ((C₁ ⊓ F₂ ⊔ 𝒜₂ : Subgroup G) : Set G) := h
    rw [coe_mul_of_left_le_normalizer_right _ _ hMN] at h'
    obtain ⟨m', hm', a, ha, hma⟩ := h'
    have hm'D : m' ∈ C₁ ⊓ D₂ := mem_inf.2 ⟨(mem_inf.1 hm').1, hFD (mem_inf.1 hm').2⟩
    obtain ⟨c, y, y', hc⟩ := nu_eq_jSym he hb φ hzC hz hν₂z hγD₁ hC₁D hm'D
    have haR : a ∈ ℛ := mem_sup_left ha
    have haD : a ∈ D₂ := hRD₂ haR
    have ha0 : ν₂ a = 0 := (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H haD).2 haR
    have hma' : m' * a = m₃ := hma
    have h1 := nu_mul he φ hzC hinf hz hν₂z hpure hm'D.2 haD
    rw [hma', ha0, add_zero, hc, hm₃ν] at h1
    exact zmod_two_jMat_ne_alt3Mat c y y' (congrArg Subtype.val h1).symm
  have hcard := card_C₁_inf_F₂_sup_radA he hb hnd φ hzC hinf hz hν₂z hD₂H hRD₂ hD₁H hγD₁ hC₁D hC₁B
    hC₁z hzC₁ hKz hF₂ hcomm₂
  have hdvd : 256 ∣ Nat.card S := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hMS
  have hle : Nat.card S ≤ 512 := by
    rw [← hE₂card]
    exact Subgroup.card_le_of_le hSE
  have hne : Nat.card S ≠ 256 := by
    intro h
    apply hm₃M
    have heq : C₁ ⊓ F₂ ⊔ 𝒜₂ = S := Subgroup.eq_of_le_of_card_ge hMS (by rw [h, hcard])
    rw [heq]
    exact hm₃S
  have hpos : 0 < Nat.card S := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hS : Nat.card S = 512 := by omega
  have hSE' : S = E₂ := Subgroup.eq_of_le_of_card_ge hSE (by rw [hS, hE₂card])
  have hxS : x ∈ S := by
    rw [hSE']
    exact hx
  exact hxS.2

include hinf in
theorem C₁_inf_D₂_eq_mul {C₁ D₁ D₂ F₂ : Subgroup G} {ν₂ : G → ↥(binarySymMatrices 3)}
    (hν₂z : ∀ d ∈ D₂, d⁻¹ * z * d = radHom φ he hzC hz (Multiplicative.ofAdd (ν₂ d, 1)))
    (hpure : ∀ d ∈ D₂, ∀ (B : ↥(binarySymMatrices 3)) (ε : ZMod 2),
      d⁻¹ * radHom φ he hzC hz (Multiplicative.ofAdd (B, ε)) * d =
        radHom φ he hzC hz (Multiplicative.ofAdd (B + ε • ν₂ d, ε)))
    (hD₂H : D₂ ⊓ centralizer ({z} : Set G) = ℛ)
    (hγD₁ : ∀ d ∈ D₁, z⁻¹ * (d⁻¹ * z * d) ∈ 𝒜₁) (hC₁D : C₁ ≤ D₁)
    (hF₂ : ∀ d : G, d ∈ F₂ ↔ d ∈ D₂ ∧ z⁻¹ * (d⁻¹ * z * d) ∈ altSub φ he)
    {g : G} (hgK : g ∈ C₁ ⊓ D₂) (hgν : ν₂ g = jSym 1 0 0) :
    ((C₁ ⊓ D₂ : Subgroup G) : Set G) =
      ((C₁ ⊓ F₂ : Subgroup G) : Set G) * (zpowers g : Set G) := by
  have hFD : F₂ ≤ D₂ := fun x hx => ((hF₂ x).1 hx).1
  have hmemF : ∀ k ∈ C₁ ⊓ D₂, (∃ y y' : ZMod 2, ν₂ k = jSym 0 y y') → k ∈ C₁ ⊓ F₂ := by
    rintro k hk ⟨y, y', hk0⟩
    refine mem_inf.2 ⟨(mem_inf.1 hk).1, (hF₂ k).2 ⟨(mem_inf.1 hk).2, ?_⟩⟩
    rw [← tauHom_nu he φ hzC hz hν₂z (mem_inf.1 hk).2, hk0]
    refine ⟨_, ?_, rfl⟩
    funext i
    fin_cases i <;> rfl
  ext k
  constructor
  · intro hk
    obtain ⟨c, y, y', hc⟩ := nu_eq_jSym he hb φ hzC hz hν₂z hγD₁ hC₁D hk
    rcases zmod_two_eq_zero_or_eq_one c with rfl | rfl
    · exact ⟨k, hmemF k hk ⟨y, y', hc⟩, 1, one_mem _, mul_one k⟩
    · have hkg : k * g⁻¹ ∈ C₁ ⊓ D₂ := mul_mem hk (inv_mem hgK)
      have hginv : ν₂ g⁻¹ = jSym 1 0 0 := by
        have h1 := nu_mul he φ hzC hinf hz hν₂z hpure hgK.2 (inv_mem hgK.2)
        rw [mul_inv_cancel, (nu_eq_zero_iff he φ hzC hz hν₂z hD₂H (one_mem _)).2 (one_mem _),
          hgν] at h1
        apply Subtype.ext
        have h2 := congrArg Subtype.val h1
        change (0 : M₃) = jMat 1 0 0 + (ν₂ g⁻¹ : M₃) at h2
        change (ν₂ g⁻¹ : M₃) = jMat 1 0 0
        have h3 : (ν₂ g⁻¹ : M₃) = -(jMat 1 0 0) := by
          rw [eq_neg_iff_add_eq_zero, add_comm, ← h2]
        rw [h3]
        decide
      have h1 := nu_mul he φ hzC hinf hz hν₂z hpure hk.2 (inv_mem hgK.2)
      rw [hc, hginv] at h1
      refine ⟨k * g⁻¹, hmemF _ hkg ⟨y, y', ?_⟩, g, mem_zpowers g, by group⟩
      rw [h1]
      apply Subtype.ext
      change jMat 1 y y' + jMat 1 0 0 = jMat 0 y y'
      rw [zmod_two_jMat_add, add_zero, add_zero]
      rfl
  · rintro ⟨m, hm, t, ht, rfl⟩
    exact mul_mem (mem_inf.2 ⟨(mem_inf.1 hm).1, hFD (mem_inf.1 hm).2⟩)
      ((zpowers_le.2 hgK) ht)

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
