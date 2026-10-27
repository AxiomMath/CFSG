module

public import CFSG.FeitThompson.Representations.TypeVTwoFamilyCoherenceJoining
public import CFSG.FeitThompson.Representations.ExceptionalOrderBoundPrimeLinearFamily

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeCubeDivisorCoherence

open TypeVTwoFamilyJoining NormalLinearInduced

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]

structure IsPrimeCubeDivisorHyp (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) (ζ : ↥L → ℂ) (p d n : ℕ) (δ : ℤ)
    (A₀ : Set G) (T : G → Subgroup G)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G) : Prop where
  arrayHyp : IsPrimeCubeArrayHyp h σ ζ p d n (δ : ℂ)
  sq_le : p ^ 2 ≤ 4 * Nat.card ↥W₁ ^ 2 + 1
  dvd : Nat.card ↥W₁ ∣ p + 1
  odd : Odd (Nat.card G)
  isDadeData : IsDadeData L A₀ T
  image_subset :
    (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀
  stabilizer_eq : {g : G | (fun x => g⁻¹ * x * g) ''
      cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
    = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G)
  inter_eq_empty : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
    (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω

namespace IsPrimeCubeDivisorHyp

variable {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {p d n : ℕ} {δ : ℤ} {A₀ : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  (hC : IsPrimeCubeDivisorHyp h σ ζ p d n δ A₀ T ω)

include hC

omit [K.Normal] in
theorem prime_eq : (p : ℤ) = 2 * (Nat.card ↥W₁ : ℤ) - 1 := by
  refine ExceptionalOrderBound.eq_two_mul_sub_one ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨k, hk⟩ := hC.arrayHyp.odd; exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  · exact_mod_cast hC.arrayHyp.prime.pos
  · obtain ⟨k, hk⟩ := h.isCyclicTIPair.odd_natCard_left; exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  · exact_mod_cast h.isCyclicTIPair.three_le_natCard_left
  · exact_mod_cast Int.natCast_dvd_natCast.2 hC.dvd
  · exact_mod_cast hC.sq_le

omit [K.Normal] in
theorem prime_add_one_eq : p + 1 = 2 * Nat.card ↥W₁ := by
  have h1 := hC.prime_eq
  omega

omit [K.Normal] in
theorem sign_eq_neg_one_and_eq_two : δ = -1 ∧ (n : ℤ) = 2 := by
  have := Fintype.ofFinite ↑(Irr ↥W₁)
  have := Fintype.ofFinite ↑(Irr ↥W₂)
  have hd := hC.arrayHyp.degree_eq
  rw [hC.arrayHyp.d_eq_prime] at hd
  have hsub : (p : ℤ) - δ = (n : ℤ) * (Nat.card ↥W₁ : ℤ) := by exact_mod_cast hd
  refine ExceptionalOrderBound.eq_neg_one_and_eq_two ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsub
  · obtain ⟨k, hk⟩ := hC.arrayHyp.odd; exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  · exact_mod_cast hC.arrayHyp.prime.pos
  · obtain ⟨k, hk⟩ := h.isCyclicTIPair.odd_natCard_left; exact ⟨(k : ℤ), by exact_mod_cast hk⟩
  · exact_mod_cast h.isCyclicTIPair.three_le_natCard_left
  · exact_mod_cast Int.natCast_dvd_natCast.2 hC.dvd
  · exact_mod_cast hC.sq_le
  · rcases hC.arrayHyp.sign with hs | hs
    · left; exact_mod_cast hs
    · right; exact_mod_cast hs
  · have := hC.arrayHyp.two_le_n; omega

omit [K.Normal] in
theorem card_lt : Nat.card ↥W₁ < Nat.card ↥W₂ := by
  have h1 := hC.prime_add_one_eq
  have h2 : 3 ≤ Nat.card ↥W₁ := h.isCyclicTIPair.three_le_natCard_left
  rw [hC.arrayHyp.card_W₂]
  omega

omit [K.Normal] in
theorem eight_le_ncard : 8 ≤ (indFamLinear K).ncard := by
  have := Fintype.ofFinite ↑(Irr ↥W₁)
  have := Fintype.ofFinite ↑(Irr ↥W₂)
  have hcount := hC.arrayHyp.ncard_indFamLinear_mul
  have h1 := hC.prime_add_one_eq
  have h3 : 3 ≤ Nat.card ↥W₁ := h.isCyclicTIPair.three_le_natCard_left
  have hkey : 8 * Nat.card ↥W₁ ≤ p ^ 2 - 1 := by
    have hsq : 8 * Nat.card ↥W₁ + 1 ≤ p ^ 2 := by nlinarith
    omega
  rw [← hcount] at hkey
  exact Nat.le_of_mul_le_mul_right hkey Nat.card_pos

omit [K.Normal] in
theorem isUniformBridgeData : h.IsUniformBridgeData σ ζ (p : ℤ) 2 δ where
  isometry := hC.arrayHyp.isometry
  mem_indFam := hC.arrayHyp.zeta_mem_indFam
  mem_Irr := hC.arrayHyp.zeta_mem_Irr
  apply_one := hC.arrayHyp.zeta_one
  one_lt := by have := hC.arrayHyp.three_le_prime; omega
  two_le := le_refl 2
  sign := by
    rcases hC.arrayHyp.sign with hs | hs
    · left; exact_mod_cast hs
    · right; exact_mod_cast hs
  primeTIirr_one := by
    have := Fintype.ofFinite ↑(Irr ↥W₁)
    have := Fintype.ofFinite ↑(Irr ↥W₂)
    intro i j hj
    rw [hC.arrayHyp.primeTIirr_one_eq i j hj, hC.arrayHyp.d_eq_prime]
    norm_cast
  primeTISign_eq := fun j hj => hC.arrayHyp.primeTISign_eq j hj
  sub_eq := by
    have h1 := hC.prime_eq
    have h2 := hC.sign_eq_neg_one_and_eq_two.1
    omega

section
variable [Fintype ↑(Irr ↥W₁)]

omit [K.Normal] in
theorem isTypeVTwoFamilyData :
    IsTypeVTwoFamilyData h σ ζ (p : ℤ) δ A₀ T ω (indFamLinear K) where
  local_data := hC.isUniformBridgeData
  odd := hC.odd
  isDadeData := hC.isDadeData
  image_subset := hC.image_subset
  stabilizer_eq := hC.stabilizer_eq
  inter_eq_empty := hC.inter_eq_empty
  omega_isometry := hC.omega_isometry
  card_lt := hC.card_lt
  union_eq := by
    have := Fintype.ofFinite ↑(Irr ↥W₂)
    exact hC.arrayHyp.indFam_eq_union
  subset_Irr := by
    have := Fintype.ofFinite ↑(Irr ↥W₂)
    exact hC.arrayHyp.indFamLinear_subset_Irr
  star_mem := fun _ hχ => conj_mem_indFamLinear K hχ
  zeta_mem := by
    have := Fintype.ofFinite ↑(Irr ↥W₂)
    exact hC.arrayHyp.zeta_mem_indFamLinear
  eight_le := hC.eight_le_ncard
  degree_eq := fun _ hχ => h.apply_one_of_mem_indFamLinear hχ

end

theorem exists_isCoherent_indFam :
    IsCoherent (indFam K (Irr ↥K \ {1}))
      (subDadeHom hC.isDadeData (subset_refl (indFam K (Irr ↥K \ {1}))) hC.image_subset) := by
  have := Fintype.ofFinite ↑(Irr ↥W₁)
  exact hC.isTypeVTwoFamilyData.exists_isCoherent_indFam

end IsPrimeCubeDivisorHyp

end PrimeCubeDivisorCoherence

end CFSG.FeitThompson

end
