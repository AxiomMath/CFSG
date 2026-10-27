module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Big
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma414Small

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem stronglyClosed_of_omega_sylow
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M)
    (hPE : FooteEvenOrNormalizes M) {T A S : Subgroup G} {t₁ : G}
    (hT : IsSylowOf 2 T (coreActionKernel M)) (hA : IsOmegaOneOf A T) (ht₁A : t₁ ∈ A)
    (ht₁1 : t₁ ≠ 1) (htr : ∀ a ∈ A, a ≠ 1 → FooteAConj M A t₁ a)
    (hACC : ∀ a ∈ A, a ≠ 1 → FooteInCC M a) (hS : IsSylowOf 2 S (normalizer (M : Set G)))
    (hSA : S ≤ normalizer (A : Set G)) (hTS : T ≤ S) (hSC : S ⊓ coreActionKernel M = T) :
    ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have hAS : A ≤ S := hA.1.trans hTS
  have hAC : A ≤ C := hA.1.trans hT.le
  have key : ∀ t ∈ A, orderOf t = 2 → (∀ s ∈ S, s * t = t * s) →
      ∀ g : G, g⁻¹ * t * g ∈ S → g⁻¹ * t * g ∈ A := by
    intro t htA ht2 htS g hyS
    by_contra hyA
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; omega
    have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have hy2 : (g⁻¹ * t * g) ^ 2 = 1 := by
      calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * t ^ 2 * g := by rw [sq, sq]; group
        _ = 1 := by rw [ht2']; group
    have hyC : g⁻¹ * t * g ∉ C := fun hyC => hyA (hA.2.2 _
      (by rw [← hSC]; exact mem_inf.mpr ⟨hyS, hyC⟩) hy2)
    have hU8 := card_inf_centralizer_lt_eight h h47 hST hA5 hE8 hK hcalc hM hPE hAC hA.2.1 hS
      ht2 htA htS hyC
    have hyN : g⁻¹ * t * g ∈ N := hS.le hyS
    have hyT : g⁻¹ * t * g ∈ normalizer (T : Set G) := by
      rw [← hSC]
      exact mem_normalizer_inf_of_mem (le_normalizer hyS)
        (normalizer_le_normalizer_coreActionKernel M hyN)
    have hTt : T ≤ centralizer ({t} : Set G) := fun x hx =>
      mem_centralizer_singleton_iff.mpr (htS x (hTS hx))
    have h8 := eight_le_card_inf_centralizer h h47 hST hAsc h2An hM hT hA hACC htA ht1 hTt hy2
      hyN (htS _ hyS) hyT
    omega
  have hA1' : A ≠ ⊥ := fun h1 => ht₁1 (by
    have h2 := ht₁A
    rwa [h1, mem_bot] at h2)
  obtain ⟨t₀, ht₀A, ht₀2, ht₀S⟩ := exists_involution_inf_center hS.isPGroup hAS hSA hA1'
  have ht₀1 : t₀ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht₀2; omega
  intro a ha g hga
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, inv_mul_cancel]
    exact one_mem A
  obtain ⟨n, -, -, hna⟩ := (htr t₀ ht₀A ht₀1).symm.trans (htr a ha ha1)
  have heq : g⁻¹ * a * g = (n⁻¹ * g)⁻¹ * t₀ * (n⁻¹ * g) := by rw [← hna]; group
  rw [heq] at hga ⊢
  exact key t₀ ht₀A ht₀2 ht₀S _ hga

theorem isSylowOf_top_of_stronglyClosed {A S N : Subgroup G} (hS : IsSylowOf 2 S N)
    (hAS : A ≤ S) (hNA : normalizer (A : Set G) ≤ N)
    (hcl : ∀ a ∈ A, ∀ g : G, g⁻¹ * a * g ∈ S → g⁻¹ * a * g ∈ A) : IsSylowOf 2 S ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_ge_of_le (le_top : S ≤ ⊤) hS.isPGroup
  by_cases hSP' : S = P
  · rw [hSP']
    exact hP
  obtain ⟨x, hxP, hxS, hxN⟩ := exists_mem_normalizer_of_lt hP.isPGroup (lt_of_le_of_ne hSP hSP')
  have hxA : x ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 : x * a * x⁻¹ ∈ S := (mem_normalizer_iff.mp hxN a).mp (hAS ha)
      have h2 := hcl a ha x⁻¹ (by rwa [inv_inv])
      rwa [inv_inv] at h2
    · intro ha
      have h1 : x⁻¹ * (x * a * x⁻¹) * x ∈ S := by
        rw [show x⁻¹ * (x * a * x⁻¹) * x = a by group]
        exact (mem_normalizer_iff.mp hxN a).mpr (hAS ha)
      have h2 := hcl _ ha x h1
      rwa [show x⁻¹ * (x * a * x⁻¹) * x = a by group] at h2
  have hxN' : x ∈ N := hNA hxA
  have hp : IsPGroup 2 ↥(S ⊔ zpowers x) :=
    hP.isPGroup.to_le (sup_le hSP (zpowers_le.mpr hxP))
  have h1 := hS.eq_of_le le_sup_left (sup_le hS.le (zpowers_le.mpr hxN')) hp
  exact (hxS (by rw [← h1]; exact mem_sup_right (mem_zpowers x))).elim

end CFSG.ComponentClassification.FooteLit
