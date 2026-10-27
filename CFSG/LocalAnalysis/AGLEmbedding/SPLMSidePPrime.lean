module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSide
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideOrbit
import CFSG.LocalAnalysis.AGLEmbedding.SPLMSideFaithful
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

@[expose] def KFactPPrimeCompInvolutionP : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ Λ : Subgroup Y, CFSG.IsComponent Λ → IsCatalogGroup (↥Λ ⧸ Subgroup.center ↥Λ) →
    ¬ p ∣ (Subgroup.center Λ).index →
    ∀ (T₁ : Subgroup Y) (u : Y), T₁ ≤ Subgroup.normalizer (Λ : Set Y) →
      (∀ a ∈ T₁, a ^ p ∈ Subgroup.centralizer (Λ : Set Y)) →
      u ∈ Subgroup.normalizer (Λ : Set Y) → u ^ p = 1 →
      (∀ t ∈ T₁, t * u = u * t) → u ∉ Subgroup.centralizer (Λ : Set Y) →
      ∃ j ∈ Λ, j ≠ 1 ∧ j ^ 2 = 1 ∧ j * u = u * j ∧ ∀ t ∈ T₁, j * t = t * j

namespace SPLMSide

@[expose] def PPrimeComponentInvolutionP (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  ∀ Λ : Subgroup G, CFSG.IsComponent Λ → ¬ p ∣ (Subgroup.center Λ).index →
    ∀ (T₁ : Subgroup G) (u : G), T₁ ≤ Subgroup.normalizer (Λ : Set G) →
      (∀ a ∈ T₁, a ^ p ∈ Subgroup.centralizer (Λ : Set G)) →
      u ∈ Subgroup.normalizer (Λ : Set G) → u ^ p = 1 →
      (∀ t ∈ T₁, t * u = u * t) → u ∉ Subgroup.centralizer (Λ : Set G) →
      ∃ j ∈ Λ, j ≠ 1 ∧ j ^ 2 = 1 ∧ j * u = u * j ∧ ∀ t ∈ T₁, j * t = t * j

variable {G : Type} [Group G] [Finite G]

theorem dvd_index_center_of_moved_P {p : ℕ} {u : G} {T X Λ : Subgroup G}
    (hΛ : CFSG.IsComponent Λ) (hup1 : u ^ p = 1)
    (hu : u ∈ Subgroup.normalizer (Λ : Set G)) (hunc : u ∉ Subgroup.centralizer (Λ : Set G))
    (hTC : T ≤ Subgroup.centralizer ({u} : Set G))
    (hTN : T ≤ Subgroup.normalizer (Λ : Set G)) (hTp : ∀ a ∈ T, a ^ p ∈ X)
    (hXE : ∀ x ∈ X, ∀ a ∈ Λ, x * a = a * x)
    (hCT : ∀ j ∈ Subgroup.centralizer ({u} : Set G), (∀ t ∈ T, j * t = t * j) → j ^ 2 = 1 →
      j = 1)
    (hK2 : PPrimeComponentInvolutionP G p) : p ∣ (Subgroup.center Λ).index := by
  by_contra hpZ
  have hTu : ∀ t ∈ T, t * u = u * t := fun t ht =>
    (Subgroup.mem_centralizer_iff.mp (hTC ht) u (Set.mem_singleton u)).symm
  have hTp' : ∀ a ∈ T, a ^ p ∈ Subgroup.centralizer (Λ : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hXE _ (hTp a ha) y hy).symm
  obtain ⟨j, -, hj1, hj2, hju, hjT⟩ := hK2 Λ hΛ hpZ T u hTN hTp' hu hup1 hTu hunc
  have hjC : j ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hju.symm
  exact hj1 (hCT j hjC hjT hj2)

theorem faithful_of_moved_P {p r : ℕ} [Fact p.Prime] {u c : G} {T X : Subgroup G}
    (hup1 : u ^ p = 1)
    (hu : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → u ∈ Subgroup.normalizer (Λ : Set G))
    (hunc : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → u ∉ Subgroup.centralizer (Λ : Set G))
    (hTC : T ≤ Subgroup.centralizer ({u} : Set G)) (hXT : X ≤ T)
    (hTN : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → T ≤ Subgroup.normalizer (Λ : Set G))
    (hTp : ∀ a ∈ T, a ^ p ∈ X)
    (hcC : c ∈ Subgroup.centralizer ({u} : Set G)) (hcT : ∀ t ∈ T, c * t * c⁻¹ ∈ T)
    (hcX : ∀ x ∈ X, c * x = x * c) (hcr : ∃ k : ℕ, c ^ r ^ k = 1) (hr : r.Prime)
    (hr5 : 5 ≤ r)
    (hirr : ∀ V : Subgroup G, X ≤ V → V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
      (∀ v ∈ V, c * v * c⁻¹ ∈ V) → V = X ∨ V = T)
    (hXel : CFSG.Open.IsElemAbelian p X) (hXcard : Nat.card X = p ^ 2)
    (hXE : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → ∀ x ∈ X, ∀ a ∈ Λ, x * a = a * x)
    (hZX : ∀ Λ : Subgroup G, CFSG.IsComponent Λ → ∀ φ ∈ Λ, (∀ a ∈ Λ, a * φ = φ * a) →
      (∃ k : ℕ, φ ^ p ^ k = 1) → φ ∈ X)
    (hrank : ∀ A : Subgroup G, A ≤ Subgroup.centralizer ({u} : Set G) →
      CFSG.Open.IsElemAbelian p A → Nat.card A < p ^ 6)
    (hCT : ∀ j ∈ Subgroup.centralizer ({u} : Set G), (∀ t ∈ T, j * t = t * j) → j ^ 2 = 1 →
      j = 1)
    (hK2 : PPrimeComponentInvolutionP G p)
    (Λ : Subgroup G) (hΛ : CFSG.IsComponent Λ) (hmov : ∃ t ∈ T, t ∉
      Subgroup.centralizer (Λ : Set G)) :
    p ∣ (Subgroup.center Λ).index ∧ c ∈ Subgroup.normalizer (Λ : Set G) ∧
      T ⊓ Subgroup.centralizer (Λ : Set G) ≤ X := by
  have hup : ∃ k : ℕ, u ^ p ^ k = 1 := ⟨1, by rw [pow_one]; exact hup1⟩
  have hpZ := dvd_index_center_of_moved_P hΛ hup1 (hu Λ hΛ) (hunc Λ hΛ) hTC (hTN Λ hΛ) hTp
    (hXE Λ hΛ) hCT hK2
  have hcN := mem_normalizer_of_rank hΛ hup (hu Λ hΛ) hcC hcX hcr hr hr5 (hXT.trans hTC) hXel
    hXcard hXE (hZX Λ hΛ) hrank hpZ
  exact ⟨hpZ, hcN, inf_centralizer_le_of_moved hXT (hXE Λ hΛ) (hTN Λ hΛ) hcN hcT hirr hmov⟩

end SPLMSide

theorem false_of_splMSideConfig_P {p r : ℕ} {Y : Type} [Group Y] [Finite Y] {u c : Y}
    {T X O : Subgroup Y} (h : SPLMSideConfig p Y u c r T X O)
    (hK2 : KFactPPrimeCompInvolutionP) (hK3 : KFactSPLBlockTorus) : False := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hTN := SPLMSide.le_normalizer_of_components h.ne_two h.u_pow h.u_norm h.T_le h.X_le h.T_p
    h.O_coprime h.TO_norm h.T_X h.T_O h.c_mem h.c_T h.irr h.X_E h.Z_X
  obtain ⟨t, ht, htX⟩ : ∃ t ∈ T, t ∉ X := by
    by_contra hno
    push Not at hno
    have h1 : X.relIndex T = 1 := Subgroup.relIndex_eq_one.mpr hno
    rw [h.index] at h1
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) h.prime.one_lt
    omega
  obtain ⟨Λ, hΛ, hmov⟩ : ∃ Λ : Subgroup Y, CFSG.IsComponent Λ ∧
      t ∉ Subgroup.centralizer (Λ : Set Y) := by
    by_contra hno
    push Not at hno
    apply htX
    refine h.E_le t ht fun Λ hΛ a ha => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hno Λ hΛ) a ha).symm
  have hK2' : SPLMSide.PPrimeComponentInvolutionP Y p := by
    intro Λ' hΛ' hpZ T₁ u' hT₁N hT₁p hu'N hu'p hu'T hu'c
    exact hK2 Y p h.prime h.ne_two Λ' hΛ' (h.catalog Λ' hΛ') hpZ T₁ u' hT₁N hT₁p hu'N hu'p
      hu'T hu'c
  have hr5 := five_le_of_dvd_sq_add_one h.ne_two h.prime h.r_prime h.r_dvd h.r_ndvd
  obtain ⟨hpZ, hcN, hTX⟩ := SPLMSide.faithful_of_moved_P h.u_pow h.u_norm h.u_noncent h.T_le
    h.X_le hTN h.Tp h.c_mem h.c_T h.c_X h.c_pow h.r_prime hr5 h.irr h.X_elem h.X_card h.X_E
    h.Z_X h.rank h.CT_odd hK2' Λ hΛ ⟨t, ht, hmov⟩
  have hsolv : Group.IsSolvable ↥(Λ ⊓ Subgroup.centralizer ({u} : Set Y)) := by
    have := h.solv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_right)
  have hTX' : T ⊓ Subgroup.centralizer (Λ : Set Y) = X := by
    refine le_antisymm hTX (le_inf h.X_le fun x hx => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (h.X_E Λ hΛ x hx a ha).symm
  exact hK3 Y Λ p r hΛ h.prime h.ne_two h.r_prime h.r_dvd h.r_ndvd (h.types Λ hΛ hpZ)
    (h.catalog Λ hΛ) u c T X
    (h.u_norm Λ hΛ) h.u_pow (h.u_noncent Λ hΛ) hsolv (hTN Λ hΛ) h.T_le h.X_le hTX' h.TT h.Tp
    h.index hcN h.c_mem h.c_pow h.c_T h.irr

theorem d1SmallSPLPair_of_mside_P (hBr : D1SPLMSideBridge) (hK2 : KFactPPrimeCompInvolutionP)
    (hK3 : KFactSPLBlockTorus) : D1SmallSPLPair := by
  intro G _ _ p P M H R Rbar K hd huniq z hz hLA hSP hout hVK hVC hIa hN
  obtain ⟨u, c, r, T, X, O, hcfg⟩ :=
    hBr G p P M H R Rbar K hd huniq z hz hLA hSP hout hVK hVC hIa hN
  exact false_of_splMSideConfig_P hcfg hK2 hK3

end CFSG.AGLEmbedding
