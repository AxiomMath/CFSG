module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1GEVStarSmall {G : Type} [Group G] [Finite G] (p : ℕ) (P : Sylow p G)
    (M R : Subgroup G) (z : G) (K : Type) [Group K] : Prop :=
  ∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
    ∃ (Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p))
      (Ls : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)),
      D1OneSmallData p P M Hs R Rbars Ls ∧ D1SmallCZElt p Hs R Ls z ∧ Nonempty (Ls ≃* K)

@[expose] def D1SmallGEVIbNormal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    ¬ D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    ¬ (p = 3 ∧ IsAltTwoP 3 K) → ¬ (p = 3 ∧ IsSmallUnitary 3 K) →
    ¬ (p = 3 ∧ IsLinThreeFour K) →
    ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    GLBIsMaxTwoLocal H →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    D1GEVStarSmall p P M R z K →
    (∀ Hs : Subgroup G, GLBIsMaxTwoLocal Hs →
      Subgroup.normalizer
        (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ Hs →
      ∀ hzHs : z ∈ Hs, ¬ (Subgroup.zpowers
        (QuotientGroup.mk' (primeComplementCore (G := Hs) p) ⟨z, hzHs⟩)).Normal) → False

@[expose] def D1SmallGEVNormalFi22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)), D1OneSmallData p P M H R Rbar K →
    ∀ z : G, D1SmallCZElt p H R K z →
    D1SmallIa p H K → D1CzB0 p R z → D1CzEven p z → D1CzIso p z K →
    p = 5 → IsFi22 K → 3 ∉ GLBBetaFour G →
    (∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) →
    ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (R : Set G) →
    Subgroup.normalizer
      (pCoreOf 2 (GLBPrimeCore p (Subgroup.centralizer ({z} : Set G))) : Set G) ≤ H →
    Subgroup.centralizer ({z} : Set G) ≤ H →
    GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≤ GLBPrimeCore p H →
    (∀ hzH : z ∈ H,
      (Subgroup.zpowers (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨z, hzH⟩)).Normal) →
    False

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem twoCore_inf_core_ne_bot_of_comm (hd : D1OneSmallData p P M H R Rbar K) {z : G}
    (hcomm : ∀ u ∈ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G), ∀ r ∈ R,
      u * r * u⁻¹ * r⁻¹ ∈ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)))
    (hnot : ¬ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer (R : Set G)) :
    pCoreOf 2 M ⊓ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := by
  intro hbot
  apply hnot
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hrM : r ∈ M := hd.cfg.ext.le_M hr
  have huQ : r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 M hrM) _).mp
      ((pCoreOf 2 M).inv_mem hu.1)
  have hcQ : u * r * u⁻¹ * r⁻¹ ∈ pCoreOf 2 M := by
    have h := (pCoreOf 2 M).mul_mem hu.1 huQ
    simpa only [mul_assoc] using h
  have hc1 : u * r * u⁻¹ * r⁻¹ = 1 := by
    have hmem : u * r * u⁻¹ * r⁻¹ ∈
        pCoreOf 2 M ⊓ GLBPrimeCore p (Subgroup.centralizer ({z} : Set G)) :=
      ⟨hcQ, hcomm u hu r hr⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  calc r * u = (u * r * u⁻¹ * r⁻¹)⁻¹ * (u * r) := by group
    _ = u * r := by rw [hc1, inv_one, one_mul]

end CFSG.AGLEmbedding
