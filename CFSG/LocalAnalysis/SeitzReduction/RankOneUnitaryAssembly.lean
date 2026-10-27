module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEnding
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySixNineTwoBurnside
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearMain
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryFreeTransfer

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_u3Start {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : SeitzSetting G L) {f : ℕ} (hf : 2 ≤ f) (hm : LieModel L .PSU 3 2 f)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ (t : G) (T : Subgroup G), U3Start G L f t T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  have h2 : 2 ∣ Nat.card (centralizer (L : Set G)) := by
    have := Subgroup.card_subgroup_dvd_card (S₀ : Subgroup (centralizer (L : Set G)))
    rwa [hS2 S₀] at this
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2 h2
  have ht : orderOf (c : G) = 2 := by rw [Subgroup.orderOf_coe, hc]
  obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer ({(c : G)} : Set G))) := inferInstance
  refine ⟨c, (P : Subgroup _).map (centralizer ({(c : G)} : Set G)).subtype,
    ⟨hset, hm, hf, ht, c.2, map_subtype_le _, P, ?_⟩⟩
  exact (comap_map_eq_self_of_injective (subtype_injective _) _).symm

section Certificates

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem exists_u3EndingData_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hstar : StarPrimeStatement f)
    {R₂ : Subgroup G} (hR : U3R2 G L (szT₁ L T) R₂ t f) (hc : ¬ ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹)
    (hfour : U3SixNineFourInput) :
    ∃ (U₁ : Subgroup G) (s : G), U3EndingData G L f t T R₂ U₁ s := by
  obtain ⟨hΩ, E, hE, hEn, hEreg⟩ := h.omega_regular_of_semilinear_of_card_sylow hS2 hR hstar hc
  have hU := h.u3U1Data_of_card_sylow hS2 hR hc hΩ hE hEn hEreg
  have hncyc := h.not_isCyclic_quot_of_card_sylow hS2 hR hc hΩ ⟨E, hE, hEn, hEreg⟩
  have hnS := hU.not_isSylow_sup h hS2 hR hncyc (u3SixNineInput_of_four hfour)
  obtain ⟨s, hsN, hsP, hsQ, hst⟩ := hU.exists_normalizer_conj_not_mem h hS2 hR hnS
  have hs := mem_inf.mp (hU.normalizer_sup_le_of_not_isCyclic h hS2 hR hncyc hsN)
  exact ⟨_, s, h, hS2, hstar, hR, hc, hΩ, ⟨E, hE, hEn, hEreg, rfl⟩, hU, hncyc, hnS, hsN, hsP,
    hsQ, hst, fun w hwT hw2 hwS => hU.exists_eq_mul_of_conj_not_mem h hS2 hR hwT hw2 hwS hsN hst,
    hs.1, hs.2⟩

end U3Start

theorem rankOneUnitaryExclusion_of_starPrime (hstar : ∀ f : ℕ, 2 ≤ f → StarPrimeStatement f)
    (hC1 : U3C1Exclusion) (hfour : U3SixNineFourInput) (hend : U3EndingInput) :
    RankOneUnitaryExclusion := by
  intro G _ _ L hset f hf hm hS2
  obtain ⟨t, T, h⟩ := exists_u3Start hset hf hm hS2
  obtain ⟨R₂, hR, -, -, -⟩ := h.exists_u3R2_of_card_sylow hS2
  by_cases hinv : ∀ r ∈ R₂, t * r * t⁻¹ = r⁻¹
  · by_cases hel : ∀ r ∈ R₂, r ^ 2 = 1
    · apply h.t_not_mem_centralizer_of_card_sylow hS2 hR
      refine mem_centralizer_iff.mpr fun r hr => ?_
      have hrr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hel r hr)
      have htr : t * r * t⁻¹ = r := by rw [hinv r hr, hrr]
      calc r * t = t * r * t⁻¹ * t := by rw [htr]
        _ = t * r := by group
    · push Not at hel
      exact hC1 G L f t T R₂ h hS2 hR hinv hel
  · obtain ⟨U₁, s, hD⟩ := h.exists_u3EndingData_of_card_sylow hS2 (hstar f hf) hR hinv hfour
    exact hend G L f t T R₂ U₁ s hD

end Certificates

end CFSG.SeitzReduction.RankOne
