module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFWreath
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxOutNFKill

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X] {M : Subgroup X} {n : ℕ}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)}

theorem IsPermAction.not_isPComponent_layer_of_noFix (hρ : IsPermAction θ ρ) [Finite X]
    (hn : 9 ≤ n) (hodd : Odd n) {a : X} (hCaN : centralizer ({a} : Set X) ≤ normalizer (M : Set X))
    {L : Subgroup X} (hLM : L ≤ M) (θL : ↥L ⧸ pPrimeCore 2 ↥L ≃* alternatingGroup (Fin n))
    (hθL : ∀ (x : X) (hxL : x ∈ L) (hxM : x ∈ M), θL ((⟨x, hxL⟩ : ↥L) : ↥L ⧸ pPrimeCore 2 ↥L) =
      θ ((⟨x, hxM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M))
    (hLN : ∀ g ∈ normalizer (M : Set X), g * a = a * g → g ∈ normalizer (L : Set X))
    {c : X} (hcN : c ∈ normalizer (M : Set X)) (hc2 : c * c = 1) (hca : c * a = a * c)
    (hcA : ρ ⟨c, hcN⟩ ∈ alternatingGroup (Fin n)) (h5 : n - (ρ ⟨c, hcN⟩).support.card < 5)
    {Y : Subgroup X} (hLY : L ⊓ centralizer ({c} : Set X) ≤ Y)
    (hYC : Y ≤ centralizer ({a} : Set X) ⊓ centralizer ({c} : Set X)) {R : Subgroup X}
    (hRL : R ≤ L) (hRY : R ≤ Y) : ¬ IsPComponent 2 (R.subgroupOf Y) := by
  classical
  obtain ⟨ρL, hρL⟩ := exists_isPermAction (M := L) (by omega) (by omega) θL
  have hcL : c ∈ normalizer (L : Set X) := hLN c hcN hca
  have hρLc : ρL ⟨c, hcL⟩ = ρ ⟨c, hcN⟩ := hρ.apply_eq_of_le (by omega) hLM hρL hθL hcL hcN
  have hσ2 : ρ ⟨c, hcN⟩ * ρ ⟨c, hcN⟩ = 1 := by
    rw [← map_mul, show (⟨c, hcN⟩ : ↥(normalizer (M : Set X))) * ⟨c, hcN⟩ = 1 from
      Subtype.ext hc2, map_one]
  obtain ⟨q, hq⟩ := four_dvd_card_support_of_mem_alternating hσ2 hcA
  have hcard : (ρ ⟨c, hcN⟩).support.card ≤ n := by
    have := Finset.card_le_univ (ρ ⟨c, hcN⟩).support
    rwa [Fintype.card_fin] at this
  obtain ⟨m, hm⟩ := hodd
  have hYN : Y ≤ normalizer (L : Set X) := fun z hz =>
    hLN z (hCaN (mem_inf.mp (hYC hz)).1)
      (mem_centralizer_singleton_iff.mp (mem_inf.mp (hYC hz)).1)
  exact hρL.not_isPComponent_of_fix_le_three (by omega) hcL hc2 (by rw [hρLc]; omega)
    (by rw [hρLc]; omega) hLY hYN (hYC.trans inf_le_right) hRL hRY

end CFSG.ComponentClassification.SolMax
