module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2Base
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CHom
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

public section

namespace CFSG.ComponentClassification.CatLeafProof.Q81P2

open CFSG Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow

theorem exists_odd_U4 {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) (α : MulAut (hypPSU h 2 0)) (hα : α ^ 2 = 1) :
    ∃ T : Set (hypPSU h 2 0), (∀ t ∈ T, α t = t ∧ Odd (orderOf t)) ∧
      2 ∣ Nat.card (closure T) := by
  obtain ⟨k, _, _, hk, ρ, heven, hfix⟩ :=
    exists_fixed_even_sl2 h hp (by norm_num) (by norm_num) (by norm_num) α hα
  have hpr : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  exact exists_odd_of_hom ρ (fun g => hfix _ ⟨g, rfl⟩)
    LinearGroups.special_linear_elementary_generation
    (fun s hs => GSThmB.Cent516.odd_orderOf_of_mem_elementarySet hpr hk hs)
    (even_iff_two_dvd.mp heven)

theorem exists_odd_of_lieModel_psu {L : Type} [Group L] (hL : Blueprint.LieModel L .PSU 4 3 1)
    (β : MulAut L) (hβ : β * β = 1) :
    ∃ T : Set L, (∀ t ∈ T, β t = t ∧ Odd (orderOf t)) ∧ 2 ∣ Nat.card (closure T) := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (3 ^ 1) ^ 2 ∧ Nonempty (L ≃*
        Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 4 (3 ^ 1) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData 3 1 K := ⟨Nat.prime_three, le_rfl, by rw [hcard]; norm_num⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 0) h
  set e : L ≃* hypPSU h 2 0 := e₀.trans (hypPSUEquivStatedProj h hR₀ (by norm_num)).symm
  have hα : MulAut.congr e β ^ 2 = 1 := by rw [← map_pow, sq, hβ, map_one]
  obtain ⟨T, hT, h2⟩ := exists_odd_U4 h (by norm_num) _ hα
  exact exists_odd_congr e β hT h2

end CFSG.ComponentClassification.CatLeafProof.Q81P2
