module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutJ
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutId
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutTheta
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelCd

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Monster.B.Fischer CFSG.Sporadic.Fi23 FrameJ

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem Cd_aut_cent_of_exists
    (H : ∃ N₀ : Subgroup fi22P, (∀ v ∈ N₀, v ^ 2 = 1) ∧ Nat.card N₀ = 2 ^ 10 ∧
      CentralizerCore N₀) :
    ∀ σ : MulAut ↥Cd, (∀ e ∈ E0, σ e = e) → ∃ x ∈ E0, σ = MulAut.conj x := by
  obtain ⟨N₀, hN₀sq, hN₀card, hC⟩ := H
  have hker : piP.ker ≤ E0 := by
    rw [ker_piP]
    exact E0_center_le
  have hVcard : Nat.card (E0.map piP) = 2 ^ 10 :=
    card_map_of_ker piP E0 card_ker_piP hker (n := 10) E0_card
  have hVsq : ∀ v ∈ E0.map piP, v ^ 2 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, E0_sq e he, map_one]
  obtain ⟨g, hg⟩ := exists_conj_P (E0.map piP) N₀ hVsq hVcard hN₀sq hN₀card
  have hV : CentralizerCore (E0.map piP) := by
    rw [hg]
    exact centralizerCore_conj N₀ g hC
  exact Cd_aut_cent_of_core hV

end CFSG.EvenSporadicStandard.TwoFi22.DS81
