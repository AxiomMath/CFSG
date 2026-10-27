module

public import CFSG.LocalAnalysis.OddStandard.Solomon75T11bOddCore
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHTD4Odd
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87G2Three
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FD4

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.Blueprint CFSG.ClassicalInvolution CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage2.Signalizer

section G2D4


theorem pPrimeCore_cen_eq_bot_of_g2d4 {G : Type} [Group G] [Finite G] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hm : LieModel G .G2 0 p f ∨ LieModel G .trialityD4 0 p f) {t : G} (ht : orderOf t = 2) :
    pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rcases hm with hG | hD
  · have h3 : 3 ≤ p ^ f :=
      le_trans (by have := hp.two_le; omega : 3 ≤ p) (Nat.le_self_pow (by omega) p)
    obtain ⟨e⟩ := Odd87.equiv_modelUniv_g2 hp hp2 hf h3 hG
    exact pPrimeCore_cen_eq_bot_of_equiv e
      (Asc77.thm5IH_g2_oddCoreTrivial hp2 ⟨hp, hf, rfl, h3⟩) ht
  · obtain ⟨e⟩ := Odd87.equiv_modelUniv_d4 hp hp2 hf hD
    exact pPrimeCore_cen_eq_bot_of_equiv e
      (Asc77.thm5IH_td4_oddCoreTrivial hp2 ⟨hp, hf, rfl⟩) ht

end G2D4

end CFSG.OddStandard.Solomon75
