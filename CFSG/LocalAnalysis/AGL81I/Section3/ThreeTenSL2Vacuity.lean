module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenCase1

public section
namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {H : Type} [Group H] [Finite H]

@[expose] def ThreeTenSL2Vacuity : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
    ThreeTenHyp I D P Y p d →
      (IsSLType 2 (ZMod p) ↥I ∨ IsPSLType 2 (ZMod p) ↥I) → False

@[expose] def ThreeTenSL3Data (I D Y : Subgroup H) (p d : ℕ) : Prop :=
  D ≤ I ∧ IsCyclic ↥D ∧ ThreeTenTorusExclusion p d ∧ IsMaxParabolicP p I Y

theorem threeTenCase1_of_data
    (hv : ThreeTenSL2Vacuity)
    (hs : ∀ (H : Type) [Group H] [Finite H] (I D P Y : Subgroup H) (p d : ℕ),
      ThreeTenHyp I D P Y p d → IsSLType 3 (ZMod p) ↥I → ThreeTenSL3Data I D Y p d) :
    ThreeTenCase1 := by
  intro H _ _ I D P Y p d hhyp hcase
  obtain ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩ := hhyp
  have hhyp' : ThreeTenHyp I D P Y p d :=
    ⟨hp, hp2, hd, hd2, hdp, hI, hD, hDne, hP, hYlt, hγ, hN⟩
  rcases hcase with h2 | h2 | h3
  · exact (hv H I D P Y p d hhyp' (Or.inl h2)).elim
  · exact (hv H I D P Y p d hhyp' (Or.inr h2)).elim
  · obtain ⟨hDle, hcyc, htor, hYmax⟩ := hs H I D P Y p d hhyp' h3
    exact threeTenConcl_of_isSL3_data hp hd hdp h3 hDle hcyc hDne hD.isPGroup htor hYmax

end CFSG.LocalAnalysis.AGL81I.Section3
