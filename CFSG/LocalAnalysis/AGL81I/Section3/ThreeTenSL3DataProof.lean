module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenSL3Cyclic

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open Matrix
open CFSG.GH74.GLS.Stage2.Signalizer

open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {H : Type} [Group H] [Finite H]

theorem threeTenSL3Data_of_torusExclusion {I D P Y : Subgroup H} {p d : ℕ} [Fact p.Prime]
    (hhyp : ThreeTenHyp I D P Y p d)
    (e : ↥I ≃* SpecialLinearGroup (Fin 3) (ZMod p))
    (htor : ThreeTenTorusExclusion p d) :
    ThreeTenSL3Data I D Y p d := by
  have hh : ThreeTenHyp I D P Y p d := hhyp
  obtain ⟨hp, _hp2, hd, hd2, hdp, _hI, hDsyl, hDne, _hPsyl, _hY, _hγ, _hN⟩ := hhyp
  haveI : Fact d.Prime := ⟨hd⟩
  have hSL3 : IsSLType 3 (ZMod p) ↥I := ⟨e⟩
  have hDI : D ≤ I := d_le_I_of_threeTenHyp_of_isSLType hh e htor
  have hDpg : IsPGroup d D := hDsyl.isPGroup
  have hdvd : d ∣ p + 1 := dvd_p_add_one_of_isSL3 hp hd hdp hSL3 hDI hDne hDpg htor
  have hDsylI : CFSG.ABGLocalTools.IsSylowOf d D I := hDsyl.of_le hDI le_top
  have hcyc : IsCyclic ↥D :=
    isCyclic_of_isSylow_dvd_p_add_one_of_prime_ne_two hp hd hd2 hdp hdvd e hDsylI
  have hmp : IsMaxParabolicP p I Y :=
    isMaxParabolicP_of_threeTenHyp_of_isSLType_of_torusExclusion hh e htor
  exact ⟨hDI, hcyc, htor, hmp⟩

end CFSG.LocalAnalysis.AGL81I.Section3
