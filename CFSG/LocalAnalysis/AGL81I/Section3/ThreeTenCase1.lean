module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeTenBasics
public import CFSG.LocalAnalysis.AGL81I.Section3.SL3Arith

public section
namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
open CFSG.GH74.GLS.Stage2.Signalizer (IsMaxParabolicP)

variable {H : Type} [Group H] [Finite H]

theorem threeTenConcl_of_isSL3_data {I D Y : Subgroup H} {p d : ℕ}
    (hp : p.Prime) (hd : d.Prime) (hdp : d ≠ p)
    (hSL3 : IsSLType 3 (ZMod p) ↥I) (hDle : D ≤ I) (hDcyc : IsCyclic ↥D) (hDne : D ≠ ⊥)
    (hDpg : IsPGroup d D) (htor : ThreeTenTorusExclusion p d)
    (hY : IsMaxParabolicP p I Y) : ThreeTenConcl I D Y p d :=
  ⟨hDcyc, hDle, hSL3, dvd_p_add_one_of_isSL3 hp hd hdp hSL3 hDle hDne hDpg htor, hY⟩

end CFSG.LocalAnalysis.AGL81I.Section3
