module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPSyl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPFieldsA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPFieldsB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPOnly
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPRankM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84FPYEx
public import Certificates.Certificate442349

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.Asc82NormA6 (Facts)

theorem sec8t84_model_facts (F : Facts) (G : Certificates.T84P.Facts) :
    IsSylow2Of (sec8t84FPP0 F G) ⊤ ∧
      Sec8T84PFacts (Sec8T84FPM0 F) (Sec8T84FPV0 F) (sec8t84FPP0 F G) (sec8t84FPF0 F G) := by
  have honly := sec8t84FPonly F G
  have h32 := sec8t84_no32_of_only honly (sec8t84FPJ_card F G)
  obtain ⟨y, hy3, hyN, hyC, s, hsP, hsJ, hs2, hsy, hPs⟩ := sec8t84FPy_exists F G
  rw [← sec8t84FPJ_eq F G] at hyN hyC hsJ hPs
  exact ⟨sec8t84FPP0_sylow F G,
    { E_le := sec8t84FPV0_le_P0 F G
      F_le := sec8t84FPF0_le_P0 F G
      F_e16 := sec8t84FPF0_e16 F G
      F_ne := sec8t84FPF0_ne F G
      F_norm := sec8t84FPF0_norm F G
      only := honly
      no32 := h32
      J_card := sec8t84FPJ_card F G
      EF_card := sec8t84FPEF_card F G
      rank_cent := sec8t84_rank_cent (sec8t84FPP0_sylow F G) h32 (sec8t84FPrank_wit F G)
      cent_E := sec8t84FPcent_V F G
      cent_F := sec8t84FPcent_F F G
      y_exists := ⟨y, hy3, hyN, hyC, s, hsP, hsJ, hs2, hsy, hPs⟩ }⟩

theorem sec8t84_factP_of_facts (G : Certificates.T84P.Facts) :
    Sec8T84FactP := by
  intro Y _ _ E H P hE hEn hH hEH hEH' htr hP
  haveI := hEn
  obtain ⟨Θ, hΘ⟩ := sec8t84_iso_model hE hH hEH hEH' htr
  obtain ⟨hP₀, hF⟩ := sec8t84_model_facts Certificates.certificate442267 G
  exact sec8t84_facts_transfer Θ hΘ hP hP₀ hF

theorem sec8t84_factP_of :
    Sec8T84FactP :=
  sec8t84_factP_of_facts Certificates.certificate442349

end CFSG.OddStandard.SmallF3.Omega
