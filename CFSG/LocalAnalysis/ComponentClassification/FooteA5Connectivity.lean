module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.LocalAnalysis.ComponentClassification.Sol76StrongEmb
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.OddQuotientProduct

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.Sol76

variable {Y : Type} [Group Y] [Finite Y]

theorem not_isTwoDisconnected_of_oddKer_alt5_prod
    {Z : Type*} [Group Z] (f : Y →* alternatingGroup (Fin 5) × Z)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    {B : Subgroup Z} (hB : IsKleinFour B) :
    ¬ FooteLit.IsTwoDisconnected Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 Y) := inferInstance
  obtain ⟨PA⟩ : Nonempty (Sylow 2 (alternatingGroup (Fin 5))) := inferInstance
  obtain ⟨V, hV, _hVT, hVC⟩ :=
    CFSG.ProperTwoGeneratedCore.exists_central_isKleinFour_of_oddKer_alt5_prod f hf hker T
  refine not_isTwoDisconnected_of_gamma_eq_top T ?_ ?_
  · intro E F hE hET hF hFT
    have hEV : CommFourAdj Y E V := ⟨hE, hV, fun e he =>
      Subgroup.mem_centralizer_iff.mpr fun v hv =>
        ((Subgroup.mem_centralizer_iff.mp (hVC hv)) e (hET he)).symm⟩
    have hVF : CommFourAdj Y V F := ⟨hV, hF, fun v hv =>
      Subgroup.mem_centralizer_iff.mpr fun f hf =>
        (Subgroup.mem_centralizer_iff.mp (hVC hv)) f (hFT hf)⟩
    exact (Relation.ReflTransGen.single hEV).tail hVF
  · exact CFSG.ProperTwoGeneratedCore.properTwoGenCoreGamma_eq_top_of_oddKer_prod f hf hker
      (CFSG.Quasithin.Vol2.Ch11.O5.isKleinFour_sylow_two_alt5 PA) hB T

theorem not_isTwoDisconnected_of_oddKer_alt5_prod_of_twoRank
    {Z : Type} [Group Z] [Finite Z] (f : Y →* alternatingGroup (Fin 5) × Z)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker))
    (hZ : 2 ≤ CFSG.Open.twoRank Z) : ¬ FooteLit.IsTwoDisconnected Y := by
  have hpRank : 2 ≤ CFSG.pRank 2 Z := by
    simpa only [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.Open.twoRank] using hZ
  obtain ⟨B, hB⟩ := CFSG.ComponentClassification.Sol76.exists_isKleinFour_of_two_le_pRank hpRank
  exact not_isTwoDisconnected_of_oddKer_alt5_prod f hf hker hB

end CFSG.ComponentClassification.Sol76.Sig
