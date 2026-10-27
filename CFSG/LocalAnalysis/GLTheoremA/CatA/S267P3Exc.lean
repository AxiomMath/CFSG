module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ExcLift
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.ExcRankCarrier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.ExcRank

theorem p3At_F4
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.F4 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨φ, hinj, hcomm⟩ := f4_commuting_SL2 Q hv
  exact H.false_of_commuting_SL2_fixedField e hchar φ hinj hcomm

theorem p3At_E6
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨φ, hinj, hcomm⟩ := e6_commuting_SL2' Q hv
  exact H.false_of_commuting_SL2_fixedField e hchar φ hinj hcomm

theorem p3At_twistedE6
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedE6 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨φ, hinj, hcomm⟩ := twistedE6_commuting_SL2' Q hv
  exact H.false_of_commuting_SL2_fixedField e hchar φ hinj hcomm

theorem p3At_E7
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E7 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨φ, hinj, hcomm⟩ := e7_commuting_SL2' Q hv
  exact H.false_of_commuting_SL2_fixedField e hchar (fun i => φ i.castSucc) (fun i => hinj _)
    (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B)

theorem p3At_E8
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E8 Q).Valid) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exfalso
  obtain ⟨φ, hinj, hcomm⟩ := e8_commuting_SL2 Q hv
  exact H.false_of_commuting_SL2_fixedField e hchar (fun i => φ i.castSucc) (fun i => hinj _)
    (fun i j hij A B => hcomm _ _ (fun h => hij (Fin.castSucc_injective 4 h)) A B)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
