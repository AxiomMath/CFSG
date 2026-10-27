module

public import CFSG.ClassicalInvolution.RouteD.TWS6SignModels
public import CFSG.ClassicalInvolution.RouteD.TWDConfig
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Witness

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {tY : StatedLieTag} {nY : ℕ} {N : Subgroup G} {x : G}

theorem sign_config' (cx : TCtx p f tY nY Ω N x)
    (hF : SignFacts (fundamentalSubgroups tY (modelUniv tY nY p f Fact.out).D) (GaloisField p f))
    {a b d : Subgroup G} {wa wb wd : G} (ha : a ∈ centralizingMembers Ω {x})
    (hb : b ∈ centralizingMembers Ω {x}) (hd : d ∈ centralizingMembers Ω {x})
    (hwa : IsClassicalMember p f a wa) (hwb : IsClassicalMember p f b wb)
    (hwd : IsClassicalMember p f d wd) (hab : a ≠ b) (hbd : b ≠ d)
    (hpair : ∃ W, LinearBlockStandardPair (GaloisField p f) W a b) (hnbd : ¬ Commutes b d)
    (had : Commutes a d) (hcab : Commute wa wb) (hcdb : Commute wd wb)
    (hna : conjSub wb a = a) (hnd : conjSub wb d = d) :
    ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField p f) W b d := by
  obtain ⟨W, hW⟩ := hpair
  have hnab : ¬ Commutes a b := not_commutes_of_linearBlockStandardPair hW
  have haL : IsLayerMember cx a := IsLayerMember.of_not_commutes cx ha hb hab hnab
  have hbL : IsLayerMember cx b :=
    IsLayerMember.of_not_commutes cx hb hd hbd hnbd
  have hdL : IsLayerMember cx d := IsLayerMember.of_not_commutes cx hd hb hbd.symm
    (fun h => hnbd (commutes_symm h))
  obtain ⟨Ra, hRa, haR⟩ := haL.exists_fund
  obtain ⟨Rb, hRb, hbR⟩ := hbL.exists_fund
  obtain ⟨Rd, hRd, hdR⟩ := hdL.exists_fund
  have hadjab : ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Ra Rb :=
    modelAdj_of_adj cx ha hb hRa hRb haR hbR hwa hwb hab hnab hcab hna
  have hadjdb : ModelAdj (Subgroup.center (modelUniv tY nY p f Fact.out).K) Rd Rb :=
    modelAdj_of_adj cx hd hb hRd hRb hdR hbR hwd hwb hbd.symm
      (fun h => hnbd (commutes_symm h)) hcdb hnd
  have hcom : Commutes Ra Rd := (cx.commutes_iff_fund ha hd hRa haR hdR).mp had
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members cx.hP1 ha hb hW
  rw [haR, hbR] at hW'
  have hlift := hF.lift cx.d.ψ cx.d.ker_le Ra hRa Rb hRb ⟨W', hW'⟩
  obtain ⟨W₂, hW₂⟩ := hF.sign Ra hRa Rb hRb Rd hRd hadjab hadjdb hcom hlift
  exact cx.stdPair_of_fund hb hd hW₂ hbR hdR

end Witness

end CFSG.ClassicalInvolution.RouteD.TWS6
