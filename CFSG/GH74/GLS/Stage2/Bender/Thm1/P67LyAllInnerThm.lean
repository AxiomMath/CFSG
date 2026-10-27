module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyOutRigid
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Ly
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultThreeAux
public import CFSG.Sporadic.Recognition.LyonsLocalPerfect
public import CFSG.Sporadic.Recognition.LyonsAmalgamExtOutMcL
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyGenCert

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut

open Subgroup CFSG CFSG.Blueprint CFSG.Sporadic.LySchreier CFSG.GH74.GLS.Stage12
  CFSG.Sporadic.Recognition.LyonsSims

theorem lyAllInner_thm :
    LyAllInner := by
  intro Y _ hLy α
  obtain ⟨eT⟩ := hLy
  have hcard : Nat.card Y = 51765179004000000 := by
    rw [Nat.card_congr eT.toEquiv]
    exact CFSG.Sporadic.Ly.card_Ly
  have hfin : Finite Y := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨t, ρ, D⟩ :=
    exists_lyData_of_oneClassDoubleCover (LyMult.oneClassDoubleCover_of_ly ⟨eT⟩)
  obtain ⟨x₁, x₂, x₃, S⟩ := D.exists_lyStd
  have hperfM := D.isPerfect_centralizer S
  have hcenM := D.center_centralizer S
  obtain ⟨eM⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  have e : ↥(centralizer ({(x₁ : Y)} : Set Y)) ⧸ center ↥(centralizer ({(x₁ : Y)} : Set Y)) ≃*
      NativeSporadic.McL := (QuotientGroup.quotientMulEquivOfEq hcenM).trans eM
  have hAut := card_mulAut_le_of_centerQuot_mcl e
  have hgenY := LyGen.sup_eq_top_of_ly eT D S.pow₁ S.rho₁
  exact allInner_of_rigid t D.order_t (fun u hu => isConj_iff.mp (D.one_class t u D.order_t hu))
    ρ (fun σ => by rw [D.cover.range_eq]) D.cover.ker_eq D.cover.perfect x₁ S.pow₁ S.rho₁
    (fun a b ha hb h => D.cover.eq_of_rho_eq_of_pow_three ha hb h) hAut hgenY α

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyOut
