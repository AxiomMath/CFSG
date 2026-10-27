module

public import CFSG.ClassicalInvolution.Q3.Q3PPWireAll
public import CFSG.ClassicalInvolution.Q3.Q3PPFundG2D4
public import CFSG.ClassicalInvolution.Q3.Q3TIYTPShape
public import CFSG.ClassicalInvolution.Q3.Q3OFUnique
public import CFSG.ClassicalInvolution.Q3.Q3OFProd
public import CFSG.ClassicalInvolution.Q3.Q3TIYTPMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3NM
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt TwinElt TwinElt.u)

section Top

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem EdgeData.involutionOddCore_prod_eq_bot_of_alphaCore (hOA : OddAutLayerRigidHyp)
    (hR : RouteD3Setup K z) (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂)
    (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥) :
    involutionOddCore (z₁ * z₂) = ⊥ := by
  have hP₁ : involutionOddCore z₁ = ⊥ := involutionOddCore_eq_bot_of_member hR h.mem₁ h.cls₁
  have hP₂ : involutionOddCore z₂ = ⊥ := involutionOddCore_eq_bot_of_member hR h.mem₂ h.cls₂
  have hcomm : ∀ p ∈ involutionOddCore (z₁ * z₂), z₁ * p = p * z₁ :=
    (alphaCore_edge_eq_bot_iff h.sq₁ h.sq₂ h.mul_comm₁₂ h.cls₁.ne_one h.cls₂.ne_one h.ne hP₁
      hP₂).mp hα
  refine (Subgroup.eq_bot_iff_forall _).mpr fun p hp => ?_
  have hpV : p ∈ involutionOddCore (z₁ * z₂) ⊓ Subgroup.centralizer ({z₁} : Set G) :=
    ⟨hp, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm p hp).symm⟩
  rw [h.oddCore_inf_centralizer_eq_bot hOA hR hnab] at hpV
  exact Subgroup.mem_bot.mp hpV

theorem twinP1R3Central3_of_edgesAtSetup (hE : AlphaCent3EdgesAtSetup) :
    Q3TIY.TwinP1R3Central3 := by
  intro G _ _ _ K z hR T hTΩ hTK clsT hKT u hu
  obtain ⟨-, huKT, hu2, huK, huT⟩ := hu
  have h3 : OddThreeFreeInput := oddThreeFreeInput_proved
  have hnab := routeD3Setup_nonabelian hR
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le hR.cls.subnormal⟩
  have hTz : T ∈ centralizingMembers (conjClass3 K) {z} := ⟨hTΩ, isSubnormal_le clsT.subnormal⟩
  have hKiso := Q3TIY.isolated_of_involution_eq h3 hR hKz hR.cls
  have hTiso := Q3TIY.isolated_of_involution_eq h3 hR hTz clsT
  have htwin : IsTwinAt (conjClass3 K) K T z :=
    ⟨hTz, hTK, fun N hN hNT => hTiso N hN hNT, fun N hN hNK => hKiso N hN hNK⟩
  obtain ⟨e, he⟩ := Q3TIY.exists_twinElt_of_productElt hR.cls clsT (hR.setup.1 K hKΩ) hKT huKT
    hu2 huK huT
  obtain ⟨J, hJ, t, clsJ, htz⟩ := Q3TIY.exists_member_involution_ne hR
  have hJK : J ≠ K := fun h => htz (involution_unique3 clsJ (h ▸ hR.cls))
  have hJT : J ≠ T := fun h => htz (involution_unique3 clsJ (h ▸ clsT))
  have hedge : EdgeData K K J z t := ⟨hKΩ, hJ.1, hR.cls, clsJ, htz.symm, hKiso J hJ hJK⟩
  rw [← he]
  exact Q3TIY.twin_P1_R3_of_edge ⟨hR, htwin, clsT⟩ e hJ hJK hJT clsJ htz
    (hE G K z hR hnab K J z t hedge)

theorem commutingProductP1Input3_of_edgesAtSetup (hE : AlphaCent3EdgesAtSetup)
    (hOA : OddAutLayerRigidHyp) : Q3TY.CommutingProductP1Input3 := by
  intro G _ _ _ K z hR M hM hKM x hxKM hx2 hxK hxM
  have hx : IsProductElt3 K M x := ⟨hKM, hxKM, hx2, hxK, hxM⟩
  obtain ⟨w, hw⟩ := hR.inClass.classical M hM
  by_cases hzw : z = w
  · rw [← hzw] at hw
    have hMK : M ≠ K := by
      intro h
      rw [h] at hw hKM
      exact not_commutes_self3 hw hKM
    exact twinP1R3Central3_of_edgesAtSetup hE G K z hR M hM hMK hw hKM x hx
  · have hnab := routeD3Setup_nonabelian hR
    have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
    have hxz : x = z * w := eq_mul_of_isProductElt hR.cls hw (hR.setup.1 K hKΩ) hzw hx
    have he : EdgeData K K M z w := ⟨hKΩ, hM, hR.cls, hw, hzw, hKM⟩
    have hP : involutionOddCore x = ⊥ := by
      rw [hxz]
      exact he.involutionOddCore_prod_eq_bot_of_alphaCore hOA hR hnab
        (hE G K z hR hnab K M z w he)
    exact ⟨localOddCentral3_of_involutionOddCore_eq_bot hR.inClass.conjInvariant hP,
      Q3TIY.localOddThreeFree3_of_involutionOddCore_eq_bot hR.inClass.conjInvariant hP⟩

theorem mfComp_g2 : MFComp (CompData.model .G2 0) := Or.inr fixedOddFreeFund_g2

theorem mfComp_trialityD4 : MFComp (CompData.model .trialityD4 0) :=
  Or.inr fixedOddFreeFund_trialityD4

end Top

end CFSG.ClassicalInvolution.Q3.Q3PP
