module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146F20
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146P10
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146P13
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zKUK
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S146zMDec
public import CFSG.Quasithin.EmptyFaithful.S146P17
public import CFSG.Quasithin.EmptyFaithful.S146P20
public import CFSG.Quasithin.EmptyFaithful.S146zMSolv
public import CFSG.Quasithin.EmptyFaithful.SBc14Call
public import CFSG.Quasithin.EmptyFaithful.SBc17FixG2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc17

@[expose] def Input14615ContraOuterFix_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
            HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
              CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                  CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                    ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → ¬ K₁ ≤ J → False

theorem input14615ContraOuterP_of_Fix_F4 (h5 : Stage1461Five) (iFix : Input14615FixR)
    (iO : Input14615ContraOuterFix_F4) : Input14615ContraOuterP_F4 := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ J hJc hJq hJle hJK hJ5 hK
  obtain ⟨hHyp, hchar, hPcore⟩ := SBc14.callSite_facts h5 S hred hmax hdec hctx hset hG₂
  exact iO G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
    (gap3Fix_of_ctx iFix S hred hmax hdec hctx hset) hHyp hchar hPcore J hJc hJq hJle hJK hJ5 hK

@[expose] def Input14615ContraInnerFix_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDecP T M H p H₀ H₁ H₂ t → Ctx15 T M H p H₁ →
        ∀ (K₁ K₂ : Subgroup G) (s : G), Setup14615 T M H H₁ H₂ K₁ K₂ s →
          ¬ g2_14615 K₂ ≤ mcOf T → Gap3Fix T K₁ K₂ →
            HypC23 (g2_14615 K₂) (pCoreOf 2 (mcOf T)) (g12_14615 T K₂) →
              CharTwo (g2_14615 K₂) → pCoreOf 2 (g2_14615 K₂) ≤ g12_14615 T K₂ →
                ∀ J : Subgroup G, J ∈ cComp (g2_14615 K₂) →
                  CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) → ¬ J ≤ g12_14615 T K₂ →
                    ⁅J, K₁⁆ = J → pRank 5 J ≤ 1 → K₁ ≤ J → False

theorem input14615ContraInnerP_of_Fix_F4 (h5 : Stage1461Five) (iFix : Input14615FixR)
    (iI : Input14615ContraInnerFix_F4) : Input14615ContraInnerP_F4 := by
  intro G _ _ T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂ J hJc hJq hJle hJK hJ5 hK
  obtain ⟨hHyp, hchar, hPcore⟩ := SBc14.callSite_facts h5 S hred hmax hdec hctx hset hG₂
  exact iI G T M S H PQ p hred hmax H₀ H₁ H₂ t hdec hctx K₁ K₂ s hset hG₂
    (gap3Fix_of_ctx iFix S hred hmax hdec hctx hset) hHyp hchar hPcore J hJc hJq hJle hJK hJ5 hK

end SBc17

theorem stages14613_to_14617_of_SBc17_noUK_F4
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP_F4) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14a : Input14614Solv) (i14b : Input14614Sol_F4) (i14c : Input14614Shape_F4)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iO : SBc17.Input14615ContraOuterFix_F4) (iI : SBc17.Input14615ContraInnerFix_F4)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP_F4 ∧ Stage14614_F4 ∧ Stage14615_F4 ∧ Stage14616_F4 ∧ Stage14617_F4 := by
  have h13 : Stage14613LabP_F4 := stage14613LabP_of_inputs_F4 iA iB1 iB2
  have h14 : Stage14614_F4 := stage14614_of_named_inputs_F4 i14a i14b i14c
  have iH : Input14615HypP := SBc14.input14615HypP_proved h5
  have iTheta : SBc14.Input14615Theta := SBc17.input14615Theta_of_FixR iFix
  have h15 : Stage14615_F4 := stage14615_of_fine_inputsPM4_F4 h12 h13 h14
    (input14615SetupP_of_four iSF) (SBc14.input14615GP_of_theta iTheta) iH
    (input14615A3P_proved iH (input14615KzP_proved h5)) (SBc14.input14615JP_proved h5 h36 h38)
    (SBc17.input14615ContraOuterP_of_Fix_F4 h5 iFix iO)
    (SBc17.input14615ContraInnerP_of_Fix_F4 h5 iFix iI)
  have h16 : Stage14616_F4 := stage14616_of_named_inputs_v2_F4 h14 h15 iWeak input14616One_proved
  have iFs : Input14617Fstar := input14617Fstar_of_K iF
  exact ⟨h13, h14, h15, h16, stage14617_of_named_inputs_PM_F4 h2 h5 h12 (stage14613Lab_of_P_F4 h13)
    h14 h15 h16 h4 input14617Mod_proved iFs
    (input14617UK_of_stages_F4 h5 h14 h16 h4 input14617Mod_proved iFs)⟩

theorem stages14613_to_14617_of_SBc17_noUK_solDec_F4
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP_F4) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape_F4)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iO : SBc17.Input14615ContraOuterFix_F4) (iI : SBc17.Input14615ContraInnerFix_F4)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP_F4 ∧ Stage14614_F4 ∧ Stage14615_F4 ∧ Stage14616_F4 ∧ Stage14617_F4 :=
  stages14613_to_14617_of_SBc17_noUK_F4 h2 h5 h12 h4 h36 h38 iA iB1 iB2 input14614Solv_proved
    (input14614Sol_of_dec_F4 h12 i14b) i14c iSF iFix iO iI iWeak iF

end CFSG.Quasithin
