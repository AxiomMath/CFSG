module

public import CFSG.Quasithin.EmptyFaithful.SBc17Inn4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.SBc17N

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

namespace SBc17

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem inner_facts_F4 (hC27 : ASC27Statement_F4 G) {H R M J : Subgroup G} (hyp : HypC23 H R M)
    (hJc : J ∈ cComp H) (hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)) (hH : CharTwo H)
    (hJM : ¬ J ≤ M) (hR : R ≤ Subgroup.normalizer (J : Set G)) :
    J ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) ∧
      J ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) ≤ oTwoZIn J ∧
        pCoreOf 2 J ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (J ⊔ R)) : Set G) := by
  have hcJ : CharTwo J := charTwo_of_mem_cComp hH hJc
  have h1 := (hC27 H R M J (omegaOneCenterOf (pCoreOf 2 (J ⊔ R))) hyp hJc hq hcJ hJM hR rfl).1
  exact ⟨le_normalizer_V J R, inf_centralizer_le_oTwoZIn h1.2.1, fun x hx =>
    (h1.1 (pCoreOf_le_pCoreOf_sup hR hx)).2⟩

end SBc17

theorem stages14613_to_14617_of_SBc17F_cert_noUK_solDec_F4
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G)
    (h2 : Stage1461Two) (h5 : Stage1461Five) (h12 : Stage14612PartP_F4) (h4 : Stage1463Four)
    (h36 : A36ForSQTK) (h38 : A38ForSQTK)
    (iA : Input14613AP) (iB1 : Input14613B1P) (iB2 : Input14613B2P)
    (i14b : Input14614SolDec) (i14c : Input14614Shape_F4)
    (iSF : Input14615SetupFourP) (iFix : SBc17.Input14615FixR)
    (iOD : SBc17.Input14615ContraOuterD) (iIE : SBc17.Input14615ContraInnerE)
    (iWeak : Input14616Weak) (iF : Input14617FstarK) :
    Stage14613LabP_F4 ∧ Stage14614_F4 ∧ Stage14615_F4 ∧ Stage14616_F4 ∧ Stage14617_F4 :=
  have hN := SBc17.input14615ContraN_of_B h36
    (SBc17.input14615ContraOuterB_of_C h36 (SBc17.input14615ContraOuterC_of_D SBc17.factOut5U33 iOD))
    (SBc17.input14615ContraInnerB_of_D (SBc17.input14615ContraInnerD_of_E iIE))
  stages14613_to_14617_of_SBc17N_noUK_solDec_F4 hC27 h2 h5 h12 h4 h36 h38 iA iB1 iB2 i14b i14c iSF iFix
    hN.1 hN.2 iWeak iF

end CFSG.Quasithin
