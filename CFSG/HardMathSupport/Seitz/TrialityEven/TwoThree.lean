module

public import CFSG.HardMathSupport.Seitz.TrialityEven.Split
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoPlane
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
import CFSG.Quasithin.Recognition.CertD4Bridge
import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw

public section

namespace CFSG.HardMathSupport.Seitz.TrialityEven

open TauCeti CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.AGLEmbedding.D4Two
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP

theorem exists_equiv_trialityGroup8
    {q : PrimePower} (hq : q.p = 2) (hq1 : q.exponent = 1)
    (hv : (LieTypeIndex.trialityD4 q).Valid) :
    ∃ _ : Cat ⟨.trialityD4 q, hv⟩ ≃* trialityGroup8, Nat.card trialityGroup8 = 211341312 := by
  have hcard := card_catGroup_trialityD4_even (d := ⟨LieTypeIndex.trialityD4 q, hv⟩) hq rfl
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq, hq1] at hm
  rw [hq1] at hcard
  have hL : CFSG.Blueprint.LieModel (CatGroup ⟨LieTypeIndex.trialityD4 q, hv⟩)
      .trialityD4 0 2 1 := CFSG.RankThree.PartOne.Sec66T.lieModel_trialityD4_iff.mpr ⟨rfl, hm⟩
  obtain ⟨e2⟩ := trialityD4ModelBridge_of_lieModel _ hL
  have hk8 : Nat.card GF8 = 8 := by rw [Nat.card_eq_fintype_card]; rfl
  obtain ⟨e3⟩ := d4bG8_equiv_quasithin GF8 hk8
  let φ : Cat ⟨.trialityD4 q, hv⟩ ≃* trialityGroup8 := e2.trans e3.symm
  refine ⟨φ, ?_⟩
  rw [← Nat.card_congr φ.toEquiv, hcard]
  norm_num [ordTrialityD4]

theorem trialityTwoThreePlanes_holds :
    TrialityTwoThreePlanes := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, -, ⟨hp3, q, hdq, hq, hq1⟩, -, -⟩
  simp only at hdq hp3 hin
  subst hdq hp3
  obtain ⟨φ, hG⟩ := exists_equiv_trialityGroup8 hq hq1 hv
  have hfs := finite_isSimpleGroup_cat_trialityD4 hv
  haveI : Finite (Cat ⟨.trialityD4 q, hv⟩) := hfs.1
  haveI : IsSimpleGroup (Cat ⟨.trialityD4 q, hv⟩) := hfs.2
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hel : IsElementaryAbelian 3 ↥E := isElementaryAbelian_of_isElemAbelian hE
  rw [planeGen_iff_closure_fixUnion]
  refine closure_fixUnion_eq_top_of_inner_equiv
    (exists_noncommuting_of_isElementaryAbelian_aut hel hc) φ ?_ E hc
    (fun ψ hψ => (hin hψ).imp fun g hg => hg.symm)
  intro E₁ hE₁ hE₁c
  exact closure_centralizers_trialityGroup8 hG E₁
    ⟨hE₁.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ hE₁c

end CFSG.HardMathSupport.Seitz.TrialityEven
