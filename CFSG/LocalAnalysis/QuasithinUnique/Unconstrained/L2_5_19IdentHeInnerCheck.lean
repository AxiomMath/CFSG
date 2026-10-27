module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayer
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.ClassCount
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayer
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import CFSG.Sporadic.HeldB.ClassCount
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentHeInnerCheckInputs
public import Certificates.Certificate4148

public section

namespace CFSG.QuasithinUnique.Id2519.HeInner

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native
open CFSG.QuasithinUnique.Id2519.MathNoLayer

theorem heP105_big :
    incListOK 8330 105 heDeltaP = true ∧
    ∀ j < 9, permChk 105 (heSigmaP.getD j #[]) = true ∧
      agreeOK 105 (heInnerC0 j) heDeltaP (heSigmaP.getD j #[]) = true :=
  Certificates.certificate4148.1

theorem heXp_check :
    heXp.check = true ∧ heXp.orderCertificate = 40320 :=
  Certificates.certificate4148.2.1

theorem heDp_check :
    heDp.check = true ∧ heDp.orderCertificate = 20160 :=
  Certificates.certificate4148.2.2.1

theorem heDp_gens_check :
    (∀ k < 5, permChk 105 (heDpGens.getD k #[]) = true) ∧ heDpGens.length = 5 ∧
      heSigmaP.length = 9 :=
  Certificates.certificate4148.2.2.2.1

theorem heDp_rel :
    (∀ k < 5, heXp.sift (heDpPerm k) 0 = true) ∧
    (∀ i < 9, ∀ k < 5,
      heDp.sift (heSigmaPerm i * heDpPerm k * (heSigmaPerm i)⁻¹) 0 = true) ∧
    (∀ i < 9, ∀ k < 5,
      heDp.sift ((heSigmaPerm i)⁻¹ * heDpPerm k * heSigmaPerm i) 0 = true) ∧
    (∀ i < 9, ∀ j < 9,
      heDp.sift (heSigmaPerm i * heSigmaPerm j * (heSigmaPerm i)⁻¹ * (heSigmaPerm j)⁻¹) 0 =
        true) :=
  Certificates.certificate4148.2.2.2.2.1

open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.PSL3Four in
theorem heDp_classes :
    (∀ j < 5, heDp.sift (permOrId 105 heDGens[j]!) 0 = true) ∧
    ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes heDOrbits ∧
    (∀ j < heDGens.size, TabRep heDGens[j]! (permOrId 105 heDGens[j]!)) ∧
    heDEnum.tabs.size = 20160 :=
  Certificates.certificate4148.2.2.2.2.2.1

theorem he1_noLayer_check :
    noLayerOK 42 (heToTabs he1E) (allTables heX1) = true :=
  Certificates.certificate4148.2.2.2.2.2.2

end CFSG.QuasithinUnique.Id2519.HeInner
