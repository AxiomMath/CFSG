module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGood
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.Enumeration
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24Data
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporGood
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public meta import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24CheckInputs
public import Certificates.Certificate4094
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public meta import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public meta import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public meta import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Structure318Red
public meta import CFSG.Quasithin.Background.A3Structure36A
public meta import CFSG.Quasithin.Background.A3Structure36BAction
public meta import CFSG.Quasithin.Background.A3Structure36BBase
public meta import CFSG.Quasithin.Background.A3Structure36BCase3Base
public meta import CFSG.Quasithin.Background.A3Structure36BCasesBase
public meta import CFSG.Quasithin.Background.A3Structure36BCommonBase
public meta import CFSG.Quasithin.Background.A3Structure36BFrattini
public meta import CFSG.Quasithin.Background.A3Structure36BHeisBase
public meta import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public meta import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public meta import CFSG.Quasithin.Background.A3Structure36BStarBase
public meta import CFSG.Quasithin.Background.A3Structure36Base
public meta import CFSG.Quasithin.Background.A3Structure37Base
public meta import CFSG.Quasithin.Background.A3Structure37Comm
public meta import CFSG.Quasithin.Background.A3Structure37Frattini
public meta import CFSG.Quasithin.Background.A3Structure37KeyBase
public meta import CFSG.Quasithin.Background.A3Structure37Schur
public meta import CFSG.Quasithin.Background.A3Structure38Part3
public meta import CFSG.Quasithin.Background.B1MoreElevenE
public meta import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public meta import CFSG.Quasithin.Background.B4ModelsAction
public meta import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B4ModelsIso
public meta import CFSG.Quasithin.Background.C2Basic
public meta import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.C2Inputs
public meta import CFSG.Quasithin.Background.E1
public meta import CFSG.Quasithin.Background.E1Sec4
public meta import CFSG.Quasithin.Background.E1Sec5
public meta import CFSG.Quasithin.Background.E1Sec8
public meta import CFSG.Quasithin.Background.E1Solv
public meta import CFSG.Quasithin.Background.E1Twelve
public meta import CFSG.Quasithin.Background.E3Cent
public meta import CFSG.Quasithin.Vol2.Ch1Local
public meta import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public meta import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public meta import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs

open scoped Pointwise
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

theorem enc_injective : Function.Injective enc := fun x y h =>
  Subtype.ext (encPerm_injective (by norm_num) h)

theorem tabX_eq (x : X24) : tabX x = x := Subtype.ext (tab_eq x.1)

theorem s0_facts : S0X.length = 1024 ∧
    strictAsc ((S0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧ (1 : X24) ∈ S0X ∧
    (∀ x ∈ S0X, ∀ g ∈ s0gen, enc (x * g) ∈ S0X.map enc) ∧ (∀ x ∈ S0X, x ^ (2 ^ 10) = 1) :=
  Certificates.certificate4094.1

theorem a_facts :
    A1X.length = 2 ∧ Z2X.length = 8 ∧ A2X.length = 256 ∧
    (∀ a ∈ a2gen, enc a ∈ A2X.map enc) ∧ (∀ y ∈ A2X, enc y ∈ A2cl.map enc) :=
  Certificates.certificate4094.2.1

theorem k1_facts : K1X.length = 21504 ∧
    strictAsc ((K1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K1X, enc (x * zX * x⁻¹) = enc zX) ∧
    (∀ x ∈ K1X, ∀ a ∈ A1X, enc (x * a * x⁻¹) ∈ A1X.map enc ∧ enc (x⁻¹ * a * x) ∈ A1X.map enc) ∧
    zX ≠ 1 ∧ (∀ a ∈ A1X, enc a = enc 1 ∨ enc a = enc zX) ∧ enc zX ∈ A1X.map enc :=
  Certificates.certificate4094.2.2.1

theorem class_facts :
    Reach gensC zX classRes.1 classRes.2.1 classRes.2.2 ∧
    classRes.1.length = 11385 ∧
    strictAsc ((classRes.1.map enc).mergeSort (fun a b => decide (a ≤ b))) = true :=
  Certificates.certificate4094.2.2.2.1

theorem trio_facts :
    Reach gensA trio trioRes.1 trioRes.2.1 trioRes.2.2 ∧
    trioRes.1.length = 3795 ∧
    strictAsc ((trioRes.1.map encTrioN).mergeSort (fun a b => decide (a ≤ b))) = true :=
  Certificates.certificate4094.2.2.2.2.1

theorem t0_facts : T0X.length = 64512 ∧
    strictAsc ((T0X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ T0X, x • trio = trio) ∧ T0N.length = 9216 :=
  Certificates.certificate4094.2.2.2.2.2.1

theorem k2_facts : K2X.length = 9216 ∧
    strictAsc ((K2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ x ∈ K2X, nrmTestGens enc (A2X.map enc) a2gen x = true) :=
  Certificates.certificate4094.2.2.2.2.2.2.1

theorem q1_facts : Q1X.length = 128 ∧
    strictAsc ((Q1X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ Q1X, enc q ∈ K1X.map enc) ∧ (1 : X24) ∈ Q1X ∧
    (∀ p ∈ Q1X, ∀ q ∈ Q1X, enc (p * q) ∈ Q1X.map enc) ∧
    (∀ k ∈ k1gen, ∀ q ∈ Q1X,
      enc (k * q * k⁻¹) ∈ Q1X.map enc ∧ enc (k⁻¹ * q * k) ∈ Q1X.map enc) ∧
    (∀ q ∈ Q1X, q ^ (2 ^ 4) = 1) ∧
    (∀ y ∈ K1X, (∀ q ∈ Q1X, enc (y * q) = enc (q * y)) → enc y ∈ Q1X.map enc) ∧
    (∀ b ∈ K1X, b ≠ 1 → b ^ 3 = 1 →
      4 < ((Q1X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
    K1X.length / Q1X.length = 168 :=
  Certificates.certificate4094.2.2.2.2.2.2.2.1

theorem q2_facts :
    strictAsc ((A2X.map enc).mergeSort (fun a b => decide (a ≤ b))) = true ∧
    (∀ q ∈ A2X, enc q ∈ K2X.map enc) ∧ (1 : X24) ∈ A2X ∧
    (∀ p ∈ A2X, ∀ q ∈ A2X, enc (p * q) ∈ A2X.map enc) ∧
    (∀ k ∈ k2gen, ∀ q ∈ A2X,
      enc (k * q * k⁻¹) ∈ A2X.map enc ∧ enc (k⁻¹ * q * k) ∈ A2X.map enc) ∧
    (∀ q ∈ A2X, q ^ (2 ^ 4) = 1) ∧
    (∀ y ∈ K2X, (∀ q ∈ A2X, enc (y * q) = enc (q * y)) → enc y ∈ A2X.map enc) ∧
    (∀ b ∈ K2X, b ≠ 1 → b ^ 3 = 1 →
      4 < ((A2X.map fun q => enc (q * b * q⁻¹ * b⁻¹)).dedup).length) ∧
    K2X.length / A2X.length = 36 :=
  Certificates.certificate4094.2.2.2.2.2.2.2.2.1

theorem gen_facts :
    (jLetters.all fun g => (K1X ++ K2X).any fun x => enc x == encPerm g) = true ∧
    evalW jLetters wordA = m24gA ∧ evalW jLetters wordB = m24gB :=
  Certificates.certificate4094.2.2.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs
