module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.LieType.Chevalley.E6GraphLeviTheta
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionAbstract
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.E6.StdF4RadicalRoots
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Census.Exceptional.TwistedE6Local
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.RankThree.CentralCover
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.SeitzReduction
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private def torusExp (i : Fin Tag.E6.rank) (e : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  fun j => e j - Tag.E6.cartan i j * e i

private theorem conj_weylElt_word_rootDiagUnit {K : Type} [Field K]
    (l : List (Fin Tag.E6.rank)) (a : Fin Tag.E6.rank → Kˣ) :
    (l.map (fun i => weylElt Tag.E6 K i 1)).prod * rootDiagUnit Tag.E6 a *
      ((l.map (fun i => weylElt Tag.E6 K i 1)).prod)⁻¹ =
    rootDiagUnit Tag.E6 (l.foldr (fun i b j => b j * b i ^ (-Tag.E6.cartan i j)) a) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, List.foldr_cons]
    calc
      (weylElt Tag.E6 K i 1 * (l.map (fun i => weylElt Tag.E6 K i 1)).prod) *
          rootDiagUnit Tag.E6 a *
          (weylElt Tag.E6 K i 1 * (l.map (fun i => weylElt Tag.E6 K i 1)).prod)⁻¹
          = weylElt Tag.E6 K i 1 *
              ((l.map (fun i => weylElt Tag.E6 K i 1)).prod * rootDiagUnit Tag.E6 a *
                ((l.map (fun i => weylElt Tag.E6 K i 1)).prod)⁻¹) *
              (weylElt Tag.E6 K i 1)⁻¹ := by group
      _ = weylElt Tag.E6 K i 1 *
              rootDiagUnit Tag.E6 (List.foldr (fun i b j => b j * b i ^ (-Tag.E6.cartan i j)) a l) *
              (weylElt Tag.E6 K i 1)⁻¹ := by rw [ih]
      _ = rootDiagUnit Tag.E6 (fun j =>
              List.foldr (fun i b j => b j * b i ^ (-Tag.E6.cartan i j)) a l j *
                List.foldr (fun i b j => b j * b i ^ (-Tag.E6.cartan i j)) a l i ^
                  (-Tag.E6.cartan i j)) :=
            weylElt_conj_rootDiagUnit _ i

private theorem foldr_torusReflect_zpow {K : Type} [Field K]
    (l : List (Fin Tag.E6.rank)) (e : Fin Tag.E6.rank → ℤ) (t : Kˣ) :
    l.foldr (fun i b j => b j * b i ^ (-Tag.E6.cartan i j)) (fun j => t ^ e j) =
      fun j => t ^ (l.foldr torusExp e j) := by
  induction l generalizing e with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, ih]
    funext j
    simp only [List.foldr_cons, torusExp]
    rw [← zpow_mul, ← zpow_add]
    congr 1
    ring

private theorem te6Words_three_torusExp :
    (CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3).foldr torusExp
      (fun j => Tag.E6.cartan (3 : Fin Tag.E6.rank) j) =
      Pi.single (1 : Fin Tag.E6.rank) (1 : ℤ) := by
  decide +kernel

theorem e6Isogeny_te6SL2_three_HSL {f : ℕ} (hf : 1 ≤ f) {k : Type} [Field k]
    [Algebra k (GaloisField 2 (2 * f))]
    (hj : ∀ x, frobQ 2 f (algebraMap k (GaloisField 2 (2 * f)) x) =
      algebraMap k (GaloisField 2 (2 * f)) x) (t : kˣ) :
    ((e6Isogeny (GaloisField 2 (2 * f))
        (te6SL2 (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj 3 (HSL t)) :
        adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :
      ModGL Tag.E6 (GaloisField 2 (2 * f))) =
    (E6GraphLevi.thetaTorusHom (GaloisField 2 (2 * f))
      ((Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom) t) :
      ModGL Tag.E6 (GaloisField 2 (2 * f))) := by
  let u : (GaloisField 2 (2 * f))ˣ :=
    (Units.map (algebraMap k (GaloisField 2 (2 * f))).toMonoidHom) t
  have hte6 : te6SL2 (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj 3 (HSL t) =
      te6N (frobQ 2 f) 3 *
        fixSL2 (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj rhoPerm_three (HSL t) *
        (te6N (frobQ 2 f) 3)⁻¹ := rfl
  rw [hte6]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [map_mul, map_mul, map_inv]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have hfix : ((e6Isogeny (GaloisField 2 (2 * f))
      (fixSL2 (frobQ 2 f) (algebraMap k (GaloisField 2 (2 * f))) hj rhoPerm_three (HSL t)) :
      adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :
      ModGL Tag.E6 (GaloisField 2 (2 * f))) =
      rootDiagUnit Tag.E6 (fun j => u ^ Tag.E6.cartan 3 j) := by
    rw [fixSL2_val, map_HSL]
    have hsl : HSL u = sl2Diag u := rfl
    rw [hsl, simpleSL2_diag, e6Isogeny_hm_eq]
    rfl
  have hN : ((e6Isogeny (GaloisField 2 (2 * f)) (te6N (frobQ 2 f) 3) :
      adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :
      ModGL Tag.E6 (GaloisField 2 (2 * f))) =
      ((CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3).map
        (fun i => weylElt Tag.E6 (GaloisField 2 (2 * f)) i 1)).prod := by
    rw [te6N_val]
    change ((e6Isogeny (GaloisField 2 (2 * f)) (e6NWord (GaloisField 2 (2 * f))
      (CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3)) :
      adjointGroup Tag.E6 (GaloisField 2 (2 * f))) :
      ModGL Tag.E6 (GaloisField 2 (2 * f))) = _
    rw [e6Isogeny_nWord]
  rw [hN, hfix]
  rw [conj_weylElt_word_rootDiagUnit]
  have hz : (fun j => u ^
      ((CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3).foldr torusExp
        (fun j => Tag.E6.cartan 3 j)) j) =
      Pi.mulSingle (1 : Fin Tag.E6.rank) u := by
    rw [te6Words_three_torusExp]
    funext j
    by_cases h : j = 1 <;> simp [Pi.mulSingle, Pi.single, Function.update, h]
  have hspec : (CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3).foldr
      (fun i b j => b j * b i ^ (-Tag.E6.cartan i j))
      (fun j => u ^ Tag.E6.cartan 3 j) =
      (fun j => u ^ ((CFSG.RankThree.PartTwo.Census.Exceptional.te6Words 3).foldr torusExp
        (fun j => Tag.E6.cartan 3 j) j)) :=
    foldr_torusReflect_zpow _ _ u
  rw [hspec, hz]
  rw [E6GraphLevi.thetaTorusHom_apply, E6GraphLevi.rootTorusSL2_e6HighestRoot]
  rfl

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
