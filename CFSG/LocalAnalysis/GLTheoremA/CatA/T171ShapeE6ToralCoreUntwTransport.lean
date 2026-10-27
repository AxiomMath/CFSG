module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreUntwDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralLangOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescProof
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentral
import CFSG.Assembly.LargeEvenGLABridge
import CFSG.LieType.Automorphisms.SteinbergBLCompleteIndexTwo
import CFSG.Assembly.OpenBridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE

theorem e6ComponentCore_of_toralComponentAction
    (hcore : E6ToralComponentAction) : E6ComponentCore := by
  intro G _ _ L J A d b n K _ _ _ hn hK h3 hS θ wd wb hd hb w g0 hg0 hF htorus
  classical
  haveI : Finite (TableBExc.RecipeGroup Tag.E6 K) := Finite.of_equiv _ θ.toEquiv
  have hdL : d ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem
  have hcomp : CFSG.Assembly.IsComponentOf J
      (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hS.comp.1
  have hlayer : LargeEvenLayer (L ⊓ Subgroup.centralizer ({d} : Set G)) = J := by
    rw [CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer]
    exact hS.comp.2
  have hdesc := componentDescent_holds (G := G) (L := L)
    (R := TableBExc.RecipeGroup Tag.E6 K) hS.qs θ d hdL (e6RecipeConj wd) hd J hcomp hlayer
  have hbL : b ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.b_mem
  have hnorm := map_conjOn_image_of_normalizes θ hbL hS.b_norm hb
  have hwd3 : wd ^ 3 = 1 := e6wd_pow_three_eq_one hS hd
  have hwd1 : wd ≠ 1 := e6wd_ne_one hS hd
  have hwb3 : wb ^ 3 = 1 := e6wb_pow_three_eq_one hS hb
  exact hcore n K hn hK h3 wd wb hwd3 hwd1 hwb3 w g0 hg0 hF htorus _ hdesc.1 hnorm

theorem e6LangTorusExit_of_componentCore
    (hcore : E6ComponentCore) : E6LangTorusExit := by
  intro G _ _ L J A d b n K _ _ _ hn hK h3 hS θ wd wb hd hb w g0 hg0 hF htorus
  haveI : Finite (TableBExc.RecipeGroup Tag.E6 K) := Finite.of_equiv _ θ.toEquiv
  have hdiag : InnDiagOn 3 (Subgroup.zpowers (e6RecipeConj wb))
      (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K))) :=
    hcore G L J A d b n K hn hK h3 hS θ wd wb hd hb w g0 hg0 hF htorus
  have hN : e6RecipeConj wb ∈ Subgroup.normalizer
      ((((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K))) :
          Set (MulAut (TableBExc.RecipeGroup Tag.E6 K))) :=
    hdiag.1 (Subgroup.mem_zpowers _)
  have hcenter : Subgroup.center (TableBExc.RecipeGroup Tag.E6 K) = ⊥ :=
    CFSG.StandardType.TableBExc.center_recipeGroup_eq_bot (τ := Tag.E6) (K := K)
  have hι : Function.Injective (MulAut.conj :
      TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K)) :=
    CFSG.LieType.Automorphisms.conj_injective_of_center_eq_bot hcenter
  have hnat : ∀ x ∈ (J.subgroupOf L).map (piCenterQuot θ),
      MulAut.conj (e6RecipeConj wb x) =
        e6RecipeConj wb * MulAut.conj x * (e6RecipeConj wb)⁻¹ :=
    fun x _ => (CFSG.LieType.Automorphisms.mulAut_conj_conj _ x).symm
  obtain ⟨e, he⟩ := componentDescentIndAut_of_conjOn_map (p := 3) (L := L) (J := J)
    (A := A) (d := d) (b := b)
    (ι := (MulAut.conj :
      TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K)))
    hι θ (e6RecipeConj wb) (e6RecipeConj wb) hS hb hN hnat
  have hdiag' : InnDiagOn 3 (Subgroup.zpowers (e6RecipeConj wb)⁻¹)
      (((J.subgroupOf L).map (piCenterQuot θ)).map (MulAut.conj :
        TableBExc.RecipeGroup Tag.E6 K →* MulAut (TableBExc.RecipeGroup Tag.E6 K))) := by
    simpa only [Subgroup.zpowers_inv] using hdiag
  exact innDiagOn_of_psimple_iso hS.pcomp e hS.b_norm (Subgroup.inv_mem _ hN) he hdiag'

theorem e6LangTorusExit_of_toralComponentAction
    (hcore : E6ToralComponentAction) : E6LangTorusExit :=
  e6LangTorusExit_of_componentCore (e6ComponentCore_of_toralComponentAction hcore)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
