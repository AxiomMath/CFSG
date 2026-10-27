module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Defs
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem componentDescent_holds : ComponentDescent := by
  intro G _ _ L hLq R _ _ θ d hd φ hind J hJ hlayer
  let f : ↥L →* R := piCenterQuot θ
  let a : MulAut ↥L := ggGamma L (le_refl (Subgroup.normalizer (L : Set G)))
    ⟨d⁻¹, Subgroup.inv_mem _ hd⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨q, rfl⟩ := θ.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hker : f.ker ≤ Subgroup.center ↥L := by
    rw [show f.ker = Subgroup.center ↥L from by
      dsimp only [f, piCenterQuot]
      rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center ↥L))
        θ.toMonoidHom θ.injective, QuotientGroup.ker_mk']]
  have hcen : Subgroup.centralizer ({d⁻¹} : Set G) =
      Subgroup.centralizer ({d} : Set G) := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    change Commute x d⁻¹ ↔ Commute x d
    constructor
    · intro hx
      simpa using hx.inv_right
    · intro hx
      exact hx.inv_right
  have hfix : (ggFix a).map L.subtype = L ⊓ Subgroup.centralizer ({d} : Set G) := by
    have h := map_ggFix_ggGamma (B := Subgroup.normalizer (L : Set G)) L
      (le_refl (Subgroup.normalizer (L : Set G))) ⟨d⁻¹, Subgroup.inv_mem _ hd⟩
    rw [hcen] at h
    simpa only [a] using h
  have hfix' : ggFix a = (L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L := by
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    rw [hfix, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hJ' : CFSG.Assembly.IsComponentOf (J.subgroupOf L) (ggFix a) := by
    have hJopen : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
      (CFSG.Assembly.isComponentOf_iff_open).1 hJ
    have h1 := CFSG.LocalAnalysis.GLTheoremA.S265.isComponentOf_subgroupOf (H := L)
      inf_le_left hJopen
    have h1' : CFSG.Assembly.IsComponentOf (J.subgroupOf L)
        ((L ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf L) :=
      (CFSG.Assembly.isComponentOf_iff_open).2 h1
    simpa [hfix'] using h1'
  have hαβ : ∀ x : ↥L, f (a x) = φ (f x) := by
    intro x
    have hrel : conjRel d x (a x) := by
      simp only [conjRel, a]
      simpa using ggGamma_coe L (le_refl (Subgroup.normalizer (L : Set G)))
        ⟨d⁻¹, Subgroup.inv_mem _ hd⟩ x
    have h := hind x (a x) hrel
    exact h.symm
  have himg : CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ))
      (fixedSubgroup φ) := by
    have h := CFSG.StandardType.LayerCC.isComponentOf_map_ggFix hf hker hαβ hJ'
    change CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ)) (ggFix φ)
    simpa only [f] using h
  have hE : LargeEvenLayer (ggFix a) = J.subgroupOf L := by
    apply Subgroup.map_injective (f := L.subtype) L.subtype_injective
    rw [← CFSG.StandardType.largeEvenLayer_map_of_injective L.subtype L.subtype_injective
      (ggFix a), hfix, hlayer, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hJ.1.trans inf_le_left)]
  refine ⟨himg, ?_⟩
  have hmap := CFSG.StandardType.LayerCC.map_largeEvenLayer_ggFix hf hker hαβ
  rw [hE] at hmap
  change LargeEvenLayer (ggFix φ) = (J.subgroupOf L).map (piCenterQuot θ)
  simpa only [f] using hmap.symm

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
