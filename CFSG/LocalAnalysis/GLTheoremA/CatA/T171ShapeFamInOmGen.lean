module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescProof
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Std
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Down
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Cover
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Facts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156Layer
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.FixedCommutingProduct
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem componentDescent_component {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {d : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) {φ : MulAut R}
    (hind : LargeEvenInduces θ (conjRel d) φ) {J : Subgroup G}
    (hJ : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G))) :
    CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ)) (fixedSubgroup φ) := by
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
  have h := CFSG.StandardType.LayerCC.isComponentOf_map_ggFix hf hker hαβ hJ'
  change CFSG.Assembly.IsComponentOf ((J.subgroupOf L).map (piCenterQuot θ)) (ggFix φ)
  simpa only [f] using h

abbrev isLinearCharTwoIdx : TauCeti.LieTypeIndex → Prop :=
  fun i => ∃ (n : ℕ) (q : TauCeti.PrimePower), i = .A n q ∧ q.p = 2

abbrev isUnitaryCharTwoIdx : TauCeti.LieTypeIndex → Prop :=
  fun i => ∃ (n : ℕ) (q : TauCeti.PrimePower), i = .twistedA n q ∧ q.p = 2

@[expose] def InnerCompData (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
      (hS : Setup p L J A d b),
    catalogIs (PSimple p L) (onLie F) → ¬ I171.I171LieShapeAt p L →
      InducesInnerMod p L b → b ∉ Subgroup.zpowers d →
        b ∉ Subgroup.centralizer (J : Set G) →
        (catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
            MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
          (catalogIs (PSimple p J) (onLie isUnitaryCharTwoIdx) ∧
            MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J)) ∨
            InducesInnerMod p J b

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
