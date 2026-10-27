module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10StabS8
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Final
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Smith
public import Certificates.Certificate8063
public import Certificates.Certificate17023
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.GroupTheory.SteinbergCBFTCores
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Layer
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124BlkTransfer
public import CFSG.Quasithin.Background.C124InterfaceDefs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.AGLEmbedding KFactsPair

@[expose] def K5192P2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ Ls : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) →
      ∃ P₂ : Subgroup (X ⧸ gnC T), P₂ ≤ Ls ∧ IsTwoFourSFive P₂ ∧
        (oddHull P₂ ≤ gnA T T₁ Ls ∨ oddHull P₂ ≤ gnA T T₂ Ls)

namespace K5192Proof

theorem center_eq_bot_of_equiv_alt_ten {G : Type} [Group G] (e : G ≃* alternatingGroup (Fin 10)) :
    Subgroup.center G = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin 10)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := Subgroup.mem_center_iff.1 hz (e.symm y)
    simpa using congrArg e this
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h1
  exact e.injective (h1.trans (map_one e).symm)

theorem exists_s8
    {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hG : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} (hLs : GNYComponent T T₁ T₂ Ls)
    (e : ↥Ls ≃* alternatingGroup (Fin 10)) :
    ∃ P₁ : Subgroup (X ⧸ gnC T), P₁ ≤ Ls ∧ Nonempty (↥P₁ ≃* Equiv.Perm (Fin 8)) ∧
      oddHull P₁ ≤ gnA T T₁ Ls := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := hG.c118
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hLs
  have hGF : CFSG.HardMathSupport.Cooperstein.Coordinator.GF2EightFive :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.gf2EightFive_of_b42L42Core
      CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.b42L42Core_holds
  have hcen : Subgroup.center ↥Ls = ⊥ := center_eq_bot_of_equiv_alt_ten e
  have he : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* alternatingGroup (Fin 10)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot.trans e)⟩
  obtain ⟨-, φ, hφinj, hφ⟩ :=
    exists_alt_eight_le_centralizer hGF hX hLs.1 hJ (by norm_num : 8 < 10) he
  have hφA : φ.range ≤ gnA T T₁ Ls := hφ.trans (gnImg_centralizer_inf_le_gnA h1Z Ls)
  let φ' : alternatingGroup (Fin 8) →* ↥Ls := φ.codRestrict Ls fun s => (hφ ⟨s, rfl⟩).2
  have hφ'inj : Function.Injective φ' := fun s t h => hφinj (congrArg Subtype.val h)
  let ψ : alternatingGroup (Fin 8) →* Equiv.Perm (Fin 10) :=
    ((alternatingGroup (Fin 10)).subtype.comp e.toMonoidHom).comp φ'
  have hψ : Function.Injective ψ := fun s t h =>
    hφ'inj (e.injective (Subtype.ext h))
  obtain ⟨P, ⟨eP⟩, hPodd⟩ := exists_s8_of_embed ψ hψ
  let ι : alternatingGroup (Fin 10) →* X ⧸ gnC T := Ls.subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := fun x y h =>
    e.symm.injective (Subtype.ext h)
  refine ⟨P.map ι, ?_, ⟨(Subgroup.equivMapOfInjective P ι hι).symm.trans eP⟩, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact (e.symm y).2
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨y, hy, rfl⟩, hodd⟩
    have hodd' : Odd (orderOf y) := by rwa [← orderOf_injective ι hι y]
    obtain ⟨s, hs⟩ := hPodd y hy hodd'
    have hs' : e (φ' s) = y := Subtype.ext hs
    have hys : ι y = φ s := by
      show ((e.symm y : ↥Ls) : X ⧸ gnC T) = φ s
      rw [← hs', e.symm_apply_apply]
      rfl
    rw [SetLike.mem_coe, hys]
    exact hφA ⟨s, rfl⟩

theorem k5192_of_p2
    (h : K5192P2) : K5192 := by
  intro X _ _ T T₁ T₂ hX hG Ls hLs hinv he
  obtain ⟨P₂, hP₂le, hP₂shape, hP₂odd⟩ := h X T T₁ T₂ hX hG Ls hLs hinv he
  obtain ⟨P₁, hP₁le, hP₁, hP₁odd⟩ := exists_s8 hX hG hLs he.some
  exact ⟨P₁, P₂, hP₁le, hP₂le, hP₁, hP₂shape, hP₁odd, hP₂odd⟩

end K5192Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
