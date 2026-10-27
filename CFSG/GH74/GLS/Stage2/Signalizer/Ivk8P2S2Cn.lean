module

public import CFSG.GH74.Defs
public import CFSG.GH74.GLS.Classes
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.Prop28Basic
public import CFSG.GH74.GLS.Stage2.Local.Prop28Layer
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Lift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Blocks.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SectionRank.CentralLift
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.GH74.GLS.Stage2.Final.L26 (WBar_two_pow WBar_le_generalizedFitting)
open CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem not_isSimpleGroup_of_center_ne_bot {X : Type*} [Group X] (hq : IsQuasisimple X)
    (hz : center X ≠ ⊥) : ¬ IsSimpleGroup X := by
  intro hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · exact hz h
  · obtain ⟨-, -, a, b, hab⟩ := hq
    have hsub : Subsingleton (X ⧸ center X) := QuotientGroup.subsingleton_iff.mpr h
    exact hab (Subsingleton.elim _ _)

theorem center_ne_bot_of_hasSL2Model_odd {K : Type} [Group K] (h : HasSL2Model K Odd) :
    center K ≠ ⊥ := by
  obtain ⟨F, _, _, hodd, ⟨e⟩⟩ := h
  have h2F : (2 : F) ≠ 0 := CFSG.ABGLocalTools.two_ne_zero_of_odd_card hodd
  let e' : SL(2, F) ≃* K := (specialLinearGroupEquivStatedSL 2 F).trans e.symm
  have hne : (-1 : SL(2, F)) ≠ 1 := by
    intro h
    have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    exact h2F (by linear_combination (-1 : F) * h00)
  intro hbot
  have hmem : e' (-1) ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    ext i j
    simp
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hne (e'.injective (by simpa using hmem))


theorem hasSL2Model_odd {K : Type} [Group K] {q : ℕ} (hq : Odd q)
    (h : HasSL2Model K (fun r => r = q)) : HasSL2Model K Odd := by
  obtain ⟨F, _, _, hF, e⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF ▸ hq, e⟩

theorem center_ne_bot_of_doubleCover {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsDoubleCoverOfAlt X n) {K : Subgroup X} (hK : IsComponent K) : center ↥K ≠ ⊥ := by
  have hK' : K = ⊤ := Prop28.isComponent_eq_top_of_isQuasisimple h.1 hK
  subst hK'
  have hne : center X ≠ ⊥ :=
    (Subgroup.one_lt_card_iff_ne_bot (center X)).mp (by rw [h.2.1]; norm_num)
  obtain ⟨c, hc⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  intro hbot
  have hmem : (⟨c.1, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup X)) ∈ center ↥(⊤ : Subgroup X) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp c.2 g.1)
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hc (Subtype.ext (congrArg (fun x : ↥(⊤ : Subgroup X) => (x : X)) hmem))

theorem allComponentsNonsimple_of_stage2 {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (ctx : Stage2Ctx G z k S) : AllComponentsNonsimple z := by
  intro K hK hsimp
  have hq : IsQuasisimple ↥K := hK.1
  suffices hZ : center ↥K ≠ ⊥ from not_isSimpleGroup_of_center_ne_bot hq hZ hsimp
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Group.IsPerfect ↥K := hq.1
  have hKF : K ≤ generalizedFitting (CentralizerBar z) :=
    ((le_sSup hK : K ≤ layer (CentralizerBar z))).trans le_sup_right
  cases ctx.data with
  | g2 h =>
    obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := h.shape
    obtain ⟨hr₁, hr₂, -, hprod, hsl₁, hsl₂, -, hF3, hFbig, -, -, -⟩ := hsh
    have hr₂' : 2 ≤ r₂ := by
      obtain ⟨F, _, _, hF, -⟩ := hsl₂
      rw [← hF]
      exact Finite.one_lt_card
    have hKle : K ≤ LBar z := by
      rcases Nat.lt_or_ge 3 r₂ with h3 | h3
      · rw [(hFbig h3).2] at hKF
        exact hKF
      · have h3' : r₂ = 3 := by
          obtain ⟨m, hm⟩ := hr₂
          omega
        rw [(hF3 h3').2] at hKF
        exact hKF.trans (Subgroup.map_subtype_le _)
    have hsup : K ≤ L₁ ⊔ L₂ := hprod.1 ▸ hKle
    have key : ∀ {L : Subgroup (CentralizerBar z)} {r : ℕ}, Odd r →
        HasSL2Model ↥L (fun q => q = r) → K ≤ L → center ↥K ≠ ⊥ := by
      intro L r hr hsl hKL
      rcases solvable_or_quasisimple_of_hasSL2Model (hasSL2Model_odd hr hsl) with hs | hqs
      · exfalso
        have hsolvK : Group.IsSolvable ↥K :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKL)
        exact Group.IsPerfect.not_isSolvable ↥K hsolvK
      · have hKeq : K = L := comp_eq_of_le_quasisimple hqs hK hKL
        subst hKeq
        exact center_ne_bot_of_hasSL2Model_odd (hasSL2Model_odd hr hsl)
    rcases comp_le_or_le_of_commute hprod.2.1 hK hsup with h1 | h2
    · exact key hr₁ hsl₁ h1
    · exact key hr₂ hsl₂ h2
  | m12 h =>
    exfalso
    obtain ⟨A, -, -, -, hF, -, -⟩ := h.L_shape
    rw [hF] at hKF
    have hKp : IsPGroup 2 ↥K := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha⟩ := WBar_two_pow z x (hKF hx)
      exact ⟨a, Subtype.ext ha⟩
    have hsolvK : Group.IsSolvable ↥K := by
      have : Group.IsNilpotent ↥K := hKp.isNilpotent
      infer_instance
    exact Group.IsPerfect.not_isSolvable ↥K hsolvK
  | psp4 h =>
    obtain ⟨q, L₁, L₂, hP⟩ := h
    have hKm : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hP.pair.comps]; exact hK
    rcases hKm with h1 | h2
    · subst h1
      exact center_ne_bot_of_hasSL2Model_odd (hasSL2Model_odd hP.pair.odd hP.pair.sl₁)
    · have h2' : K = L₂ := h2
      subst h2'
      exact center_ne_bot_of_hasSL2Model_odd (hasSL2Model_odd hP.pair.odd hP.pair.sl₂)
  | l4 ε h =>
    obtain ⟨q, L₁, L₂, hL⟩ := h
    have hKm : K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hL.pair.comps]; exact hK
    rcases hKm with h1 | h2
    · subst h1
      exact center_ne_bot_of_hasSL2Model_odd (hasSL2Model_odd hL.pair.odd hL.pair.sl₁)
    · have h2' : K = L₂ := h2
      subst h2'
      exact center_ne_bot_of_hasSL2Model_odd (hasSL2Model_odd hL.pair.odd hL.pair.sl₂)
  | mcl h =>
    obtain ⟨n, -, hS⟩ := h
    exact center_ne_bot_of_doubleCover hS.cover hK
  | ly h =>
    obtain ⟨n, -, hS⟩ := h
    exact center_ne_bot_of_doubleCover hS.cover hK


theorem hat_equiv_component {G : Type} [Group G] [Finite G] {z : G} {J : Subgroup G}
    (hJ : IsPCompIn 2 (Cen z) J) :
    ∃ K : Subgroup (CentralizerBar z), IsComponent K ∧ Nonempty (Hat J ≃* ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, hJp⟩ := hJ
  obtain ⟨K, hK, hsub, hmap, -⟩ := id hJp
  refine ⟨K, hK, ?_⟩
  obtain ⟨e₁⟩ := Prop28.quot_pPrimeCore_congr (Subgroup.subgroupOfEquivOfLe hJC).symm
  let e₂ := CFSG.ComponentClassification.CatalogueBHeldSmallCore.subnormalCoreQuotientEquivImage
    2 (J.subgroupOf (Cen z)) hsub
  exact ⟨e₁.trans (e₂.trans (MulEquiv.subgroupCongr hmap))⟩

theorem hat_not_isSimpleGroup {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (ctx : Stage2Ctx G z k S) {J : Subgroup G} (hJ : IsPCompIn 2 (Cen z) J) :
    ¬ IsSimpleGroup (Hat J) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hat_equiv_component hJ
  intro hs
  exact allComponentsNonsimple_of_stage2 ctx K hK (e.isSimpleGroup_congr.mp hs)

theorem not_alt7_or_L2_of_nonsimple {X : Type} [Group X] (hq : IsQuasisimple X)
    (hns : ¬ IsSimpleGroup X) :
    ¬ (Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 X Odd) := by
  intro hcon
  rcases hcon with h7 | hL2
  · obtain ⟨e⟩ := h7
    exact hns (e.isSimpleGroup_congr.mpr (alternatingGroup.isSimpleGroup (by simp)))
  · obtain ⟨F, hF, hFin, hodd, ⟨e⟩⟩ := hL2
    by_cases h3 : Nat.card F = 3
    · have hS := isSolvable_statedSL_of_card_three h3
      have hL : Group.IsSolvable (IVK.L2 F) :=
        Group.isSolvable_of_surjective
          (f := QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F)))
          (QuotientGroup.mk'_surjective _)
      have hX : Group.IsSolvable X :=
        Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      have : Nontrivial X := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect X := hq.1
      exact Group.IsPerfect.not_isSolvable X hX
    · have h4 := four_le_card_of_odd hodd h3
      have hq2 : IsQuasisimple SL(2, F) := isQuasisimple_special_linear_two h4
      have hs : IsSimpleGroup (SL(2, F) ⧸ center SL(2, F)) := hq2.2.1
      exact hns ((e.trans (IVK.L2.equivPSL F)).isSimpleGroup_congr.mpr hs)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.P2S2
