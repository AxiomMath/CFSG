module

public import CFSG.ClassicalInvolution.RouteD.TWEB6Bridge
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSplitProd
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD.TWE.B6
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.Models (linearBlockStandardPair_of_normalized)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Bridge

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem bridge_aux_gen (hodd : Odd (Nat.card K)) {n : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)}
    {i : ℕ → V ≃ₗ[K] V} (hc : VChain Q (n + 1) L i) {L5 : Subgroup (V ≃ₗ[K] V)}
    (h5 : IsFundamental Q L5 (i n)) (hne : L5 ≠ L n) (p : ℕ → HypPair Q)
    (horth : ∀ a b, a ≤ n + 1 → b ≤ n + 1 → a ≠ b → (p a).Orth (p b))
    (hL : ∀ a (ha : a < n + 1), L a =
      (oFrame true (p a) (p (a + 1)) (horth a (a + 1) ha.le (by omega) (by omega))).La.range)
    (q : HypPair Q) (hq : ∀ a < n + 2, (p a).Orth q) :
    (∀ a < n, Commutes (mkFrame (p (n + 1)) (swapPair q)
        (orth_swapPair (hq (n + 1) (by omega)))).La.range (L a)) ∧
    LinearBlockStandardPair K (L n ⊔
      (mkFrame (p (n + 1)) (swapPair q) (orth_swapPair (hq (n + 1) (by omega)))).La.range) (L n)
      (mkFrame (p (n + 1)) (swapPair q) (orth_swapPair (hq (n + 1) (by omega)))).La.range ∧
    LinearBlockStandardPair K (L5 ⊔
      (mkFrame (p (n + 1)) (swapPair q) (orth_swapPair (hq (n + 1) (by omega)))).La.range) L5
      (mkFrame (p (n + 1)) (swapPair q) (orth_swapPair (hq (n + 1) (by omega)))).La.range := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set F := mkFrame (p (n + 1)) (swapPair q) (orth_swapPair (hq (n + 1) (by omega))) with hF
  refine ⟨fun a ha => ?_, ?_⟩
  · rw [hL a (by omega)]
    refine commutes_of_span_orth F _ ?_
    rw [frame_span_eq, frame_span_eq]
    simp only [oFrame, mkFrame, twistPair, ite_true, hypPlane_swapPair, hF]
    refine polar_eq_zero_of_sup (fun x hx y hy => ?_) (fun x hx y hy => ?_)
      (fun x hx y hy => ?_) (fun x hx y hy => ?_)
    · exact polar_hypPlane_of_orth (horth (n + 1) a (by omega) (by omega) (by omega)) x hx y hy
    · exact polar_hypPlane_of_orth (horth (n + 1) (a + 1) (by omega) (by omega) (by omega)) x hx
        y hy
    · exact polar_hypPlane_of_orth (hq a (by omega)).symm x hx y hy
    · exact polar_hypPlane_of_orth (hq (a + 1) (by omega)).symm x hx y hy
  · let T : Triple Q := ⟨p n, p (n + 1), q, horth n (n + 1) (by omega) (by omega) (by omega),
      hq n (by omega), hq (n + 1) (by omega)⟩
    have hL4 : L n = T.frame01.swap.La.range := by
      rw [hL n (by omega)]
      rfl
    have hFT : F = T.frame12.swap := rfl
    have hf4 : IsFundamental Q (L n) (T.frame01.swap.La (-1)) :=
      hL4 ▸ IsFundamental.of_frame T.frame01.swap
    have hi4 : i n = T.frame01.swap.La (-1) :=
      IsFundamental.involution_unique hodd (hc.fund n (by omega)) hf4
    have hL5 : L5 = T.frame01.La.range := by
      obtain ⟨F'', hF''L, hF''i⟩ := h5
      have hii : F''.La (-1) = T.frame01.swap.La (-1) := hF''i.symm.trans hi4
      rcases Frame.La_range_eq_or_eq_swap h2 hii with h | h
      · exact absurd (hF''L.trans (h.trans hL4.symm)) hne
      · rw [hF''L, h]
        rfl
    have hker : ∀ θ : SL(3, K) →* (V ≃ₗ[K] V), Function.Injective θ →
        θ.ker ≤ Subgroup.center SL(3, K) := fun θ hinj => by
      rw [(MonoidHom.ker_eq_bot_iff θ).mpr hinj]
      exact bot_le
    refine ⟨?_, ?_⟩
    · obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta (Or.inr hL4) (Or.inr rfl)
      rw [hFT]
      exact linearBlockStandardPair_of_normalized (hker θ hinj) hrange hU hV
    · obtain ⟨θ, hinj, hrange, hU, hV⟩ := T.exists_theta (Or.inl hL5) (Or.inr rfl)
      rw [hFT]
      exact linearBlockStandardPair_of_normalized (hker θ hinj) hrange hU hV

theorem exists_bridges_gen (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hn : 1 ≤ n) (hdim : 2 * n + 7 ≤ Module.finrank K V) {L : ℕ → Subgroup (V ≃ₗ[K] V)}
    {i : ℕ → V ≃ₗ[K] V} (hc : VChain Q (n + 1) L i) {L5 : Subgroup (V ≃ₗ[K] V)}
    (h5 : IsFundamental Q L5 (i n)) (hne : L5 ≠ L n) :
    ∃ S₁ S₂ : Subgroup (V ≃ₗ[K] V), S₁ ∈ fundSet Q ∧ S₂ ∈ fundSet Q ∧
      (∀ a < n, Commutes S₁ (L a) ∧ Commutes S₂ (L a)) ∧
      LinearBlockStandardPair K (L n ⊔ S₁) (L n) S₁ ∧
      LinearBlockStandardPair K (L5 ⊔ S₁) L5 S₁ ∧
      LinearBlockStandardPair K (L n ⊔ S₂) (L n) S₂ ∧
      LinearBlockStandardPair K (L5 ⊔ S₂) L5 S₂ ∧ ¬ Commutes S₁ S₂ ∧ S₁ ≠ S₂ := by
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, hpl, hL⟩ := exists_chain_pairs true hodd hc (by omega : 2 ≤ n + 1)
  have ho : ∀ a b, a < n + 2 → b < n + 2 → a ≠ b → (p a).Orth (p b) :=
    fun a b ha hb hab => horth a b (by omega) (by omega) hab
  obtain ⟨q₁, q₂, c, hq, he, hf, hQc, hce, hcf⟩ :=
    exists_two_pairs_perp hodd hQ p (n + 2) ho (by omega)
  have hq₁ : ∀ a < n + 2, (p a).Orth q₁ := fun a ha => (hq a ha).1
  have hq₂ : ∀ a < n + 2, (p a).Orth q₂ := fun a ha => (hq a ha).2
  obtain ⟨c₁, s₁, t₁⟩ := bridge_aux_gen hodd hc h5 hne p horth hL q₁ hq₁
  obtain ⟨c₂, s₂, t₂⟩ := bridge_aux_gen hodd hc h5 hne p horth hL q₂ hq₂
  set F₁ := mkFrame (p (n + 1)) (swapPair q₁) (orth_swapPair (hq₁ (n + 1) (by omega))) with hF₁
  set F₂ := mkFrame (p (n + 1)) (swapPair q₂) (orth_swapPair (hq₂ (n + 1) (by omega))) with hF₂
  refine ⟨F₁.La.range, F₂.La.range, ⟨_, IsFundamental.of_frame F₁⟩,
    ⟨_, IsFundamental.of_frame F₂⟩, fun a ha => ⟨c₁ a ha, c₂ a ha⟩, s₁, t₁, s₂, t₂, ?_⟩
  have hmemF : ∀ (F : OFrame Q), F.P = p (n + 1) → ∀ x ∈ hypPlane (p (n + 1)),
      x ∈ negSpace (F.La (-1)) := by
    intro F hFP x hx
    rw [negSpace_La_neg_one h2, frame_span_eq, hFP]
    exact Submodule.mem_sup_left hx
  have hne' : F₂.La (-1) ≠ F₁.La (-1) := by
    intro heq
    set f := q₁.f with hff
    have e1 := La_neg_one_mkFrame_swap (p (n + 1)) q₁ (hq₁ (n + 1) (by omega)) f
    have e2 := La_neg_one_mkFrame_swap (p (n + 1)) q₂ (hq₂ (n + 1) (by omega)) f
    have hx1 : (F₁.La (-1)) f = f - (2 : K) • (polar Q f (p (n + 1)).f • (p (n + 1)).e +
        polar Q f (p (n + 1)).e • (p (n + 1)).f + polar Q f q₁.e • q₁.f +
        polar Q f q₁.f • q₁.e) := e1
    have hx2 : (F₂.La (-1)) f = f - (2 : K) • (polar Q f (p (n + 1)).f • (p (n + 1)).e +
        polar Q f (p (n + 1)).e • (p (n + 1)).f + polar Q f q₂.e • q₂.f +
        polar Q f q₂.f • q₂.e) := e2
    have hh := congrArg (fun g : V ≃ₗ[K] V => polar Q f (g f)) heq
    simp only [hx1, hx2] at hh
    have o1 : polar Q f (p (n + 1)).f = 0 := by
      rw [polar_comm]
      exact (hq₁ (n + 1) (by omega)).ff
    have o2 : polar Q f (p (n + 1)).e = 0 := by
      rw [polar_comm]
      exact (hq₁ (n + 1) (by omega)).ef
    have o3 : polar Q f q₁.e = 1 := q₁.polar_fe
    have o4 : polar Q f q₁.f = 0 := q₁.polar_ff
    have o5 : polar Q f q₂.e = 1 := by rw [he]; exact o3
    have o6 : polar Q f q₂.f = -Q c := by
      rw [hf, polar_sub_right, polar_add_right, polar_smul_right_eq, o4, hcf, o3]
      ring
    simp only [polar_sub_right, polar_add_right, polar_smul_right_eq, o1, o2, o3, o4, o5, o6,
      zero_mul, zero_add, add_zero, mul_zero] at hh
    have h4 : (2 : K) * (2 * Q c) = 0 := by linear_combination hh
    rcases mul_eq_zero.mp h4 with h | h
    · exact h2 h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h2 h'
      · exact hQc h'
  refine ⟨not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame F₂)
    hne' (hmemF F₁ rfl _ (e_mem_hypPlane (p (n + 1)))) (hmemF F₂ rfl _
      (f_mem_hypPlane (p (n + 1))))
    (by rw [(p (n + 1)).polar_ef]; exact one_ne_zero), fun h => hne' ?_⟩
  exact IsFundamental.involution_unique hodd (IsFundamental.of_frame F₂)
    (h ▸ IsFundamental.of_frame F₁)

end Bridge

end CFSG.ClassicalInvolution.Q3.Q3TWY
