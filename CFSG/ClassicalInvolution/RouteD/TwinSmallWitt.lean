module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinGen
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix
public import CFSG.ClassicalInvolution.RouteD.TwinSmallModel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusLift
public import CFSG.ClassicalInvolution.RouteD.GapsOrthSpin
public import CFSG.ClassicalInvolution.RouteD.LocalTwinChain
public import CFSG.ClassicalInvolution.RouteD.TypeCChain
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
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

namespace CFSG.ClassicalInvolution.RouteD.TwinSmall

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.RouteD.Gaps

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Witt

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Invertible (2 : F)] [FiniteDimensional F V]

theorem false_of_succ_pairs {k : ℕ} (F₀ : HypFrame Q k)
    (hrest : ∀ v : V, (∀ i r, polar Q v (F₀.vec i r) = 0) → Q v = 0 → v = 0)
    (P : Fin (k + 1) → HypPair Q) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) : False := by
  have hv : IsHypFam Q (fun (i : Fin k) s => F₀.vec i s) :=
    ⟨fun i s => F₀.map_vec i s, fun i j hij s t => F₀.polar_vec_of_ne hij s t,
      fun i s => F₀.polar_vec_not i s⟩
  have hv' : IsHypFam Q (hypPairFam fun i : Fin k => P (Fin.castSucc i)) :=
    isHypFam_hypPairFam _ fun i j hij => hP _ _ fun h => hij (Fin.castSucc_injective _ h)
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hωinv : ω.symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem hω
  have hlast : ∀ i : Fin k, (Fin.last k) ≠ Fin.castSucc i := fun i h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hu : ω.symm (P (Fin.last k)).e = 0 := by
    apply hrest
    · intro i r
      have h1 : ω.symm (ω (F₀.vec i r)) = F₀.vec i r := ω.symm_apply_apply _
      rw [← h1, polar_map_of_mem hωinv, hωv i r]
      cases r
      · exact (hP _ _ (hlast i)).ef
      · exact (hP _ _ (hlast i)).ee
    · rw [map_of_mem hωinv]
      exact (P (Fin.last k)).Q_e
  have : (P (Fin.last k)).e = 0 := by
    have := congrArg ω hu
    simpa using this
  exact (P (Fin.last k)).e_ne_zero this

end Witt

section Minus

variable {F : Type} [Field F] [Finite F] {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit [Finite F] in
include hirr in
theorem minusHyp_hrest (n : ℕ) (v : Vm n F)
    (hv : ∀ i r, polar (quadMinus n F b c) v ((minusHyp n b c).vec i r) = 0)
    (hQ : quadMinus n F b c v = 0) : v = 0 := by
  have hv' : ∀ k r, polar (quadMinus n F b c) v (minusVec n k r) = 0 := hv
  have h1 := eq_planeVec_of_polar_minusVec n b c hv'
  set w : Fin 2 → F := fun t => v (.inr (.inr t)) with hw
  rw [h1, quadMinus_planeVec'] at hQ
  by_contra hne
  have hw0 : w ≠ 0 := fun h => hne (by rw [h1, h, planeVec_zero])
  exact planeNorm_ne_zero hirr hw0 hQ

include hirr in
theorem false_of_pairs_minus (hodd : Odd (Nat.card F)) {n : ℕ} (hn : 1 ≤ n)
    (P : Fin n → HypPair (quadMinus n F b c)) (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) : False := by
  have : Invertible (2 : F) := invertibleOfNonzero (IsFundamental.two_ne_zero_of_odd hodd)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact false_of_succ_pairs (minusHyp (k + 1) b c) (fun v h1 h2 => minusHyp_hrest hirr _ v h1 h2) P
    hP

theorem frame_pairs_mem_span {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (Fr : OPFrame Q) :
    Fr.P.e ∈ Fr.span ∧ Fr.P.f ∈ Fr.span ∧ Fr.P'.e ∈ Fr.span ∧ Fr.P'.f ∈ Fr.span := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Frame.mem_span_iff_comb]
  · exact ⟨1, 0, 0, 0, by simp [Frame.e₁]⟩
  · exact ⟨0, 1, 0, 0, by simp [Frame.f₁]⟩
  · exact ⟨0, 0, 1, 0, by simp [Frame.e₂]⟩
  · exact ⟨0, 0, 0, 1, by simp [Frame.f₂]⟩

theorem hypPair_orth_of_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {S T : Submodule K V}
    (h : ∀ x ∈ S, ∀ y ∈ T, polar Q x y = 0) {A B : HypPair Q} (he : A.e ∈ S) (hf : A.f ∈ S)
    (he' : B.e ∈ T) (hf' : B.f ∈ T) : A.Orth B :=
  ⟨h _ he _ he', h _ he _ hf', h _ hf _ he', h _ hf _ hf'⟩

theorem hypPair_orth_symm {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {A B : HypPair Q} (h : A.Orth B) : B.Orth A :=
  ⟨by rw [polar_comm]; exact h.ee, by rw [polar_comm]; exact h.fe,
    by rw [polar_comm]; exact h.ef, by rw [polar_comm]; exact h.ff⟩

include hirr in
theorem false_of_three_frames_minus (hodd : Odd (Nat.card F))
    (F₁ F₂ F₃ : OPFrame (quadMinus 6 F b c))
    (h12 : ∀ x ∈ F₁.span, ∀ y ∈ F₂.span, polar (quadMinus 6 F b c) x y = 0)
    (h13 : ∀ x ∈ F₁.span, ∀ y ∈ F₃.span, polar (quadMinus 6 F b c) x y = 0)
    (h23 : ∀ x ∈ F₂.span, ∀ y ∈ F₃.span, polar (quadMinus 6 F b c) x y = 0) : False := by
  obtain ⟨a1, a2, a3, a4⟩ := frame_pairs_mem_span F₁
  obtain ⟨b1, b2, b3, b4⟩ := frame_pairs_mem_span F₂
  obtain ⟨c1, c2, c3, c4⟩ := frame_pairs_mem_span F₃
  let Pf : Fin 6 → HypPair (quadMinus 6 F b c) := ![F₁.P, F₁.P', F₂.P, F₂.P', F₃.P, F₃.P']
  have hlt : ∀ i j : Fin 6, i < j → (Pf i).Orth (Pf j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact F₁.orth
      | exact F₂.orth
      | exact F₃.orth
      | exact hypPair_orth_of_mem h12 ‹_› ‹_› ‹_› ‹_›
      | exact hypPair_orth_of_mem h13 ‹_› ‹_› ‹_› ‹_›
      | exact hypPair_orth_of_mem h23 ‹_› ‹_› ‹_› ‹_›
  refine false_of_pairs_minus hirr hodd (by norm_num : 1 ≤ 6) Pf fun i j hij => ?_
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact hypPair_orth_symm (hlt j i h)

end Minus

end CFSG.ClassicalInvolution.RouteD.TwinSmall
