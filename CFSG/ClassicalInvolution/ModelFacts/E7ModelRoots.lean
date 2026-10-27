module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Data
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduce
public import CFSG.LieType.Steinberg.Minuscule.Datum
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.ClassicalInvolution.Generic.Frame
public import CFSG.Timmesfeld.RankTwo.LevisExceptional
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcLevi
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Steinberg.Classical.SpinFrame
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
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.LieType.RootSystem CFSG.Timmesfeld

abbrev V7 : Type := Fin (Tag.rank .E7) → ℤ

@[expose] def e7Idx (n : ℕ) : Fin (Tag.rank .E7) := ⟨n % 7, Nat.mod_lt _ (by decide)⟩

@[expose] def wordAct (ω : List ℕ) (γ : V7) : V7 := ω.foldl (fun v i => reflect .E7 (e7Idx i) v) γ

@[expose] def thetaLit : V7 := ![2, 2, 3, 4, 3, 2, 1]

theorem thetaE7_eq : thetaE7 = thetaLit := by
  have h1 : ∀ j, iform thetaLit (Pi.single j 1) = if j.val = 0 then 1 else 0 := by
    decide +kernel
  set X := thetaE7 - thetaLit with hX
  have hXj : ∀ j, iform X (Pi.single j 1) = 0 := by
    intro j
    rw [hX, iform_sub_left, iform_thetaE7_single, h1]
    simp
  have hX0 : X = 0 := by
    by_contra hne
    have hpos := iform_self_pos hne
    rw [Levi.iform_eq_sum_single X X] at hpos
    simp only [hXj, mul_zero, Finset.sum_const_zero] at hpos
    exact lt_irrefl _ hpos
  exact sub_eq_zero.1 hX0

theorem wordAct_nil (γ : V7) : wordAct [] γ = γ := rfl

theorem wordAct_cons (i : ℕ) (ω : List ℕ) (γ : V7) :
    wordAct (i :: ω) γ = wordAct ω (reflect .E7 (e7Idx i) γ) := rfl

section Group

variable (F : Type) [Field F]

theorem refl_eq_reflect (i : Fin (Tag.rank .E7)) (γ : V7) :
    (CFSG.LieType.Steinberg.RootSystem.ofCartan (e7Datum F).isFiniteType
      (e7Datum F).divisible).refl i γ =
      reflect .E7 i γ := by
  have hs : weylAction (e7Datum F).isFiniteType
      ((coxeterMatrix (e7Datum F).isFiniteType).toCoxeterSystem.simple i) γ =
      (CFSG.LieType.Steinberg.RootSystem.ofCartan (e7Datum F).isFiniteType
        (e7Datum F).divisible).refl i γ := by
    rw [weylAction_simple]
    rfl
  rw [← hs]
  exact weylAction_simple_apply isFiniteType_cartan_E7 i γ

theorem exists_conj_rootGroup_wordAct (ω : List ℕ) :
    ∃ k : ↥(e7Data_valid.minGroup F), ∀ γ : V7, IsRoot .E7 γ →
      ((e7Datum F).rootGroup γ).map (MulAut.conj k).toMonoidHom =
        (e7Datum F).rootGroup (wordAct ω γ) := by
  induction ω with
  | nil =>
    refine ⟨1, fun γ _ => ?_⟩
    rw [wordAct_nil]
    ext x
    simp
  | cons i ω ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k * e7Data_valid.nm F (e7Idx i), fun γ hγ => ?_⟩
    have hγr : γ ∈ (e7Datum F).roots :=
      (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 F).2 hγ
    have h1 := CFSG.LieType.Steinberg.map_conj_rootGroup (e7Datum_isCTGroupDatum F) (e7Idx i) hγr
    rw [refl_eq_reflect] at h1
    have hcomp : (MulAut.conj (k * e7Data_valid.nm F (e7Idx i))).toMonoidHom =
        (MulAut.conj k).toMonoidHom.comp
          (MulAut.conj (e7Data_valid.nm F (e7Idx i))).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [wordAct_cons, ← hk _ (IsRoot.reflect _ hγ), ← h1, hcomp, Subgroup.map_map]

end Group

section PhaseOne

theorem phase_one_step : ∀ γ ∈ rootFinset .E7, γ (e7Idx 0) = 1 →
    (∀ j, 0 ≤ γ j) ∧ (γ = Pi.single (e7Idx 0) 1 ∨ ∃ i : Fin 7, i ≠ 0 ∧
      ∑ j, (reflect .E7 (e7Idx i) γ) j + 1 = ∑ j, γ j) := by
  decide +kernel

theorem reflect_apply_eq_of_ne (i : Fin (Tag.rank .E7)) {j : Fin (Tag.rank .E7)} (hij : j ≠ i)
    (γ : V7) : reflect .E7 i γ j = γ j := by
  simp [reflect, hij]

theorem exists_word_fixing_theta (γ : V7) (hγ : IsRoot .E7 γ) (h : γ (e7Idx 0) = 1) :
    ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧ wordAct ω γ = Pi.single (e7Idx 0) 1 := by
  suffices H : ∀ n : ℕ, ∀ γ : V7, IsRoot .E7 γ → γ (e7Idx 0) = 1 → (∑ j, γ j).toNat = n →
      ∃ ω : List ℕ, (∀ i ∈ ω, i % 7 ≠ 0) ∧ wordAct ω γ = Pi.single (e7Idx 0) 1 from
    H _ γ hγ h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hγ h hn
    obtain ⟨hpos, hcase⟩ := phase_one_step γ (mem_rootFinset.2 hγ) h
    rcases hcase with rfl | ⟨i, hi, hht⟩
    · exact ⟨[], by simp, rfl⟩
    · have hγ' : IsRoot .E7 (reflect .E7 (e7Idx i) γ) := IsRoot.reflect _ hγ
      have hi0 : e7Idx i ≠ e7Idx 0 := by
        intro he
        apply hi
        have := congrArg Fin.val he
        simp only [e7Idx] at this
        apply Fin.ext
        have h7 : i.val < 7 := i.2
        simpa [Nat.mod_eq_of_lt h7] using this
      have h' : reflect .E7 (e7Idx i) γ (e7Idx 0) = 1 := by
        rw [reflect_apply_eq_of_ne _ (Ne.symm hi0), h]
      have hpos1 : 1 ≤ ∑ j, γ j := by
        have : γ (e7Idx 0) ≤ ∑ j, γ j :=
          Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ _)
        omega
      obtain ⟨ω, hω, hact⟩ := ih ((∑ j, reflect .E7 (e7Idx i) γ j).toNat) (by omega)
        (reflect .E7 (e7Idx i) γ) hγ' h' rfl
      refine ⟨i.val :: ω, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · have h7 : i.val < 7 := i.2
          rw [Nat.mod_eq_of_lt h7]
          exact fun h0 => hi (Fin.ext h0)
        · exact hω k hk
      · rw [wordAct_cons]
        exact hact

end PhaseOne

section PhaseTwo

@[expose] def chainB : List ℕ → List V7 → V7 → V7 → Bool
  | [], [], v, t => decide (v = t)
  | i :: ω, w :: ws, v, t => decide (reflect .E7 (e7Idx i) v = w) && chainB ω ws w t
  | _, _, _, _ => false

theorem wordAct_eq_of_chainB : ∀ (ω : List ℕ) (ws : List V7) (v t : V7),
    chainB ω ws v t = true → wordAct ω v = t
  | [], [], v, t, h => by simpa [chainB, wordAct_nil] using h
  | [], _ :: _, v, t, h => by simp [chainB] at h
  | _ :: _, [], v, t, h => by simp [chainB] at h
  | i :: ω, w :: ws, v, t, h => by
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [wordAct_cons, h.1]
    exact wordAct_eq_of_chainB ω ws w t h.2

theorem edge_cases : ∀ a b : Fin 7, edgeE 7 a b →
    (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 3) ∨ (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 4) ∨ (a = 4 ∧ b = 5) ∨
      (a = 5 ∧ b = 6) := by
  decide

theorem exists_edge_word {a b : Fin 7} (hab : edgeE 7 a b) :
    ∃ ω : List ℕ,
      (wordAct ω (Pi.single (e7Idx a) 1) = thetaLit ∨
        wordAct ω (Pi.single (e7Idx a) 1) = -thetaLit) ∧
      (wordAct ω (Pi.single (e7Idx b) 1) = Pi.single (e7Idx 0) 1 ∨
        wordAct ω (Pi.single (e7Idx b) 1) = -(Pi.single (e7Idx 0) 1)) := by
  rcases edge_cases a b hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  ·
    refine ⟨[0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2], ?_, ?_⟩
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![-1, 0, 0, 0, 0, 0, 0], ![-1, 0, -1, 0, 0, 0, 0], ![-1, 0, -1, -1, 0, 0, 0],
          ![-1, -1, -1, -1, 0, 0, 0], ![-1, -1, -1, -1, -1, 0, 0], ![-1, -1, -1, -2, -1, 0, 0],
          ![-1, -1, -2, -2, -1, 0, 0], ![-1, -1, -2, -2, -1, 0, 0], ![-1, -1, -2, -2, -1, -1, 0],
          ![-1, -1, -2, -2, -2, -1, 0], ![-1, -1, -2, -3, -2, -1, 0],
          ![-1, -2, -2, -3, -2, -1, 0], ![-1, -2, -2, -3, -2, -1, 0],
          ![-1, -2, -2, -3, -2, -1, 0], ![-1, -2, -2, -3, -2, -1, -1],
          ![-1, -2, -2, -3, -2, -2, -1], ![-1, -2, -2, -3, -3, -2, -1],
          ![-1, -2, -2, -4, -3, -2, -1], ![-1, -2, -2, -4, -3, -2, -1],
          ![-1, -2, -3, -4, -3, -2, -1], ![-2, -2, -3, -4, -3, -2, -1],
          ![-2, -2, -3, -4, -3, -2, -1], ![-2, -2, -3, -4, -3, -2, -1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
          ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0],
          ![1, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
          ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0],
          ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0],
          ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
          ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel
  ·
    refine ⟨[1, 3, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2], ?_, ?_⟩
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0],
          ![-1, -1, -1, -1, 0, 0, 0], ![-1, -1, -1, -1, -1, 0, 0], ![-1, -1, -1, -2, -1, 0, 0],
          ![-1, -1, -1, -2, -1, 0, 0], ![-1, -1, -2, -2, -1, 0, 0], ![-1, -1, -2, -2, -1, 0, 0],
          ![-1, -1, -2, -2, -1, -1, 0], ![-1, -1, -2, -2, -2, -1, 0],
          ![-1, -1, -2, -3, -2, -1, 0], ![-1, -2, -2, -3, -2, -1, 0],
          ![-1, -2, -2, -3, -2, -1, 0], ![-1, -2, -2, -3, -2, -1, 0],
          ![-1, -2, -2, -3, -2, -1, -1], ![-1, -2, -2, -3, -2, -2, -1],
          ![-1, -2, -2, -3, -3, -2, -1], ![-1, -2, -2, -4, -3, -2, -1],
          ![-1, -2, -2, -4, -3, -2, -1], ![-1, -2, -3, -4, -3, -2, -1],
          ![-2, -2, -3, -4, -3, -2, -1], ![-2, -2, -3, -4, -3, -2, -1],
          ![-2, -2, -3, -4, -3, -2, -1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0],
          ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
          ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0],
          ![0, 1, 1, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, 1, 0, 1, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, 1, 0, 0, 0],
          ![1, 0, 1, 1, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel
  ·
    refine ⟨[0, 1, 3, 1, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2], ?_, ?_⟩
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
          ![1, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 2, 1, 0, 0],
          ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
          ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
          ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1],
          ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 1, 0, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0],
          ![0, 0, 0, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0],
          ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0],
          ![0, -1, -1, -1, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0],
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0],
          ![0, -1, 0, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0],
          ![-1, 0, -1, -1, 0, 0, 0], ![-1, 0, -1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel
  ·
    refine ⟨[1, 2, 0, 3, 2, 4, 3, 2, 5, 4, 3, 1, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2], ?_, ?_⟩
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0],
          ![1, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 0, 0, 0], ![1, 1, 1, 1, 1, 0, 0],
          ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 1, 0],
          ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 1],
          ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1],
          ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
          ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 1, 0, 0],
          ![0, 0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0, 0],
          ![0, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0],
          ![0, 0, -1, 0, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0], ![0, -1, -1, -1, 0, 0, 0],
          ![0, -1, 0, -1, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0],
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0],
          ![0, 0, 0, -1, 0, 0, 0], ![0, 0, -1, -1, 0, 0, 0], ![-1, 0, -1, -1, 0, 0, 0],
          ![-1, 0, -1, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel
  ·
    refine ⟨[3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 6, 5, 4, 3, 1, 2, 0, 3, 2], ?_, ?_⟩
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0, 0],
          ![1, 1, 1, 1, 1, 0, 0], ![1, 1, 1, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
          ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0], ![1, 1, 2, 2, 1, 0, 0],
          ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1],
          ![1, 2, 2, 3, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 2, 4, 3, 2, 1],
          ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1],
          ![2, 2, 3, 4, 3, 2, 1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0],
          ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0],
          ![0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 0],
          ![0, 1, 0, 1, 1, 0, 0], ![0, 1, 0, 1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0],
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0],
          ![0, -1, 0, 0, 0, 0, 0], ![0, -1, 0, -1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0],
          ![0, 0, -1, -1, 0, 0, 0], ![-1, 0, -1, -1, 0, 0, 0], ![-1, 0, -1, 0, 0, 0, 0],
          ![-1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel
  ·
    refine ⟨[4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 2, 0], ?_, ?_⟩
    · refine Or.inl (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1, 0], ![0, 1, 0, 1, 1, 1, 0],
          ![0, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1, 0], ![1, 1, 1, 2, 1, 1, 0],
          ![1, 1, 2, 2, 1, 1, 0], ![1, 1, 2, 2, 2, 1, 0], ![1, 1, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0], ![1, 2, 2, 3, 2, 1, 0],
          ![1, 2, 2, 3, 2, 1, 1], ![1, 2, 2, 3, 2, 2, 1], ![1, 2, 2, 3, 3, 2, 1],
          ![1, 2, 2, 4, 3, 2, 1], ![1, 2, 3, 4, 3, 2, 1], ![2, 2, 3, 4, 3, 2, 1]
        ] _ _ ?_)
      decide +kernel
    · refine Or.inr (wordAct_eq_of_chainB _
        [
          ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1],
          ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1],
          ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1],
          ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 1],
          ![0, 0, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 1, 1], ![1, 0, 1, 1, 1, 1, 1],
          ![1, 0, 1, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 0, 0],
          ![1, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0]
        ] _ _ ?_)
      decide +kernel

end PhaseTwo

section RankOne

theorem reflect_neg (i : Fin (Tag.rank .E7)) (v : V7) : reflect .E7 i (-v) = -reflect .E7 i v := by
  simp only [reflect, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_smul]
  abel

theorem wordAct_neg (ω : List ℕ) (v : V7) : wordAct ω (-v) = -wordAct ω v := by
  induction ω generalizing v with
  | nil => rfl
  | cons i ω ih => rw [wordAct_cons, wordAct_cons, reflect_neg, ih]

theorem wordAct_theta_of_ne_zero (ω : List ℕ) (hω : ∀ i ∈ ω, i % 7 ≠ 0) :
    wordAct ω thetaE7 = thetaE7 := by
  have hstep : ∀ i : Fin 7, i ≠ 0 → reflect .E7 (e7Idx i) thetaLit = thetaLit := by
    decide +kernel
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    rw [wordAct_cons, thetaE7_eq]
    have hi : i % 7 ≠ 0 := hω i (List.mem_cons_self ..)
    have h7 : (⟨i % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) ≠ 0 := fun h => hi (by
      simpa using congrArg Fin.val h)
    have := hstep ⟨i % 7, Nat.mod_lt _ (by decide)⟩ h7
    have e : e7Idx ((⟨i % 7, Nat.mod_lt _ (by decide)⟩ : Fin 7) : ℕ) = e7Idx i := by
      simp [e7Idx]
    rw [e] at this
    rw [this, ← thetaE7_eq]
    exact ih (fun k hk => hω k (List.mem_cons_of_mem _ hk))

variable (F : Type) [Field F]

theorem stdRankOne_neg (γ : V7) :
    stdRankOne (e7Datum F) (-γ) = stdRankOne (e7Datum F) γ := by
  unfold stdRankOne
  rw [neg_neg, sup_comm]

theorem exists_conj_stdRankOne_wordAct (ω : List ℕ) :
    ∃ k : ↥(e7Data_valid.minGroup F), ∀ γ : V7, IsRoot .E7 γ →
      conjSub k (stdRankOne (e7Datum F) γ) = stdRankOne (e7Datum F) (wordAct ω γ) := by
  obtain ⟨k, hk⟩ := exists_conj_rootGroup_wordAct F ω
  refine ⟨k, fun γ hγ => ?_⟩
  unfold conjSub stdRankOne
  rw [Subgroup.map_sup, hk γ hγ, hk (-γ) (CFSG.LieType.Chevalley.IsRoot.neg hγ), wordAct_neg]

theorem exists_conj_edge {a b : Fin 7} (hab : edgeE 7 a b) :
    ∃ k : ↥(e7Data_valid.minGroup F),
      conjSub k (rankOne (e7Datum F).rootGroup (e7Idx a)) = stdRankOne (e7Datum F) thetaE7 ∧
      conjSub k (rankOne (e7Datum F).rootGroup (e7Idx b)) =
        rankOne (e7Datum F).rootGroup (e7Idx 0) := by
  obtain ⟨ω, hωa, hωb⟩ := exists_edge_word hab
  obtain ⟨k, hk⟩ := exists_conj_stdRankOne_wordAct F ω
  refine ⟨k, ?_, ?_⟩
  · have := hk _ (isRoot_single .E7 (e7Idx a))
    change conjSub k (stdRankOne (e7Datum F) (Pi.single (e7Idx a) 1)) = _
    rw [this, thetaE7_eq]
    rcases hωa with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]
  · have := hk _ (isRoot_single .E7 (e7Idx b))
    change conjSub k (stdRankOne (e7Datum F) (Pi.single (e7Idx b) 1)) =
      stdRankOne (e7Datum F) (Pi.single (e7Idx 0) 1)
    rw [this]
    rcases hωb with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]

theorem iform_thetaE7_eq_coord (γ : V7) : iform thetaE7 γ = γ (e7Idx 0) := by
  rw [Levi.iform_eq_sum_single, Finset.sum_eq_single (e7Idx 0)]
  · rw [iform_thetaE7_single]
    simp [e7Idx]
  · intro j _ hj
    rw [iform_thetaE7_single]
    have : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa [e7Idx] using h))
    simp [this]
  · simp

theorem exists_conj_phase_one {γ : V7} (hγ : IsRoot .E7 γ)
    (h : iform thetaE7 γ = 1 ∨ iform thetaE7 γ = -1) :
    ∃ k : ↥(e7Data_valid.minGroup F),
      conjSub k (stdRankOne (e7Datum F) thetaE7) = stdRankOne (e7Datum F) thetaE7 ∧
      conjSub k (stdRankOne (e7Datum F) γ) = rankOne (e7Datum F).rootGroup (e7Idx 0) := by
  have key : ∀ γ : V7, IsRoot .E7 γ → iform thetaE7 γ = 1 →
      ∃ k : ↥(e7Data_valid.minGroup F),
        conjSub k (stdRankOne (e7Datum F) thetaE7) = stdRankOne (e7Datum F) thetaE7 ∧
        conjSub k (stdRankOne (e7Datum F) γ) = rankOne (e7Datum F).rootGroup (e7Idx 0) := by
    intro γ hγ h1
    rw [iform_thetaE7_eq_coord] at h1
    obtain ⟨ω, hω, hact⟩ := exists_word_fixing_theta γ hγ h1
    obtain ⟨k, hk⟩ := exists_conj_stdRankOne_wordAct F ω
    refine ⟨k, ?_, ?_⟩
    · rw [hk _ isRoot_thetaE7, wordAct_theta_of_ne_zero ω hω]
    · rw [hk _ hγ, hact]
      rfl
  rcases h with h | h
  · exact key γ hγ h
  · obtain ⟨k, hk1, hk2⟩ := key (-γ) (CFSG.LieType.Chevalley.IsRoot.neg hγ) (by
      rw [show (-γ : V7) = (-1 : ℤ) • γ by simp, iform_smul_right, h]; norm_num)
    exact ⟨k, hk1, by rw [← stdRankOne_neg]; exact hk2⟩

end RankOne

end CFSG.ClassicalInvolution.ModelFacts.E7Model
