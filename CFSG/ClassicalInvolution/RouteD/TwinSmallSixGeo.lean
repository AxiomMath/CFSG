module

public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixAlg
public import CFSG.ClassicalInvolution.RouteD.TwinSmallModel
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinFrame
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
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusFix
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

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Geo

variable {F : Type} [Field F] [Finite F] {b c : F}

structure SixSigns (b c : F) (g : Vm 6 F ≃ₗ[F] Vm 6 F) (ε₁ εM : F) : Prop where
  gO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 6 F b c)
  g2 : g * g = 1
  sq₁ : ε₁ * ε₁ = 1
  sqM : εM * εM = 1
  p1 : ∀ k : Fin (6 - 1), k.val = 1 ∨ k.val = 2 → ∀ u, g (minusVec 6 k u) = ε₁ • minusVec 6 k u
  p3 : ∀ k : Fin (6 - 1), k.val = 3 ∨ k.val = 4 → ∀ u, g (minusVec 6 k u) = εM • minusVec 6 k u

@[expose] def NormR0 (b c : F) (g : Vm 6 F ≃ₗ[F] Vm 6 F) : Prop :=
  ∀ y ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false,
    ∃ y' ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false,
      g * spinAction (quadMinus 6 F b c) y = spinAction (quadMinus 6 F b c) y' * g

@[expose] def MovR0 (b c : F) (g : Vm 6 F ≃ₗ[F] Vm 6 F) : Prop :=
  ∃ y ∈ rootSL2 (minusHyp 6 b c) 0 1 (by omega) (by omega) (by omega) true false,
    g * spinAction (quadMinus 6 F b c) y ≠ spinAction (quadMinus 6 F b c) y * g

theorem geo_H0 (hodd : Odd (Nat.card F)) {g : Vm 6 F ≃ₗ[F] Vm 6 F} {ε₁ εM : F}
    (S : SixSigns b c g ε₁ εM) (hn : NormR0 b c g) (hm : MovR0 b c g) :
    ∃ a : F, (a = 1 ∨ a = -1) ∧ a ≠ ε₁ ∧
      ∀ u, g (minusVec 6 ⟨0, by omega⟩ u) = a • minusVec 6 ⟨0, by omega⟩ u := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set F₀ := minusHyp 6 b c with hF₀
  have hij : (⟨0, by omega⟩ : Fin (6 - 1)) ≠ ⟨1, by omega⟩ := by simp
  let fr : OPFrame (quadMinus 6 F b c) := F₀.toFrame hij true false
  have hmapR : (rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
      (spinAction (quadMinus 6 F b c)) = fr.La.range := map_longSL2_range F₀ hij true false
  have hgg : ∀ v, g (g v) = v := fun v => by
    have := LinearEquiv.congr_fun S.g2 v
    simpa using this
  have hcomm₀ : g * fr.La (-1) = fr.La (-1) * g := by
    have hmem : fr.La (-1) ∈ (rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
        (spinAction (quadMinus 6 F b c)) := hmapR ▸ ⟨-1, rfl⟩
    obtain ⟨r₀, hr₀, hr₀e⟩ := hmem
    obtain ⟨y', hy', hcomm⟩ := hn r₀ hr₀
    rw [hr₀e] at hcomm
    have hy'mem : spinAction (quadMinus 6 F b c) y' ∈ fr.La.range := hmapR ▸ ⟨y', hy', rfl⟩
    have hconj : spinAction (quadMinus 6 F b c) y' = g * fr.La (-1) * g := by
      calc spinAction (quadMinus 6 F b c) y' = (spinAction (quadMinus 6 F b c) y' * g) * g := by
            rw [mul_assoc, S.g2, mul_one]
        _ = g * fr.La (-1) * g := by rw [← hcomm]
    have hi2 : fr.La (-1) * fr.La (-1) = 1 := fr.La_neg_one_mul_self
    have hsq : spinAction (quadMinus 6 F b c) y' ^ 2 = 1 := by
      rw [hconj, pow_two]
      calc g * fr.La (-1) * g * (g * fr.La (-1) * g)
          = g * fr.La (-1) * (g * g) * fr.La (-1) * g := by group
        _ = g * (fr.La (-1) * fr.La (-1)) * g := by rw [S.g2]; group
        _ = 1 := by rw [hi2, mul_one, S.g2]
    have hne : spinAction (quadMinus 6 F b c) y' ≠ 1 := by
      intro h1
      rw [hconj] at h1
      have h3 : fr.La (-1) = 1 := by
        calc fr.La (-1) = g * (g * fr.La (-1) * g) * g := by
              calc fr.La (-1) = (g * g) * fr.La (-1) * (g * g) := by rw [S.g2]; group
                _ = g * (g * fr.La (-1) * g) * g := by group
          _ = g * 1 * g := by rw [h1]
          _ = 1 := by rw [mul_one, S.g2]
      exact IsFundamental.ne_one hodd (IsFundamental.of_frame fr) h3
    have hord := orderOf_eq_prime hsq hne
    have heq := (IsFundamental.of_frame fr).eq_of_orderOf_eq_two hodd hy'mem hord
    rw [heq] at hconj
    calc g * fr.La (-1) = (g * fr.La (-1) * g) * g := by rw [mul_assoc, mul_assoc, S.g2, mul_one]
      _ = fr.La (-1) * g := by rw [← hconj]
  have hspan : ∀ x ∈ fr.span, g x ∈ fr.span := by
    intro x hx
    rw [Frame.mem_span_iff_inv fr h2] at hx ⊢
    have h1 : fr.La (-1) (g x) = g (fr.La (-1) x) := by
      have := LinearEquiv.congr_fun hcomm₀ x
      simpa using this.symm
    rw [h1, hx, map_neg]
  have h0lt : (0 : ℕ) < 6 - 1 := by omega
  have h1lt : (1 : ℕ) < 6 - 1 := by omega
  have hpe1 : ∀ u, g (minusVec 6 ⟨1, h1lt⟩ u) = ε₁ • minusVec 6 ⟨1, h1lt⟩ u := fun u =>
    S.p1 ⟨1, h1lt⟩ (Or.inl rfl) u
  have hpol : ∀ v : Vm 6 F, ∀ u : Bool,
      polar (quadMinus 6 F b c) (g v) (minusVec 6 ⟨1, h1lt⟩ u) =
        ε₁ * polar (quadMinus 6 F b c) v (minusVec 6 ⟨1, h1lt⟩ u) :=
    fun v u => polarApplyOfEig6 S.gO S.sq₁ (hpe1 u) v
  have hpolzero : ∀ (u u' : Bool), polar (quadMinus 6 F b c) (minusVec 6 ⟨0, h0lt⟩ u)
      (minusVec 6 ⟨1, h1lt⟩ u') = 0 := fun u u' => by
    rw [polar_minusVec_minusVec 6 b c]
    simp
  have hdecomp : ∀ v ∈ fr.span, (∀ u, polar (quadMinus 6 F b c) v (minusVec 6 ⟨1, h1lt⟩ u) = 0) →
      ∃ α β : F, v = α • minusVec 6 ⟨0, h0lt⟩ true + β • minusVec 6 ⟨0, h0lt⟩ false := by
    intro v hv hperp
    obtain ⟨α, β, γ, δ, hvd⟩ := (Frame.mem_span_iff_comb fr).mp hv
    have e₁ : fr.e₁ = minusVec 6 ⟨0, h0lt⟩ true := rfl
    have f₁ : fr.f₁ = minusVec 6 ⟨0, h0lt⟩ false := rfl
    have e₂ : fr.e₂ = minusVec 6 ⟨1, h1lt⟩ false := rfl
    have f₂ : fr.f₂ = minusVec 6 ⟨1, h1lt⟩ true := rfl
    rw [e₁, f₁, e₂, f₂] at hvd
    refine ⟨α, β, ?_⟩
    have hγ := hperp true
    have hδ := hperp false
    rw [hvd] at hγ hδ
    simp only [polar_add_left, polar_smul_left, smul_eq_mul, hpolzero,
      polar_minusVec_minusVec 6 b c] at hγ hδ
    simp at hγ hδ
    rw [hvd, hγ, hδ]
    simp
  have hperp0 : ∀ (u : Bool) (w : Vm 6 F), w = minusVec 6 ⟨0, h0lt⟩ u → ∀ u',
      polar (quadMinus 6 F b c) (g w) (minusVec 6 ⟨1, h1lt⟩ u') = 0 := fun u w hw u' => by
    rw [hpol w u', hw, hpolzero, mul_zero]
  obtain ⟨α, β, hge⟩ := hdecomp (g (minusVec 6 ⟨0, h0lt⟩ true))
    (hspan _ (Frame.e₁_mem_span fr)) (hperp0 true _ rfl)
  obtain ⟨γ, δ, hgf⟩ := hdecomp (g (minusVec 6 ⟨0, h0lt⟩ false))
    (hspan _ (Frame.f₁_mem_span fr)) (hperp0 false _ rfl)
  have hef : polar (quadMinus 6 F b c) (minusVec 6 ⟨0, h0lt⟩ true) (minusVec 6 ⟨0, h0lt⟩ false) =
      1 := by
    rw [polar_minusVec_minusVec 6 b c]
    simp
  obtain ⟨R1, -, R3, R4, R5, R6, -⟩ := hypRel6 S.gO S.g2 (quadMinus_minusVec 6 b c _ true)
    (quadMinus_minusVec 6 b c _ false) hef hge hgf
  rcases h0Alg6 h2 R1 R3 R4 R5 R6 with ⟨hβ, hγ, hδ, hα⟩ | ⟨hα0, hδ0, hβ0, hβγ⟩
  · refine ⟨α, hα, fun hαε => ?_, fun u => ?_⟩
    ·
      subst hαε
      have hsc : ∀ Y, g (fr.incl Y) = α • fr.incl Y := by
        refine incl_smul_of_vectors fr ?_ ?_ ?_ ?_
        · change g (minusVec 6 ⟨0, h0lt⟩ true) = _ • minusVec 6 ⟨0, h0lt⟩ true
          rw [hge, hβ]
          simp
        · change g (minusVec 6 ⟨0, h0lt⟩ false) = _ • minusVec 6 ⟨0, h0lt⟩ false
          rw [hgf, hγ, hδ]
          simp
        · exact hpe1 false
        · exact hpe1 true
      obtain ⟨y, hy, hne⟩ := hm
      have hymem : spinAction (quadMinus 6 F b c) y ∈ fr.La.range := hmapR ▸ ⟨y, hy, rfl⟩
      obtain ⟨A, hA⟩ := hymem
      apply hne
      rw [← hA]
      exact comm_La_of_smul fr S.gO S.sq₁ hsc A
    · cases u
      · change g (minusVec 6 ⟨0, h0lt⟩ false) = _ • minusVec 6 ⟨0, h0lt⟩ false
        rw [hgf, hγ, hδ]
        simp
      · change g (minusVec 6 ⟨0, h0lt⟩ true) = _ • minusVec 6 ⟨0, h0lt⟩ true
        rw [hge, hβ]
        simp
  · exfalso
    subst hα0 hδ0
    simp only [zero_smul, zero_add, add_zero] at hge hgf
    exact notAntidiag6 S.g2 h0lt h1lt (by simp) S.sq₁ hβ0 hβγ hge hgf hpe1 hn

noncomputable def aLin6 (F : Type) [Field F] : (Fin 2 → F) →ₗ[F] Vm 6 F where
  toFun := planeVec 6
  map_add' := planeVec_add 6
  map_smul' := fun r w => planeVec_smul 6 r w

def Yp6 (b c : F) : Submodule F (Vm 6 F) where
  carrier := {v | ∀ k : Fin (6 - 1), 1 ≤ k.val → ∀ u,
    polar (quadMinus 6 F b c) v (minusVec 6 k u) = 0}
  add_mem' := fun {x y} hx hy k hk u => by rw [polar_add_left, hx k hk u, hy k hk u, add_zero]
  zero_mem' := fun k _ u => by rw [polar_zero_left]
  smul_mem' := fun r x hx k hk u => by rw [polar_smul_left, hx k hk u, smul_zero]

omit [Finite F] in
theorem Yp6_le (b c : F) :
    Yp6 b c ≤ Submodule.span F (Set.range ![minusVec 6 (K := F) ⟨0, by omega⟩ true,
      minusVec 6 (K := F) ⟨0, by omega⟩ false]) ⊔ LinearMap.range (aLin6 F) := by
  intro v hv
  have h0lt : (0 : ℕ) < 6 - 1 := by omega
  set e0 := minusVec 6 (K := F) ⟨0, h0lt⟩ true with he0
  set f0 := minusVec 6 (K := F) ⟨0, h0lt⟩ false with hf0
  set w : Vm 6 F := polar (quadMinus 6 F b c) v f0 • e0 + polar (quadMinus 6 F b c) v e0 • f0
    with hw
  have hperp : ∀ k r, polar (quadMinus 6 F b c) (v - w) (minusVec 6 k r) = 0 := by
    intro k r
    by_cases hk : k.val = 0
    · have hk0 : k = ⟨0, h0lt⟩ := Fin.ext hk
      subst hk0
      cases r
      · simp only [polar_sub_left, hw, polar_add_left, polar_smul_left, he0, hf0, smul_eq_mul,
          polar_minusVec_minusVec 6 b c]
        simp
      · simp only [polar_sub_left, hw, polar_add_left, polar_smul_left, he0, hf0, smul_eq_mul,
          polar_minusVec_minusVec 6 b c]
        simp
    · have hv' := hv k (by omega) r
      have hk0 : (⟨0, h0lt⟩ : Fin (6 - 1)) ≠ k := fun h => hk (by rw [← h])
      simp only [polar_sub_left, hv', hw, polar_add_left, polar_smul_left, he0, hf0, smul_eq_mul,
        polar_minusVec_minusVec 6 b c, hk0]
      simp
  have hpl := eq_planeVec_of_polar_minusVec 6 b c hperp
  have hvw : v = w + (v - w) := by abel
  rw [hvw]
  refine Submodule.add_mem_sup (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨0, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))) ?_
  exact ⟨_, hpl.symm⟩

omit [Finite F] in
theorem finrank_Yp6_le (b c : F) : Module.finrank F (Yp6 b c) ≤ 4 := by
  have h0lt : (0 : ℕ) < 6 - 1 := by omega
  have h1 : Module.finrank F (Submodule.span F (Set.range ![minusVec 6 (K := F) ⟨0, h0lt⟩ true,
      minusVec 6 (K := F) ⟨0, h0lt⟩ false])) ≤ 2 := by
    refine (finrank_range_le_card ![minusVec 6 (K := F) ⟨0, h0lt⟩ true,
      minusVec 6 (K := F) ⟨0, h0lt⟩ false]).trans ?_
    simp
  have h2 : Module.finrank F (LinearMap.range (aLin6 F)) ≤ 2 := by
    refine (LinearMap.finrank_range_le (aLin6 F)).trans ?_
    simp
  have hmono := Submodule.finrank_mono (Yp6_le b c)
  have hsum := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span F
    (Set.range ![minusVec 6 (K := F) ⟨0, h0lt⟩ true, minusVec 6 (K := F) ⟨0, h0lt⟩ false]))
    (LinearMap.range (aLin6 F))
  omega

omit [Finite F] in
theorem pm_eq_of_ne (h2 : (2 : F) ≠ 0) {x y z : F} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (hz : z = 1 ∨ z = -1) (hxy : x ≠ y) (hxz : x ≠ z) : y = z := by
  have hne : (1 : F) ≠ -1 := fun h => h2 (by linear_combination h)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
    simp_all

theorem geo_ties (hodd : Odd (Nat.card F)) {g : Vm 6 F ≃ₗ[F] Vm 6 F} {ε₁ εM a : F}
    (S : SixSigns b c g ε₁ εM) (ha1 : a = 1 ∨ a = -1) (haε : a ≠ ε₁) (haM : a ≠ εM)
    (hg0 : ∀ u, g (minusVec 6 ⟨0, by omega⟩ u) = a • minusVec 6 ⟨0, by omega⟩ u)
    (T : Submodule F (Vm 6 F)) (hT6 : 6 ≤ Module.finrank F T) {s : F}
    (hTg : ∀ x ∈ T, g x = s • x)
    (hTp : ∀ x ∈ T, ∀ k : Fin (6 - 1), (k.val = 1 ∨ k.val = 2) → ∀ u,
      polar (quadMinus 6 F b c) x (minusVec 6 k u) = 0) :
    εM = ε₁ ∧ ∀ w, g (planeVec 6 w) = ε₁ • planeVec 6 w := by
  classical
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have e1 : ε₁ = 1 ∨ ε₁ = -1 := mul_self_eq_one_iff.mp S.sq₁
  have eM : εM = 1 ∨ εM = -1 := mul_self_eq_one_iff.mp S.sqM
  have hεM : εM = ε₁ := (pm_eq_of_ne h2 ha1 e1 eM haε haM).symm
  have h0lt : (0 : ℕ) < 6 - 1 := by omega
  have h3lt : (3 : ℕ) < 6 - 1 := by omega
  have h4lt : (4 : ℕ) < 6 - 1 := by omega
  have haa : a * a = 1 := by rcases ha1 with rfl | rfl <;> ring
  have hsM : s = εM := by
    by_contra hsne
    have hTY : T ≤ Yp6 b c := by
      intro x hx k hk u
      by_cases hk12 : k.val = 1 ∨ k.val = 2
      · exact hTp x hx k hk12 u
      · have hk34 : k.val = 3 ∨ k.val = 4 := by omega
        have h := polarApplyOfEig6 S.gO S.sqM (S.p3 k hk34 u) x
        rw [hTg x hx, polar_smul_left, smul_eq_mul] at h
        have h0 : (s - εM) * polar (quadMinus 6 F b c) x (minusVec 6 k u) = 0 := by
          linear_combination h
        rcases mul_eq_zero.mp h0 with h' | h'
        · exact absurd (sub_eq_zero.mp h') hsne
        · exact h'
    have := Submodule.finrank_mono hTY
    have := finrank_Yp6_le b c
    omega
  set e3 := minusVec 6 (K := F) ⟨3, h3lt⟩ true with he3
  set f3 := minusVec 6 (K := F) ⟨3, h3lt⟩ false with hf3
  set e4 := minusVec 6 (K := F) ⟨4, h4lt⟩ true with he4
  set f4 := minusVec 6 (K := F) ⟨4, h4lt⟩ false with hf4
  let Msp : Submodule F (Vm 6 F) := Submodule.span F (Set.range ![e3, f3, e4, f4])
  let Esp : Submodule F (Vm 6 F) :=
    Module.End.eigenspace ((g : Vm 6 F ≃ₗ[F] Vm 6 F) : Module.End F (Vm 6 F)) εM
  have hmemE : ∀ v, v ∈ Esp ↔ g v = εM • v := fun v => by
    rw [Module.End.mem_eigenspace_iff]
    rfl
  have hMdim : Module.finrank F Msp ≤ 4 := by
    refine (finrank_range_le_card ![e3, f3, e4, f4]).trans ?_
    simp
  let pm : Vm 6 F → Vm 6 F := fun v =>
    polar (quadMinus 6 F b c) v f3 • e3 + polar (quadMinus 6 F b c) v e3 • f3 +
      polar (quadMinus 6 F b c) v f4 • e4 + polar (quadMinus 6 F b c) v e4 • f4
  have hpm_mem : ∀ v, pm v ∈ Msp := by
    intro v
    refine add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))) (Submodule.smul_mem _ _
      (Submodule.subset_span ⟨2, rfl⟩))) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨3, rfl⟩))
  have hdiff : ∀ x ∈ T, x - pm x ∈ Esp ⊓ Yp6 b c := by
    intro x hx
    refine ⟨(hmemE _).mpr ?_, ?_⟩
    · have h3t : ∀ u, g (minusVec 6 ⟨3, h3lt⟩ u) = εM • minusVec 6 ⟨3, h3lt⟩ u :=
        fun u => S.p3 _ (Or.inl rfl) u
      have h4t : ∀ u, g (minusVec 6 ⟨4, h4lt⟩ u) = εM • minusVec 6 ⟨4, h4lt⟩ u :=
        fun u => S.p3 _ (Or.inr rfl) u
      simp only [pm, map_sub, map_add, map_smul, hTg x hx, hsM, he3, hf3, he4, hf4, h3t, h4t]
      module
    · intro k hk u
      by_cases hk12 : k.val = 1 ∨ k.val = 2
      · have hp := hTp x hx k hk12 u
        have hk3 : (⟨3, h3lt⟩ : Fin (6 - 1)) ≠ k := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        have hk4 : (⟨4, h4lt⟩ : Fin (6 - 1)) ≠ k := fun h => by
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [pm, polar_sub_left, polar_add_left, polar_smul_left, hp, he3, hf3, he4, hf4,
          polar_minusVec_minusVec 6 b c, hk3, hk4, smul_eq_mul]
        simp
      · have hk34 : k.val = 3 ∨ k.val = 4 := by omega
        have hk' : k = ⟨3, h3lt⟩ ∨ k = ⟨4, h4lt⟩ := by
          rcases hk34 with h | h
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Fin.ext h)
        have h34 : (⟨3, h3lt⟩ : Fin (6 - 1)) ≠ ⟨4, h4lt⟩ := by simp [Fin.ext_iff]
        rcases hk' with rfl | rfl <;> cases u <;>
          simp only [pm, polar_sub_left, polar_add_left, polar_smul_left, he3, hf3, he4, hf4,
            polar_minusVec_minusVec 6 b c, smul_eq_mul] <;> simp
  have hTsub : T ≤ Msp ⊔ (Esp ⊓ Yp6 b c) := by
    intro x hx
    have : x = pm x + (x - pm x) := by abel
    rw [this]
    exact Submodule.add_mem_sup (hpm_mem x) (hdiff x hx)
  have hdim2 : 2 ≤ Module.finrank F ↥(Esp ⊓ Yp6 b c) := by
    have h1 := Submodule.finrank_mono hTsub
    have h2' := Submodule.finrank_add_le_finrank_add_finrank Msp (Esp ⊓ Yp6 b c)
    omega
  have hle : Esp ⊓ Yp6 b c ≤ LinearMap.range (aLin6 F) := by
    rintro y ⟨hyE, hyY⟩
    have hyg : g y = εM • y := (hmemE y).mp hyE
    have hpol0 : ∀ u, polar (quadMinus 6 F b c) y (minusVec 6 ⟨0, h0lt⟩ u) = 0 := by
      intro u
      have h := polarApplyOfEig6 S.gO haa (hg0 u) y
      rw [hyg, polar_smul_left, smul_eq_mul] at h
      have h0 : (εM - a) * polar (quadMinus 6 F b c) y (minusVec 6 ⟨0, h0lt⟩ u) = 0 := by
        linear_combination h
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd (sub_eq_zero.mp h').symm haM
      · exact h'
    have hperp : ∀ k r, polar (quadMinus 6 F b c) y (minusVec 6 k r) = 0 := by
      intro k r
      by_cases hk : k.val = 0
      · have : k = ⟨0, h0lt⟩ := Fin.ext hk
        subst this
        exact hpol0 r
      · exact hyY k (by omega) r
    exact ⟨_, (eq_planeVec_of_polar_minusVec 6 b c hperp).symm⟩
  have h2dim : Module.finrank F (LinearMap.range (aLin6 F)) ≤ 2 := by
    refine (LinearMap.finrank_range_le (aLin6 F)).trans ?_
    simp
  have hEq : Esp ⊓ Yp6 b c = LinearMap.range (aLin6 F) :=
    Submodule.eq_of_le_of_finrank_le hle (by omega)
  refine ⟨hεM, fun w => ?_⟩
  have hmem : planeVec 6 w ∈ Esp ⊓ Yp6 b c := by
    rw [hEq]
    exact ⟨w, rfl⟩
  have hg : g (planeVec 6 w) = εM • planeVec 6 w := (hmemE _).mp hmem.1
  rw [hg, hεM]

end Geo

end CFSG.ClassicalInvolution.RouteD.TwinSmall
