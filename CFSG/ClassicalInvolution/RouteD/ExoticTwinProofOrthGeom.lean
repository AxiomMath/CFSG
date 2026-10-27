module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofBasic
public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.Transfer
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
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin not_commutes_of_nonorth)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Frames

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_perp_iff_four (F : OFrame Q) {x : V} :
    x ∈ F.perp ↔ polar Q x F.e₁ = 0 ∧ polar Q x F.f₁ = 0 ∧ polar Q x F.e₂ = 0 ∧
      polar Q x F.f₂ = 0 := by
  rw [Frame.mem_perp_iff, Frame.coords_apply]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp at h00 h01 h10 h11
    exact ⟨h11, h00, h10, h01⟩
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

theorem span_le_perp_iff (F₀ F₁ : OFrame Q) :
    F₁.span ≤ F₀.perp ↔ ∀ X Y, polar Q (F₀.incl X) (F₁.incl Y) = 0 := by
  constructor
  · intro h X Y
    rw [polar_comm]
    exact (Frame.mem_perp_iff_forall_incl F₀).mp (h ⟨Y, rfl⟩) X
  · intro h x hx
    obtain ⟨Y, rfl⟩ := hx
    rw [Frame.mem_perp_iff_forall_incl]
    intro X
    rw [polar_comm]
    exact h X Y

@[expose] noncomputable def sepPair (F : OFrame Q) (r : V) (hr : r ∈ F.perp) : HypPair Q :=
  HypPair.ofPolarEqOne (e := F.f₁) (h := F.e₁ + r) F.Q_f₁ (by
    have h := (mem_perp_iff_four F).mp hr
    rw [polar_add_right, F.polar_f₁_e₁, polar_comm, h.2.1]
    simp)

theorem sepPair_e (F : OFrame Q) {r : V} (hr : r ∈ F.perp) : (sepPair F r hr).e = F.f₁ := rfl

theorem sepPair_f (F : OFrame Q) {r : V} (hr : r ∈ F.perp) :
    (sepPair F r hr).f = F.e₁ + r - Q (F.e₁ + r) • F.f₁ := rfl

@[expose] noncomputable def sepFrame (F : OFrame Q) (r : V) (hr : r ∈ F.perp) : OFrame Q where
  P := sepPair F r hr
  P' := F.P'
  orth := by
    have h := (mem_perp_iff_four F).mp hr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [sepPair_e]; exact F.polar_f₁_e₂
    · rw [sepPair_e]; exact F.polar_f₁_f₂
    · rw [sepPair_f, polar_sub_left, polar_add_left, polar_smul_left_eq]
      show polar Q F.e₁ F.e₂ + polar Q r F.e₂ - Q (F.e₁ + r) * polar Q F.f₁ F.e₂ = 0
      rw [F.polar_e₁_e₂, h.2.2.1, F.polar_f₁_e₂]; ring
    · rw [sepPair_f, polar_sub_left, polar_add_left, polar_smul_left_eq]
      show polar Q F.e₁ F.f₂ + polar Q r F.f₂ - Q (F.e₁ + r) * polar Q F.f₁ F.f₂ = 0
      rw [F.polar_e₁_f₂, h.2.2.2, F.polar_f₁_f₂]; ring

end Frames

section Dim

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_aniso_perp (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V)
    (F₀ F₁ : OFrame Q) (h : F₁.span ≤ F₀.perp) : ∃ r ∈ F₀.perp ⊓ F₁.perp, Q r ≠ 0 := by
  have h1 : F₁.e₁ ∈ F₀.perp := h F₁.e₁_mem_span
  have h2 : F₁.f₁ ∈ F₀.perp := h F₁.f₁_mem_span
  have hnd₁ := (CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ F₀).inf_perp F₁.P h1 h2
  have he : F₁.P'.e ∈ F₀.perp ⊓ F₁.P.perp :=
    ⟨h F₁.e₂_mem_span, HypPair.mem_perp.mpr ⟨F₁.polar_e₁_e₂, F₁.polar_f₁_e₂⟩⟩
  have hf : F₁.P'.f ∈ F₀.perp ⊓ F₁.P.perp :=
    ⟨h F₁.f₂_mem_span, HypPair.mem_perp.mpr ⟨F₁.polar_e₁_f₂, F₁.polar_f₁_f₂⟩⟩
  have hnd₂ := hnd₁.inf_perp F₁.P' he hf
  let ℓ : V →ₗ[K] (Matrix (Fin 2) (Fin 2) K × (Fin 4 → K)) :=
    F₀.coords.prod (LinearMap.pi ![polarBilin Q F₁.e₁, polarBilin Q F₁.f₁, polarBilin Q F₁.e₂,
      polarBilin Q F₁.f₂])
  have hker : LinearMap.ker ℓ ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [Module.finrank_prod, Module.finrank_matrix, Module.finrank_fin_fun]
    simp
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' := LinearMap.mem_ker.mp hw
  have hw₀ : F₀.coords w = 0 := congrArg Prod.fst hw'
  have hw₁ : ∀ j : Fin 4, (ℓ w).2 j = 0 := fun j => by simp [hw']
  have c1 : polar Q F₁.e₁ w = 0 := hw₁ 0
  have c2 : polar Q F₁.f₁ w = 0 := hw₁ 1
  have c3 : polar Q F₁.e₂ w = 0 := hw₁ 2
  have c4 : polar Q F₁.f₂ w = 0 := hw₁ 3
  have hwW : w ∈ (F₀.perp ⊓ F₁.P.perp) ⊓ F₁.P'.perp :=
    ⟨⟨(Frame.mem_perp_iff F₀).mpr hw₀, HypPair.mem_perp.mpr ⟨c1, c2⟩⟩,
      HypPair.mem_perp.mpr ⟨c3, c4⟩⟩
  obtain ⟨y, hy, hwy⟩ := hnd₂.exists_polar_ne_zero hwW hw0
  have hQ' : ∃ r ∈ (F₀.perp ⊓ F₁.P.perp) ⊓ F₁.P'.perp, Q r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hwy
    have e1 := hcon w hwW
    have e2 := hcon y hy
    have e3 := hcon (w + y) (Submodule.add_mem _ hwW hy)
    have : polar Q w y = Q (w + y) - Q w - Q y := rfl
    rw [this, e1, e2, e3]
    ring
  obtain ⟨r, hr, hQr⟩ := hQ'
  refine ⟨r, ⟨hr.1.1, ?_⟩, hQr⟩
  show r ∈ F₁.perp
  rw [mem_perp_iff_four]
  have a1 := HypPair.mem_perp.mp hr.1.2
  have a2 := HypPair.mem_perp.mp hr.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [polar_comm]; exact a1.1
  · rw [polar_comm]; exact a1.2
  · rw [polar_comm]; exact a2.1
  · rw [polar_comm]; exact a2.2

end Dim

section Separate

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem sepFrame_span_le (F₀ F₁ : OFrame Q) (h : F₁.span ≤ F₀.perp) {r : V}
    (hr₀ : r ∈ F₀.perp) (hr₁ : r ∈ F₁.perp) : (sepFrame F₁ r hr₁).span ≤ F₀.perp := by
  rintro _ ⟨X, rfl⟩
  rw [Frame.incl_apply]
  have g1 : (sepFrame F₁ r hr₁).e₁ ∈ F₀.perp := h F₁.f₁_mem_span
  have g2 : (sepFrame F₁ r hr₁).f₁ ∈ F₀.perp := by
    show F₁.e₁ + r - Q (F₁.e₁ + r) • F₁.f₁ ∈ F₀.perp
    exact Submodule.sub_mem _ (Submodule.add_mem _ (h F₁.e₁_mem_span) hr₀)
      (Submodule.smul_mem _ _ (h F₁.f₁_mem_span))
  have g3 : (sepFrame F₁ r hr₁).e₂ ∈ F₀.perp := h F₁.e₂_mem_span
  have g4 : (sepFrame F₁ r hr₁).f₂ ∈ F₀.perp := h F₁.f₂_mem_span
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ g1) (Submodule.smul_mem _ _ g2)) (Submodule.smul_mem _ _ g3))
    (Submodule.smul_mem _ _ g4)

theorem Q_e_add (F : OFrame Q) {r : V} (hr : r ∈ F.perp) : Q (F.e₁ + r) = Q r := by
  have h := (mem_perp_iff_four F).mp hr
  rw [QuadraticMap.map_add Q, F.Q_e₁, polar_comm, h.1]
  ring

theorem polar_sepFrame (F : OFrame Q) {r : V} (hr : r ∈ F.perp) :
    polar Q F.e₁ (sepFrame F r hr).f₁ = - Q r := by
  have h := (mem_perp_iff_four F).mp hr
  show polar Q F.e₁ (F.e₁ + r - Q (F.e₁ + r) • F.f₁) = - Q r
  rw [polar_sub_right, polar_add_right, polar_smul_right_eq, F.polar_e₁_e₁, F.polar_e₁_f₁,
    polar_comm, h.1, Q_e_add F hr]
  ring

theorem sepFrame_ne_fixed (h2 : (2 : K) ≠ 0) (F₀ F₁ : OFrame Q) (h : F₁.span ≤ F₀.perp) {r : V}
    (hr₁ : r ∈ F₁.perp) (hQr : Q r ≠ 0) :
    (sepFrame F₁ r hr₁).La (-1) ≠ F₁.La (-1) ∧ (sepFrame F₁ r hr₁).La (-1) ≠ F₀.La (-1) := by
  constructor
  · intro heq
    have hs := Frame.span_eq_of_La_neg_one_eq h2 heq
    have hf : (sepFrame F₁ r hr₁).f₁ ∈ F₁.span := hs ▸ (sepFrame F₁ r hr₁).f₁_mem_span
    have hrs : r ∈ F₁.span := by
      have h1 : r = (sepFrame F₁ r hr₁).f₁ - F₁.e₁ + Q (F₁.e₁ + r) • F₁.f₁ := by
        show r = F₁.e₁ + r - Q (F₁.e₁ + r) • F₁.f₁ - F₁.e₁ + Q (F₁.e₁ + r) • F₁.f₁
        abel
      rw [h1]
      exact Submodule.add_mem _ (Submodule.sub_mem _ hf F₁.e₁_mem_span)
        (Submodule.smul_mem _ _ F₁.f₁_mem_span)
    have := Submodule.disjoint_def.mp F₁.isCompl_span_perp.disjoint r hrs hr₁
    exact hQr (by rw [this]; simp)
  · intro heq
    have hs := Frame.span_eq_of_La_neg_one_eq h2 heq
    have he : (sepFrame F₁ r hr₁).e₁ ∈ F₀.span := hs ▸ (sepFrame F₁ r hr₁).e₁_mem_span
    have hp : (sepFrame F₁ r hr₁).e₁ ∈ F₀.perp := h F₁.f₁_mem_span
    have h0 := Submodule.disjoint_def.mp F₀.isCompl_span_perp.disjoint _ he hp
    have h1 : polar Q F₁.f₁ F₁.e₁ = 1 := F₁.polar_f₁_e₁
    have h0' : F₁.f₁ = 0 := h0
    rw [h0', polar_zero_left] at h1
    exact zero_ne_one h1

end Separate

section Twin

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem span_le_perp_of_negSpace (hodd : Odd (Nat.card K)) {F₀ F₁ : OFrame Q}
    (h : ∀ x ∈ negSpace (F₀.La (-1)), ∀ y ∈ negSpace (F₁.La (-1)), polar Q x y = 0) :
    F₁.span ≤ F₀.perp := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rw [span_le_perp_iff]
  intro X Y
  exact h _ (by rw [negSpace_La_neg_one h2]; exact ⟨X, rfl⟩) _
    (by rw [negSpace_La_neg_one h2]; exact ⟨Y, rfl⟩)

theorem twin_same_involution (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) {R₀ R₁ : Subgroup (V ≃ₗ[K] V)} {i₀ i₁ : V ≃ₗ[K] V}
    (h₀ : IsFundamental Q R₀ i₀) (h₁ : IsFundamental Q R₁ i₁)
    (hP : IsTwinPair (fundSet Q) R₀ R₁) : i₁ = i₀ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rcases orth_or_twin hodd h₀ h₁ hP.2.2.2.1 with horth | heq
  swap
  · exact heq
  exfalso
  obtain ⟨F₀, rfl, rfl⟩ := h₀
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  have hsp : F₁.span ≤ F₀.perp := span_le_perp_of_negSpace hodd horth
  obtain ⟨r, hr, hQr⟩ := exists_aniso_perp hQ hdim F₀ F₁ hsp
  have hGsp := sepFrame_span_le F₀ F₁ hsp hr.1 hr.2
  obtain ⟨hne1, hne0⟩ := sepFrame_ne_fixed h2 F₀ F₁ hsp hr.2 hQr
  set G := sepFrame F₁ r hr.2 with hG
  have hS : G.La.range ∈ fundSet Q := ⟨_, IsFundamental.of_frame G⟩
  have hS0 : G.La.range ≠ F₀.La.range := fun e =>
    hne0 (IsFundamental.involution_unique hodd (IsFundamental.of_frame G)
      (by rw [e]; exact IsFundamental.of_frame F₀))
  have hS1 : G.La.range ≠ F₁.La.range := fun e =>
    hne1 (IsFundamental.involution_unique hodd (IsFundamental.of_frame G)
      (by rw [e]; exact IsFundamental.of_frame F₁))
  have horth0 := (span_le_perp_iff F₀ G).mp hGsp
  have hc0 : Commutes G.La.range F₀.La.range := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth (fun X Y => by rw [polar_comm]; exact horth0 Y X) A B
  have hc1 := (hP.2.2.2.2 _ hS hS0 hS1).mp hc0
  refine not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame G) hne1
    (x := F₁.e₁) (y := G.f₁) ?_ ?_ ?_ hc1.symm
  · rw [negSpace_La_neg_one h2]; exact F₁.e₁_mem_span
  · rw [negSpace_La_neg_one h2]; exact G.f₁_mem_span
  · rw [hG, polar_sepFrame F₁ hr.2]
    exact neg_ne_zero.mpr hQr

theorem commuting_same_involution (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V < 8)
    {R₀ R₁ : Subgroup (V ≃ₗ[K] V)} {i₀ i₁ : V ≃ₗ[K] V} (h₀ : IsFundamental Q R₀ i₀)
    (h₁ : IsFundamental Q R₁ i₁) (hc : Commutes R₀ R₁) : i₁ = i₀ := by
  rcases orth_or_twin hodd h₀ h₁ hc with horth | heq
  swap
  · exact heq
  exfalso
  obtain ⟨F₀, rfl, rfl⟩ := h₀
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  have hsp : F₁.span ≤ F₀.perp := span_le_perp_of_negSpace hodd horth
  have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₀
  have := Submodule.finrank_mono hsp
  rw [F₁.finrank_span] at this
  omega

omit [FiniteDimensional K V] in
theorem twinFamily_le_two (hodd : Odd (Nat.card K))
    (hsame : ∀ (R₀ R₁ : Subgroup (V ≃ₗ[K] V)) (i₀ i₁ : V ≃ₗ[K] V),
      IsTwinPair (fundSet Q) R₀ R₁ → IsFundamental Q R₀ i₀ → IsFundamental Q R₁ i₁ → i₁ = i₀)
    {a : ℕ} (h : TwinFamily (fundSet Q) a) : a ≤ 2 := by
  by_contra ha
  obtain ⟨R₀, R₁, R₂, hP01, hP02, hP12, -, -, -⟩ := h.exists_three (by omega)
  obtain ⟨i₀, h₀⟩ := hP01.1
  obtain ⟨i₁, h₁⟩ := hP01.2.1
  obtain ⟨i₂, h₂⟩ := hP02.2.1
  have e1 : i₁ = i₀ := hsame R₀ R₁ i₀ i₁ hP01 h₀ h₁
  have e2 : i₂ = i₀ := hsame R₀ R₂ i₀ i₂ hP02 h₀ h₂
  subst e1 e2
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd h₀
  rcases huniq R₁ h₁ with a1 | a1
  · exact hP01.2.2.1 a1.symm
  rcases huniq R₂ h₂ with a2 | a2
  · exact hP02.2.2.1 a2.symm
  exact hP12.2.2.1 (a1.trans a2.symm)

omit [Finite K] in
theorem false_of_orth_three (hdim : Module.finrank K V = 8) {F₀ F₁ F₂ : OFrame Q}
    (h01 : F₁.span ≤ F₀.perp) (h02 : F₂.span ≤ F₀.perp) (h12 : F₂.span ≤ F₁.perp) : False := by
  have hdisj : Disjoint F₁.span F₂.span := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    exact Submodule.disjoint_def.mp F₁.isCompl_span_perp.disjoint x hx1 (h12 hx2)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq F₁.span F₂.span
  rw [disjoint_iff.mp hdisj, finrank_bot, F₁.finrank_span, F₂.finrank_span] at hsum
  have hle : Module.finrank K ↥(F₁.span ⊔ F₂.span) ≤ Module.finrank K F₀.perp :=
    Submodule.finrank_mono (sup_le h01 h02)
  have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₀
  omega

theorem card_le_four_of_commuting (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8)
    {a : ℕ} (F : Fin a → Subgroup (V ≃ₗ[K] V)) (hF : ∀ k, F k ∈ fundSet Q)
    (hinj : Function.Injective F) (hcomm : ∀ i j, i ≠ j → Commutes (F i) (F j)) : a ≤ 4 := by
  classical
  have hF' : ∀ k, ∃ i, IsFundamental Q (F k) i := hF
  choose ι hι using hF'
  choose Fr hFr1 hFr2 using hι
  have hsp : ∀ j k, ι j ≠ ι k → (Fr k).span ≤ (Fr j).perp := by
    intro j k hne
    have hjk : j ≠ k := fun e => hne (by rw [e])
    rcases orth_or_twin hodd (show IsFundamental Q (F j) (ι j) from ⟨Fr j, hFr1 j, hFr2 j⟩)
      (show IsFundamental Q (F k) (ι k) from ⟨Fr k, hFr1 k, hFr2 k⟩) (hcomm j k hjk) with h | h
    · refine span_le_perp_of_negSpace hodd ?_
      rw [← hFr2 j, ← hFr2 k]
      exact h
    · exact absurd h.symm hne
  have hT : (Finset.univ.image ι).card ≤ 2 := by
    by_contra hT
    push Not at hT
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hT
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hz
    exact false_of_orth_three hdim (hsp j k hxy) (hsp j l hxz) (hsp k l hyz)
  have hfib : ∀ v ∈ Finset.univ.image ι, (Finset.univ.filter fun k => ι k = v).card ≤ 2 := by
    intro v hv
    obtain ⟨k₀, -, rfl⟩ := Finset.mem_image.mp hv
    have hfk : IsFundamental Q (F k₀) (ι k₀) := ⟨Fr k₀, hFr1 k₀, hFr2 k₀⟩
    have hnc := IsFundamental.ncard_eq_two hodd hfk
    have hfin : {L : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L (ι k₀)}.Finite :=
      Set.finite_of_ncard_ne_zero (by omega)
    calc (Finset.univ.filter fun k => ι k = ι k₀).card
        = ((Finset.univ.filter fun k => ι k = ι k₀).image F).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ = (((Finset.univ.filter fun k => ι k = ι k₀).image F : Finset _) :
            Set (Subgroup (V ≃ₗ[K] V))).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ {L : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L (ι k₀)}.ncard := by
          refine Set.ncard_le_ncard (fun L hL => ?_) hfin
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hL)
          have hk' : ι k = ι k₀ := (Finset.mem_filter.mp hk).2
          have : IsFundamental Q (F k) (ι k) := ⟨Fr k, hFr1 k, hFr2 k⟩
          rw [hk'] at this
          exact this
      _ = 2 := hnc
  have := Finset.card_le_mul_card_image (Finset.univ : Finset (Fin a)) 2 hfib
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem twinFamily_le_two_of_nine_le (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V) {a : ℕ}
    (h : TwinFamily (fundSet Q) a) : a ≤ 2 :=
  twinFamily_le_two hodd (fun _ _ _ _ hP h₀ h₁ => twin_same_involution hodd hQ hdim h₀ h₁ hP) h

theorem twinFamily_le_two_of_lt_eight (hodd : Odd (Nat.card K))
    (hdim : Module.finrank K V < 8) {a : ℕ} (h : TwinFamily (fundSet Q) a) : a ≤ 2 :=
  twinFamily_le_two hodd
    (fun _ _ _ _ hP h₀ h₁ => commuting_same_involution hodd hdim h₀ h₁ hP.2.2.2.1) h

theorem twinFamily_le_four_of_eight (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8)
    {a : ℕ} (h : TwinFamily (fundSet Q) a) : a ≤ 4 := by
  obtain ⟨F, hF, hinj, hcomm, -⟩ := h
  exact card_le_four_of_commuting hodd hdim F hF hinj hcomm

omit [FiniteDimensional K V] in
theorem twinFamily_le_two_of_noOrth (hodd : Odd (Nat.card K))
    (hNo : ∀ F₀ F₁ : OFrame Q, F₁.span ≤ F₀.perp → False) {a : ℕ}
    (h : TwinFamily (fundSet Q) a) : a ≤ 2 := by
  refine twinFamily_le_two hodd (fun R₀ R₁ i₀ i₁ hP h₀ h₁ => ?_) h
  rcases orth_or_twin hodd h₀ h₁ hP.2.2.2.1 with horth | heq
  · exfalso
    obtain ⟨F₀, rfl, rfl⟩ := h₀
    obtain ⟨F₁, rfl, rfl⟩ := h₁
    exact hNo F₀ F₁ (span_le_perp_of_negSpace hodd horth)
  · exact heq

end Twin

end CFSG.ClassicalInvolution.RouteD.Exotic
