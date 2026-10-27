module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer
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

namespace CFSG.ClassicalInvolution.RouteD.TWS6

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open scoped commutatorElement MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Comm

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] [FiniteDimensional K V] in
theorem exists_four_pairs_of_swap (F₂ : OFrame Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hsp : ∀ x ∈ F₂.span, g x ∈ F₂.perp) :
    ∃ P : Fin 4 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) := by
  have e1 : F₂.e₁ ∈ F₂.span := ⟨!![1, 0; 0, 0], by simp [F₂.incl_apply]⟩
  have f1 : F₂.f₁ ∈ F₂.span := ⟨!![0, 0; 0, 1], by simp [F₂.incl_apply]⟩
  have e2 : F₂.e₂ ∈ F₂.span := ⟨!![0, -1; 0, 0], by simp [F₂.incl_apply]⟩
  have f2 : F₂.f₂ ∈ F₂.span := ⟨!![0, 0; 1, 0], by simp [F₂.incl_apply]⟩
  have hor : ∀ {x y : V}, x ∈ F₂.span → y ∈ F₂.perp → polar Q x y = 0 := fun hx hy =>
    CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.polar_eq_zero_of_mem_perp hx hy
  have hQ : ∀ x, Q (g x) = Q x := fun x => map_of_mem hg x
  have hpol : ∀ x y, polar Q (g x) (g y) = polar Q x y := fun x y => polar_map_of_mem hg x y
  let P₃ : HypPair Q := ⟨g F₂.e₁, g F₂.f₁, by rw [hQ, F₂.Q_e₁], by rw [hQ, F₂.Q_f₁],
    by rw [hpol, F₂.polar_e₁_f₁]⟩
  let P₄ : HypPair Q := ⟨g F₂.e₂, g F₂.f₂, by rw [hQ, F₂.Q_e₂], by rw [hQ, F₂.Q_f₂],
    by rw [hpol, F₂.polar_e₂_f₂]⟩
  refine ⟨![F₂.P, F₂.P', P₃, P₄], ?_⟩
  have o12 : F₂.P.Orth F₂.P' := F₂.orth
  have o13 : F₂.P.Orth P₃ :=
    ⟨hor e1 (hsp _ e1), hor e1 (hsp _ f1), hor f1 (hsp _ e1), hor f1 (hsp _ f1)⟩
  have o14 : F₂.P.Orth P₄ :=
    ⟨hor e1 (hsp _ e2), hor e1 (hsp _ f2), hor f1 (hsp _ e2), hor f1 (hsp _ f2)⟩
  have o23 : F₂.P'.Orth P₃ :=
    ⟨hor e2 (hsp _ e1), hor e2 (hsp _ f1), hor f2 (hsp _ e1), hor f2 (hsp _ f1)⟩
  have o24 : F₂.P'.Orth P₄ :=
    ⟨hor e2 (hsp _ e2), hor e2 (hsp _ f2), hor f2 (hsp _ e2), hor f2 (hsp _ f2)⟩
  have o34 : P₃.Orth P₄ :=
    ⟨by show polar Q (g F₂.e₁) (g F₂.e₂) = 0; rw [hpol]; exact F₂.orth.ee,
      by show polar Q (g F₂.e₁) (g F₂.f₂) = 0; rw [hpol]; exact F₂.orth.ef,
      by show polar Q (g F₂.f₁) (g F₂.e₂) = 0; rw [hpol]; exact F₂.orth.fe,
      by show polar Q (g F₂.f₁) (g F₂.f₂) = 0; rw [hpol]; exact F₂.orth.ff⟩
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact o12
  · exact o13
  · exact o14
  · exact o12.symm
  · exact absurd rfl hij
  · exact o23
  · exact o24
  · exact o13.symm
  · exact o23.symm
  · exact absurd rfl hij
  · exact o34
  · exact o14.symm
  · exact o24.symm
  · exact o34.symm
  · exact absurd rfl hij

theorem commute_of_commutator_mem_scalars_small (hodd : Odd (Nat.card K))
    (h8 : Module.finrank K V = 8 →
      ∀ P : Fin 4 → HypPair Q, (∀ i j, i ≠ j → (P i).Orth (P j)) → False)
    {L₁ L₂ : Subgroup (V ≃ₗ[K] V)} {i₁ i₂ : V ≃ₗ[K] V}
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂)
    (hc : ⁅i₁, i₂⁆ ∈ scalars K V) : i₁ * i₂ = i₂ * i₁ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₂, rfl, rfl⟩ := h₂
  obtain ⟨c, hcv⟩ := mem_scalars.mp hc
  have hi₁ : F₁.La (-1) * F₁.La (-1) = 1 := F₁.La_neg_one_mul_self
  have hi₂ : F₂.La (-1) * F₂.La (-1) = 1 := F₂.La_neg_one_mul_self
  have hi₁' : ∀ v, F₁.La (-1) (F₁.La (-1) v) = v := fun v => by
    have := congrArg (fun g : V ≃ₗ[K] V => g v) hi₁
    simpa using this
  have hi₂' : ∀ v, F₂.La (-1) (F₂.La (-1) v) = v := fun v => by
    have := congrArg (fun g : V ≃ₗ[K] V => g v) hi₂
    simpa using this
  have key : ∀ v, F₁.La (-1) (F₂.La (-1) (F₁.La (-1) v)) = c • F₂.La (-1) v := by
    intro v
    have := hcv (F₂.La (-1) v)
    have e1 : (F₁.La (-1))⁻¹ = F₁.La (-1) := inv_eq_of_mul_eq_one_right hi₁
    have e2 : (F₂.La (-1))⁻¹ = F₂.La (-1) := inv_eq_of_mul_eq_one_right hi₂
    simp only [commutatorElement_def, e1, e2, LinearEquiv.mul_apply, hi₂'] at this
    exact this
  have hneg : ∀ v ∈ F₂.span, F₂.La (-1) v = -v := by
    intro v hv
    have hv' : v ∈ negSpace (F₂.La (-1)) := by rw [negSpace_La_neg_one h2]; exact hv
    have := Module.End.mem_eigenspace_iff.mp hv'
    simpa using this
  have hpos : ∀ v, F₂.La (-1) v = v → v ∈ F₂.perp := fun v hv => by
    rw [← posSpace_La_neg_one h2]
    exact Module.End.mem_eigenspace_iff.mpr (by simpa using hv)
  have hpos' : ∀ v ∈ F₂.perp, F₂.La (-1) v = v := fun v hv => by
    rw [← posSpace_La_neg_one h2] at hv
    have := Module.End.mem_eigenspace_iff.mp hv
    simpa using this
  by_cases hc1 : c = 1
  · subst hc1
    refine LinearEquiv.ext fun v => ?_
    have := key (F₁.La (-1) v)
    rw [hi₁', one_smul] at this
    exact this
  exfalso
  have hspan : ∀ v ∈ F₂.span, c • F₂.La (-1) (F₁.La (-1) v) = -(F₁.La (-1) v) := by
    intro v hv
    have h := key (F₁.La (-1) v)
    rw [hi₁', hneg v hv, map_neg] at h
    exact h.symm
  have hi₂w : ∀ v ∈ F₂.span, F₂.La (-1) (F₁.La (-1) v) = -(c • F₁.La (-1) v) := by
    intro v hv
    have h := congrArg (F₂.La (-1)) (hspan v hv)
    rw [map_smul, hi₂', map_neg] at h
    exact neg_eq_iff_eq_neg.mp h.symm
  have hne : F₂.span ≠ ⊥ := by
    intro h
    have := F₂.finrank_span
    rw [h, finrank_bot] at this
    omega
  have hcc : c = -1 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hw0 : F₁.La (-1) v ≠ 0 := fun h => hv0 (by
      have := hi₁' v
      rw [h, map_zero] at this
      exact this.symm)
    have h1 := hspan v hv
    rw [hi₂w v hv] at h1
    have h3 : (c * c - 1) • F₁.La (-1) v = 0 := by
      rw [smul_neg, smul_smul] at h1
      rw [sub_smul, one_smul, neg_inj.mp h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_self_eq_one_iff.mp (sub_eq_zero.mp h) with h | h
      · exact absurd h hc1
      · exact h
    · exact absurd h hw0
  have hg : F₁.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (F₁.La_mem_elementaryGroup (-1))
  have hsp : ∀ x ∈ F₂.span, F₁.La (-1) x ∈ F₂.perp := by
    intro x hx
    apply hpos
    rw [hi₂w x hx, hcc]
    simp
  have hper : ∀ y ∈ F₂.perp, F₁.La (-1) y ∈ F₂.span := by
    intro y hy
    rw [← negSpace_La_neg_one h2]
    refine Module.End.mem_eigenspace_iff.mpr ?_
    have h := key y
    rw [hcc, hpos' y hy] at h
    have h' := congrArg (F₁.La (-1)) h
    rw [hi₁'] at h'
    simp only [map_neg, neg_smul, one_smul] at h' ⊢
    simpa using h'
  have h4 : Module.finrank K F₂.perp = 4 := by
    have hle1 : Module.finrank K F₂.perp ≤ 4 := by
      have : Submodule.map (F₁.La (-1) : V →ₗ[K] V) F₂.perp ≤ F₂.span := by
        rintro _ ⟨y, hy, rfl⟩
        exact hper y hy
      calc Module.finrank K F₂.perp
          = Module.finrank K (Submodule.map (F₁.La (-1) : V →ₗ[K] V) F₂.perp) :=
            (LinearEquiv.finrank_map_eq (F₁.La (-1)) F₂.perp).symm
        _ ≤ Module.finrank K F₂.span := Submodule.finrank_mono this
        _ = 4 := F₂.finrank_span
    have hle2 : 4 ≤ Module.finrank K F₂.perp := by
      have : Submodule.map (F₁.La (-1) : V →ₗ[K] V) F₂.span ≤ F₂.perp := by
        rintro _ ⟨y, hy, rfl⟩
        exact hsp y hy
      calc 4 = Module.finrank K F₂.span := F₂.finrank_span.symm
        _ = Module.finrank K (Submodule.map (F₁.La (-1) : V →ₗ[K] V) F₂.span) :=
            (LinearEquiv.finrank_map_eq (F₁.La (-1)) F₂.span).symm
        _ ≤ Module.finrank K F₂.perp := Submodule.finrank_mono this
    omega
  have h8' : Module.finrank K V = 8 := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₂
    omega
  obtain ⟨P, hP⟩ := exists_four_pairs_of_swap F₂ hg hsp
  exact h8 h8' P hP

end Comm

section Adj

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem adj_data_small (hodd : Odd (Nat.card K))
    (h8 : Module.finrank K V = 8 →
      ∀ P : Fin 4 → HypPair Q, (∀ i j, i ≠ j → (P i).Orth (P j)) → False)
    {c l : Subgroup (V ≃ₗ[K] V)} {ic il : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (hl : IsFundamental Q l il) (h : ModelAdj (scalars K V) c l) :
    ic * il = il * ic ∧ il ∈ Subgroup.normalizer (c : Set (V ≃ₗ[K] V)) ∧
      il ∉ Subgroup.centralizer (c : Set (V ≃ₗ[K] V)) := by
  obtain ⟨hne, hnc, rc, rl, hrc, hrl, hcen, hnorm⟩ := h
  have e1 := invOf_eq hodd hc hrc
  have e2 := invOf_eq hodd hl hrl
  subst e1 e2
  have hcomm := commute_of_commutator_mem_scalars_small hodd h8 hc hl hcen
  refine ⟨hcomm, ?_, fun hcent => hnc ((IsFundamental.commute_iff hodd hc hl hcomm hne).mpr hcent)⟩
  have hmul : rl * rl = 1 := hl.mul_self
  have hinv : rl⁻¹ = rl := inv_eq_of_mul_eq_one_right hmul
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hnorm x, fun hx => ?_⟩
  have := hnorm _ hx
  rwa [show rl * (rl * x * rl⁻¹) * rl⁻¹ = x by
    rw [hinv]
    calc rl * (rl * x * rl) * rl = (rl * rl) * x * (rl * rl) := by group
      _ = x := by rw [hmul]; group] at this

variable {p f : ℕ} [Fact p.Prime] {K' : Type} [Field K'] [Finite K'] [CharP K' p]

theorem orthGeom_sign_small (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K))
    (h8 : Module.finrank K V = 8 →
      ∀ P : Fin 4 → HypPair Q, (∀ i j, i ≠ j → (P i).Orth (P j)) → False) :
    ∀ R₁ ∈ fundSet Q, ∀ R₂ ∈ fundSet Q, ∀ R₃ ∈ fundSet Q, ModelAdj (scalars K V) R₁ R₂ →
      ModelAdj (scalars K V) R₃ R₂ → Commutes R₁ R₃ →
      (∃ W, LinearBlockStandardPair K W R₁ R₂) → ∃ W, LinearBlockStandardPair K W R₂ R₃ := by
  rintro R₁ ⟨i₁, h₁⟩ R₂ ⟨i₂, h₂⟩ R₃ ⟨i₃, h₃⟩ a₁ a₃ k13 ⟨W, hW⟩
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data_small hodd h8 h₁ h₂ a₁
  obtain ⟨cm₃, N₃, C₃⟩ := adj_data_small hodd h8 h₃ h₂ a₃
  have hc13 : i₁ * i₃ = i₃ * i₁ := k13 _ h₁.mem _ h₃.mem
  rcases lemma_6_11_signs hK hK' hodd h₁ h₂ h₃ cm₁ cm₃ hc13 k13 N₁ N₃ C₁ C₃ with
    ⟨-, -, -, hl⟩ | ⟨-, -, hu, -⟩
  · exact ⟨_, hl⟩
  · exfalso
    have hW' : LinearBlockStandardPair K (R₁ ⊔ R₂) R₁ R₂ := linear_eq_sup hW ▸ hW
    exact not_linear_and_unitary hK hK' hodd hW' hu

end Adj

section Eight

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem adj_data_of_comm (hodd : Odd (Nat.card K))
    {c l : Subgroup (V ≃ₗ[K] V)} {ic il : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (hl : IsFundamental Q l il) (hcomm : ic * il = il * ic) (h : ModelAdj (scalars K V) c l) :
    il ∈ Subgroup.normalizer (c : Set (V ≃ₗ[K] V)) ∧
      il ∉ Subgroup.centralizer (c : Set (V ≃ₗ[K] V)) := by
  obtain ⟨hne, hnc, rc, rl, hrc, hrl, hcen, hnorm⟩ := h
  have e1 := invOf_eq hodd hc hrc
  have e2 := invOf_eq hodd hl hrl
  subst e1 e2
  refine ⟨?_, fun hcent => hnc ((IsFundamental.commute_iff hodd hc hl hcomm hne).mpr hcent)⟩
  have hmul : rl * rl = 1 := hl.mul_self
  have hinv : rl⁻¹ = rl := inv_eq_of_mul_eq_one_right hmul
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hnorm x, fun hx => ?_⟩
  have := hnorm _ hx
  rwa [show rl * (rl * x * rl⁻¹) * rl⁻¹ = x by
    rw [hinv]
    calc rl * (rl * x * rl) * rl = (rl * rl) * x * (rl * rl) := by group
      _ = x := by rw [hmul]; group] at this

theorem commute_of_orth_eight (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8)
    {L₁ L₃ : Subgroup (V ≃ₗ[K] V)} {i₁ i₃ : V ≃ₗ[K] V} (h₁ : IsFundamental Q L₁ i₁)
    (h₃ : IsFundamental Q L₃ i₃) (hk : Commutes L₁ L₃) {g : V ≃ₗ[K] V}
    (hg : g * i₁ = i₁ * g) : g * i₃ = i₃ * g := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rcases orth_or_twin hodd h₁ h₃ hk with horth | heq
  swap
  · rw [heq]; exact hg
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  obtain ⟨F₃, rfl, rfl⟩ := h₃
  have hd₁ := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₁
  have hd₃ := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₃
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at horth
  have hs₁₃ : F₁.span ≤ F₃.perp := by
    intro a ha
    rw [CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.mem_perp_iff_forall_incl]
    intro X
    exact horth a ha _ ⟨X, rfl⟩
  have hs₃₁ : F₃.span ≤ F₁.perp := by
    intro a ha
    rw [CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.mem_perp_iff_forall_incl]
    intro X
    rw [polar_comm]
    exact horth _ ⟨X, rfl⟩ a ha
  have e₁₃ : F₁.span = F₃.perp :=
    Submodule.eq_of_le_of_finrank_eq hs₁₃ (by rw [F₁.finrank_span]; omega)
  have e₃₁ : F₃.span = F₁.perp :=
    Submodule.eq_of_le_of_finrank_eq hs₃₁ (by rw [F₃.finrank_span]; omega)
  have hneg : ∀ (F : OFrame Q) (v : V), v ∈ F.span → F.La (-1) v = -v := by
    intro F v hv
    have hv' : v ∈ negSpace (F.La (-1)) := by rw [negSpace_La_neg_one h2]; exact hv
    have := Module.End.mem_eigenspace_iff.mp hv'
    simpa using this
  have hfix : ∀ (F : OFrame Q) (v : V), v ∈ F.perp → F.La (-1) v = v := fun F v hv =>
    (CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.mem_perp_iff_fix h2 (F := F)).mp hv
  have hneg3 : ∀ v : V, F₃.La (-1) v = -F₁.La (-1) v := by
    intro v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
      ((CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.isCompl_span_perp F₁).sup_eq_top ▸
        Submodule.mem_top : v ∈ F₁.span ⊔ F₁.perp)
    rw [map_add, map_add, hneg F₁ a ha, hfix F₁ b hb,
      hfix F₃ a (e₁₃ ▸ ha), hneg F₃ b (e₃₁ ▸ hb)]
    abel
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hneg3, hneg3, map_neg]
  have := congrArg (fun m : V ≃ₗ[K] V => m v) hg
  simp only [LinearEquiv.mul_apply] at this
  rw [this]

variable {p f : ℕ} [Fact p.Prime] {K' : Type} [Field K'] [Finite K'] [CharP K' p]

theorem orthGeom_sign_eight (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (hdim : Module.finrank K V = 8) :
    ∀ R₁ ∈ fundSet Q, ∀ R₂ ∈ fundSet Q, ∀ R₃ ∈ fundSet Q, ModelAdj (scalars K V) R₁ R₂ →
      ModelAdj (scalars K V) R₃ R₂ → Commutes R₁ R₃ →
      (∃ W, LinearBlockStandardPair K W R₁ R₂) → ∃ W, LinearBlockStandardPair K W R₂ R₃ := by
  rintro R₁ ⟨i₁, h₁⟩ R₂ ⟨i₂, h₂⟩ R₃ ⟨i₃, h₃⟩ a₁ a₃ k13 ⟨W, hW⟩
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hc12 : i₁ * i₂ = i₂ * i₁ := standardPair_involutions_commute h2 hW h₁.mem h₂.mem
    (h₁.orderOf_eq_two hodd) (h₂.orderOf_eq_two hodd)
  have hc32 : i₃ * i₂ = i₂ * i₃ :=
    (commute_of_orth_eight hodd hdim h₁ h₃ k13 (g := i₂) hc12.symm).symm
  obtain ⟨N₁, C₁⟩ := adj_data_of_comm hodd h₁ h₂ hc12 a₁
  obtain ⟨N₃, C₃⟩ := adj_data_of_comm hodd h₃ h₂ hc32 a₃
  have hc13 : i₁ * i₃ = i₃ * i₁ := k13 _ h₁.mem _ h₃.mem
  rcases lemma_6_11_signs hK hK' hodd h₁ h₂ h₃ hc12 hc32 hc13 k13 N₁ N₃ C₁ C₃ with
    ⟨-, -, -, hl⟩ | ⟨-, -, hu, -⟩
  · exact ⟨_, hl⟩
  · exfalso
    have hW' : LinearBlockStandardPair K (R₁ ⊔ R₂) R₁ R₂ := linear_eq_sup hW ▸ hW
    exact not_linear_and_unitary hK hK' hodd hW' hu

end Eight

section Facts

variable {KY X : Type} [Group KY] [Group X] {F : Type} [Field F] [Finite F]

structure SignFacts (𝓕 : Set (Subgroup KY)) (F : Type) [Field F] [Finite F] : Prop where
  sign : ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, ∀ R₃ ∈ 𝓕, ModelAdj (Subgroup.center KY) R₁ R₂ →
    ModelAdj (Subgroup.center KY) R₃ R₂ → Commutes R₁ R₃ →
    (∃ W, LinearBlockStandardPair F W R₁ R₂) → ∃ W, LinearBlockStandardPair F W R₂ R₃
  lift : ∀ {X : Type} [Group X] (ψ : KY →* X), ψ.ker ≤ Subgroup.center KY →
    ∀ R₁ ∈ 𝓕, ∀ R₂ ∈ 𝓕, (∃ W, LinearBlockStandardPair F W (R₁.map ψ) (R₂.map ψ)) →
      ∃ W, LinearBlockStandardPair F W R₁ R₂

variable {π : KY →* X} {𝓕 : Set (Subgroup KY)} {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}


theorem signFacts_of_centralQuot {p : ℕ} [Fact p.Prime] [CharP F p] (h4 : 4 ≤ Nat.card F)
    [Finite KY] (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (h : CentralQuot π 𝓕 𝓕' Z')
    (hsign : ∀ R₁ ∈ 𝓕', ∀ R₂ ∈ 𝓕', ∀ R₃ ∈ 𝓕', ModelAdj Z' R₁ R₂ → ModelAdj Z' R₃ R₂ →
      Commutes R₁ R₃ → (∃ W, LinearBlockStandardPair F W R₁ R₂) →
      ∃ W, LinearBlockStandardPair F W R₂ R₃) :
    SignFacts 𝓕 F where
  sign := by
    intro R₁ h₁ R₂ h₂ R₃ h₃ a₁ a₃ k13 ⟨W, hW⟩
    obtain ⟨W', hW'⟩ := hsign (R₁.map π) (h.map_mem R₁ h₁) (R₂.map π) (h.map_mem R₂ h₂)
      (R₃.map π) (h.map_mem R₃ h₃) (h.modelAdj h₁ h₂ a₁) (h.modelAdj h₃ h₂ a₃)
      ((h.commutes_iff h₁).mpr k13) ⟨_, linearBlockStandardPair_map π h.ker_le hW⟩
    exact exists_lin_of_map h4 hC π h.ker_le (h.perf R₂ h₂) (h.perf R₃ h₃) ⟨W', hW'⟩
  lift := fun ψ hψ R₁ h₁ R₂ h₂ hl =>
    exists_lin_of_map h4 hC ψ hψ (h.perf R₁ h₁) (h.perf R₂ h₂) hl

end Facts

end CFSG.ClassicalInvolution.RouteD.TWS6
