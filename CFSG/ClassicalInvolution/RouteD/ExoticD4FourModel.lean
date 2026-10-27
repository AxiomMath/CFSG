module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairSpinPlus
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectPSU
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.LocalLift
public import CFSG.LieType.CurtisTits.Symplectic
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

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.ModelFacts CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

namespace CFSG.ClassicalInvolution.RouteD.Exotic

section Frames

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem La_neg_one_mul_of_orth (h2 : (2 : K) ≠ 0) (hdim : Module.finrank K V = 8)
    {F₁ F₂ : OFrame Q} (horth : ∀ X Y, polar Q (F₁.incl X) (F₂.incl Y) = 0) :
    F₁.La (-1) * F₂.La (-1) = LinearEquiv.neg K := by
  have horth' : ∀ X Y, polar Q (F₂.incl X) (F₁.incl Y) = 0 := fun X Y => by
    rw [polar_comm]
    exact horth Y X
  have h4₁ := F₁.finrank_span
  have h4₂ := F₂.finrank_span
  have hc₁ := Submodule.finrank_add_eq_of_isCompl F₁.isCompl_span_perp
  have hc₂ := Submodule.finrank_add_eq_of_isCompl F₂.isCompl_span_perp
  have hle₁ : F₂.span ≤ F₁.perp := by
    rintro _ ⟨Y, rfl⟩
    exact (Frame.mem_perp_iff F₁).mpr (Frame.coords_incl_eq_zero_of_orth horth' Y)
  have hle₂ : F₁.span ≤ F₂.perp := by
    rintro _ ⟨Y, rfl⟩
    exact (Frame.mem_perp_iff F₂).mpr (Frame.coords_incl_eq_zero_of_orth horth Y)
  have e₁ : F₂.span = F₁.perp := Submodule.eq_of_le_of_finrank_eq hle₁ (by omega)
  have e₂ : F₁.span = F₂.perp := Submodule.eq_of_le_of_finrank_eq hle₂ (by omega)
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    ((F₁.isCompl_span_perp.sup_eq_top).symm ▸ Submodule.mem_top : x ∈ F₁.span ⊔ F₁.perp)
  have i1a : F₁.La (-1) a = -a := (Frame.mem_span_iff_inv F₁ h2).mp ha
  have i1b : F₁.La (-1) b = b := (Frame.mem_perp_iff_fix F₁ h2).mp hb
  have i2a : F₂.La (-1) a = a := (Frame.mem_perp_iff_fix F₂ h2).mp (e₂ ▸ ha)
  have i2b : F₂.La (-1) b = -b := (Frame.mem_span_iff_inv F₂ h2).mp (e₁ ▸ hb)
  simp [LinearEquiv.mul_apply, map_add, i2a, i2b, i1a, i1b]

end Frames

section Spin4

variable {K : Type} [Field K] [Finite K]

theorem spinAction_injOn_fund (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ 4)
    (hsingle : Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 K hn3))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3), ⁅R, R⁆ = R)
    (hlong : ∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 K hn3) (Pi.single k 1))
    (hsl2 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3),
      Nonempty (R ≃* SL(2, K)))
    {R : Subgroup (spinGroup (quadPlus 4 K))}
    (hR : R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3))
    {c : spinGroup (quadPlus 4 K)} (hc : c ∈ R) (h1 : spinAction (quadPlus 4 K) c = 1) :
    c = 1 := by
  have hker := ker_spinAction_le_center (quadPlus 4 K)
  obtain ⟨e⟩ := hsl2 R hR
  obtain ⟨fr, hfr⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR
  obtain ⟨r, hr, hθr⟩ : fr.La (-1) ∈ R.map (spinAction (quadPlus 4 K)) := hfr ▸ ⟨-1, rfl⟩
  have hne : fr.La (-1) ≠ 1 := by
    intro h
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd (fr.La_injective (by rw [h, map_one]))
  have hcenR : ∀ g : spinGroup (quadPlus 4 K), (hg : g ∈ R) → g ∈ Subgroup.centralizer (R : Set _) →
      e ⟨g, hg⟩ = 1 ∨ e ⟨g, hg⟩ = -1 := by
    intro g hg hgc
    have : (⟨g, hg⟩ : R) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgc y y.2)
    exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
      ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp this)
  have hrcent : r ∈ Subgroup.centralizer (R : Set _) :=
    Models.Transfer.mem_centralizer_of_map hker (hperf R hR) (g := r) (by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨s, hs, rfl⟩
      have hs' : spinAction (quadPlus 4 K) s ∈ fr.La.range := hfr ▸ ⟨s, hs, rfl⟩
      obtain ⟨A, hA⟩ := hs'
      show _ * spinAction (quadPlus 4 K) r = spinAction (quadPlus 4 K) r * _
      rw [hθr, ← hA, ← map_mul, ← map_mul]
      congr 1
      exact (Subgroup.mem_center_iff.mp
        ((CFSG.ClassicalInvolution.mem_center_sl2_iff (-1 : SL(2, K))).mpr (Or.inr rfl)) A))
  have hccent : c ∈ Subgroup.centralizer (R : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp (hker h1) y)
  rcases hcenR c hc hccent with hc1 | hc1
  · exact congrArg Subtype.val (e.injective (hc1.trans e.map_one.symm) : (⟨c, hc⟩ : R) = 1)
  · exfalso
    rcases hcenR r hr hrcent with hr1 | hr1
    · have : r = 1 := congrArg Subtype.val
        (e.injective (hr1.trans e.map_one.symm) : (⟨r, hr⟩ : R) = 1)
      rw [this, map_one] at hθr
      exact hne hθr.symm
    · have : r = c := congrArg Subtype.val
        (e.injective (hr1.trans hc1.symm) : (⟨r, hr⟩ : R) = ⟨c, hc⟩)
      rw [this, h1] at hθr
      exact hne hθr.symm

theorem fund_pair_mul_central_plus (hodd : Odd (Nat.card K)) (hn3 : 3 ≤ 4)
    (hsingle : Generic.FundamentalSingleClass .POmegaPlus (plusDatum 4 K hn3))
    (hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3), ⁅R, R⁆ = R)
    (hlong : ∀ k : Fin 4, Generic.IsLongestRoot (plusDatum 4 K hn3) (Pi.single k 1))
    (hgen : ∀ x : spinGroup (quadPlus 4 K),
      ⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) x (Pi.single k 1) = ⊤)
    (hsl2 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3),
      Nonempty (R ≃* SL(2, K)))
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 K))}
    (hR₁ : R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3))
    (hR₂ : R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3))
    (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    {c₁ c₂ : spinGroup (quadPlus 4 K)} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂)
    (h₁ : c₁ ≠ 1) (h₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 K)) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have hker := ker_spinAction_le_center (quadPlus 4 K)
  have hdim : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hmemF : ∀ (x : spinGroup (quadPlus 4 K)) (k : Fin 4),
      rankOneRoot (plusDatum 4 K hn3) x (Pi.single k 1) ∈
        Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3) := fun x k =>
    ⟨x, Pi.single k 1, Or.inl (hlong k), rfl⟩
  have hθ₁ : spinAction (quadPlus 4 K) c₁ ≠ 1 := fun h =>
    h₁ (spinAction_injOn_fund hodd hn3 hsingle hperf hlong hsl2 hR₁ hc₁ h)
  have hθ₂ : spinAction (quadPlus 4 K) c₂ ≠ 1 := fun h =>
    h₂ (spinAction_injOn_fund hodd hn3 hsingle hperf hlong hsl2 hR₂ hc₂ h)
  obtain ⟨fr₁, hfr₁⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₁
  obtain ⟨fr₂, hfr₂⟩ := exists_frame_of_mem_fund_plus hn3 hsingle hlong hR₂
  have hi₁ : spinAction (quadPlus 4 K) c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction (quadPlus 4 K) c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  by_cases hEq : fr₂.La (-1) = fr₁.La (-1)
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, hi₁, hi₂, hEq]
    exact fr₁.La_neg_one_mul_self
  · have hc' : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
      rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hc c₁ hc₁ c₂ hc₂]
    have hcent : ∀ A : SL(2, K), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
      intro A
      obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction (quadPlus 4 K)) := hfr₁ ▸ ⟨A, rfl⟩
      rw [← hi₂, ← hrA, ← map_mul, ← map_mul, (hc r hr c₂ hc₂).symm]
    have horth := (Frame.orth_or_eq h2 hc' hcent).resolve_right hEq
    have hneg := La_neg_one_mul_of_orth h2 hdim horth
    have hθ12 : spinAction (quadPlus 4 K) (c₁ * c₂) = LinearEquiv.neg K := by
      rw [map_mul, hi₁, hi₂, hneg]
    have hcent' : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (plusDatum 4 K hn3),
        R ≤ Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 K))) := by
      intro R hR y hy
      have := Models.Transfer.mem_centralizer_of_map hker (hperf R hR) (g := c₁ * c₂) (by
        rw [hθ12, Subgroup.mem_centralizer_iff]
        intro h _
        ext v
        simp)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp this y hy)
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) 1 (Pi.single k 1)) := by
      rw [hgen 1]
      trivial
    have : (⨆ k : Fin 4, rankOneRoot (plusDatum 4 K hn3) 1 (Pi.single k 1)) ≤
        Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 K))) :=
      iSup_le fun k => hcent' _ (hmemF 1 k)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)

end Spin4

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem fund_pair_mul_central_of_eq (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {t : StatedLieTag}
    {n e : ℕ} (ht : t = .POmegaPlus) (hn : n = 4) (he : e = f)
    (hadm : StatedLieAdmissible t n p e)
    {R₁ R₂ : Subgroup (Generic.modelUniv t n p e Fact.out).K}
    (hR₁ : R₁ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hR₂ : R₂ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D)
    (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    {c₁ c₂ : (Generic.modelUniv t n p e Fact.out).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂)
    (h₁ : c₁ ≠ 1) (h₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Subgroup.center (Generic.modelUniv t n p e Fact.out).K := by
  subst ht hn he
  have hn3 : 3 ≤ 4 := by omega
  obtain ⟨hodd, -⟩ := card_galoisField_facts hp2 hq
  have hM : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 p e Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 p e Fact.out).trans (modelUniv_POmegaPlus hn3)
  have hsingle : Generic.FundamentalSingleClass .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D :=
    fundamentalSingleClass .POmegaPlus 4 p e Fact.out trivial hadm (by decide) (by decide)
  have hperf : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D, ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (fundPerfect_core .POmegaPlus 4 p e hp2 trivial hadm (by omega) R hR)
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus 4 p e Fact.out trivial hadm k trivial
  have hgen : ∀ g : (Generic.modelUniv .POmegaPlus 4 p e Fact.out).K,
      ⨆ i : Fin (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D.rank,
        rankOneRoot (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D g (Pi.single i 1) = ⊤ :=
    iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 p e Fact.out trivial hadm
  have hsl2 : ∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D, Nonempty (R ≃* SL(2, GaloisField p e)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups (t := .POmegaPlus) (n := 4)
      hp2 trivial hadm (by decide) (by decide) hR
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField p e)), plusDatum 4 (GaloisField p e) hn3⟩ →
      Generic.FundamentalSingleClass .POmegaPlus M.D →
      (∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus M.D, ⁅R, R⁆ = R) →
      (∀ k : Fin M.D.rank, Generic.IsLongestRoot M.D (Pi.single k 1)) →
      (∀ g : M.K, ⨆ i : Fin M.D.rank, rankOneRoot M.D g (Pi.single i 1) = ⊤) →
      (∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus M.D, Nonempty (R ≃* SL(2, GaloisField p e))) →
      ∀ R₁ R₂ : Subgroup M.K, R₁ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
        R₂ ∈ Generic.fundamentalSubgroups .POmegaPlus M.D →
        (∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a) → ∀ c₁ c₂ : M.K, c₁ ∈ R₁ → c₂ ∈ R₂ →
        (∀ r ∈ R₁, c₁ * r = r * c₁) → (∀ r ∈ R₂, c₂ * r = r * c₂) → c₁ ≠ 1 → c₂ ≠ 1 →
        c₁ * c₂ ∈ Subgroup.center M.K := by
    intro M hM hsingle hperf hlong hgen hsl2 R₁ R₂ hR₁ hR₂ hc c₁ c₂ hc₁ hc₂ hz₁ hz₂ h₁ h₂
    subst hM
    exact fund_pair_mul_central_plus hodd hn3 hsingle hperf hlong hgen hsl2 hR₁ hR₂ hc hc₁ hc₂
      hz₁ hz₂ h₁ h₂
  exact key _ hM hsingle hperf hlong hgen hsl2 R₁ R₂ hR₁ hR₂ hc c₁ c₂ hc₁ hc₂ hz₁ hz₂ h₁ h₂

end Model



section Generation

variable {p f : ℕ} [Fact p.Prime]

theorem top_le_iSup_fund_of_eq {t : StatedLieTag} {n e : ℕ} (ht : t = .POmegaPlus) (hn : n = 4)
    (hadm : StatedLieAdmissible t n p e) :
    (⊤ : Subgroup (Generic.modelUniv t n p e Fact.out).K) ≤
      ⨆ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n p e Fact.out).D, R := by
  subst ht hn
  have hlong : ∀ k : Fin (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D.rank,
      Generic.IsLongestRoot (Generic.modelUniv .POmegaPlus 4 p e Fact.out).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus 4 p e Fact.out trivial hadm k trivial
  have hgen := iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 p e Fact.out trivial hadm 1
  rw [← hgen]
  exact iSup_le fun k => le_iSup₂_of_le _ ⟨1, Pi.single k 1, Or.inl (hlong k), rfl⟩ le_rfl

end Generation

end CFSG.ClassicalInvolution.RouteD.Exotic
