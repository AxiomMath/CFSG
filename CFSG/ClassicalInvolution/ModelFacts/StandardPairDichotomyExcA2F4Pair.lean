module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Rational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2F4Levi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4
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
public import Certificates.Certificate3952
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.OddCover
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcF4Main
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
public import CFSG.ClassicalInvolution.Models.UnitaryFrames
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.ClassicalInvolution.RouteD.TypeAChain
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
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
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.LocalAnalysis.SignalizerFunctor
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

section RankOne

variable {K : Type} [Field K]

theorem mem_stdRankOne_f4_iff' {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (r : ↥(adjointGroup .F4 K)) :
    r ∈ stdRankOne (f4Datum K) β ↔
      ∃ A : SL2 K, (r : ModGL .F4 K) = rootSL2 .F4 K β A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .F4) hβ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .F4 K hβ).1
  change r ∈ rootGroup (rootOperatorFamily .F4) K β ⊔
    rootGroup (rootOperatorFamily .F4) K (-β) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem rootTorusSL2_corootDiagF4 {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hl : iform β β = 4) (c : Kˣ) :
    rootSL2 .F4 K β (HSL c) = rootDiagUnit .F4 (corootDiagF4 β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .F4 K hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  change rootTorusSL2 .F4 K β c = _
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .F4 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .F4 a : ModGL .F4 K) : Module.End K (RootModule .F4 K))
      (rootVec .F4 K (Pi.single i 1))) = ((a i : Kˣ) : K) • rootVec .F4 K (Pi.single i 1) := by
    change rootDiag a (rootVec .F4 K (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .F4) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .F4 i), hs]
  rw [h2] at h1
  have hne : rootVec .F4 K (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .F4 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective K hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) / 2 := by
    rw [hl]
    omega
  rw [h4] at h3
  exact Units.ext h3

end RankOne

section Involutions

variable {K : Type} [Field K]

theorem eq_signDiagF4_of_orderOf_eq_two (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) (hl : iform β β = 4) {c : ↥(adjointGroup .F4 K)}
    (hc : c ∈ stdRankOne (f4Datum K) β) (hc2 : orderOf c = 2) :
    (c : ModGL .F4 K) = signDiagF4 K β := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .F4 K β) :=
    ((exceptional_Lang_root_rank_one_data .F4 K β).2.2.2.2.2.2.2.1 hK).1
  obtain ⟨A, hA⟩ := (mem_stdRankOne_f4_iff' hβ c).1 hc
  obtain ⟨hc1, hne⟩ := (orderOf_eq_prime_iff (p := 2)).1 hc2
  have hAA : A * A = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hA]
    have := congrArg (fun x : ↥(adjointGroup .F4 K) => (x : ModGL .F4 K)) hc1
    simpa [sq] using this
  rcases sl2_sq_eq_one_A2 h2 hAA with rfl | rfl
  · exfalso
    apply hne
    exact Subtype.ext (by rw [hA, map_one]; rfl)
  · rw [hA]
    exact rootTorusSL2_corootDiagF4 hβ hl (-1)

theorem signDiagF4_mem_stdRankOne {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hl : iform β β = 4) :
    (⟨signDiagF4 K β, by
        rw [signDiagF4, ← rootTorusSL2_corootDiagF4 hβ hl (-1)]
        exact rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .F4 K)) ∈
      stdRankOne (f4Datum K) β :=
  (mem_stdRankOne_f4_iff' hβ _).2 ⟨HSL (-1), (rootTorusSL2_corootDiagF4 hβ hl (-1)).symm⟩

theorem conj_mem_stdRankOne_of_mem_h1F4 {g : ↥(adjointGroup .F4 K)}
    (hg : (g : ModGL .F4 K) ∈ h1F4 K) {x : ↥(adjointGroup .F4 K)}
    (hx : x ∈ stdRankOne (f4Datum K) thetaF4) : g * x * g⁻¹ ∈ stdRankOne (f4Datum K) thetaF4 := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_f4_iff' isRoot_thetaF4 x).1 hx
  obtain ⟨n, hn, A, hgA⟩ := hg
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq_F4 hn (A * B * A⁻¹)
  refine (mem_stdRankOne_f4_iff' isRoot_thetaF4 _).2 ⟨A', ?_⟩
  rw [← hA']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgA, hB, map_mul, map_inv]
  group

theorem mem_h1F4_of_commute_signDiagF4 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .F4 K)}
    (hu : (u : ModGL .F4 K) * signDiagF4 K thetaF4 = signDiagF4 K thetaF4 * (u : ModGL .F4 K)) :
    (u : ModGL .F4 K) ∈ h1F4 K := by
  have hcT : (u : ModGL .F4 K) ∈ toralCentralizer .F4 K (corootDiagF4 thetaF4 (-1 : Kˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨u.2, ?_⟩
    show signDiagF4 K thetaF4 * (u : ModGL .F4 K) * (signDiagF4 K thetaF4)⁻¹ = u
    rw [mul_inv_eq_iff_eq_mul, hu]
  exact toralRootGroup_le_h1F4 hK
    (toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inl rfl)) hK
      (corootDiagF4_neg_one_sign thetaF4) hcT)

theorem map_conj_stdRankOne_theta_F4 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .F4 K)}
    (hu : (u : ModGL .F4 K) * signDiagF4 K thetaF4 = signDiagF4 K thetaF4 * (u : ModGL .F4 K)) :
    (stdRankOne (f4Datum K) thetaF4).map (MulAut.conj u).toMonoidHom =
      stdRankOne (f4Datum K) thetaF4 := by
  have hu1 := mem_h1F4_of_commute_signDiagF4 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .F4 K)) : ModGL .F4 K) ∈ h1F4 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact conj_mem_stdRankOne_of_mem_h1F4 hu1 hr
  · intro hx
    refine ⟨u⁻¹ * x * u, ?_, ?_⟩
    · have := conj_mem_stdRankOne_of_mem_h1F4 hu' hx
      simpa using this
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

end Involutions

section Partner

theorem form_eq_iform_F4 (hA : TauCeti.IsFiniteType (Tag.cartan .F4)) :
    ∃ c : ℚ, 0 < c ∧ ∀ x y : Fin (Tag.rank .F4) → ℤ,
      form hA (toRat x) (toRat y) = c * (iform x y : ℚ) := by
  have hsym : ∀ i j : Fin (Tag.rank .F4),
      symmetrizer hA i * (Tag.cartan .F4 i j : ℚ) = symmetrizer hA j * (Tag.cartan .F4 j i : ℚ) :=
    fun i j => by
      have h := form_comm hA (Pi.single i 1) (Pi.single j 1)
      rw [form_single_left, form_single_left] at h
      simpa [Pi.single_apply] using h
  have hpos := symmetrizer_pos hA
  have h01 := hsym ⟨0, by decide⟩ ⟨1, by decide⟩
  have h12 := hsym ⟨1, by decide⟩ ⟨2, by decide⟩
  have h23 := hsym ⟨2, by decide⟩ ⟨3, by decide⟩
  have c01 : (Tag.cartan .F4 ⟨0, by decide⟩ ⟨1, by decide⟩ : ℤ) = -1 := by decide
  have c10 : (Tag.cartan .F4 ⟨1, by decide⟩ ⟨0, by decide⟩ : ℤ) = -1 := by decide
  have c12 : (Tag.cartan .F4 ⟨1, by decide⟩ ⟨2, by decide⟩ : ℤ) = -1 := by decide
  have c21 : (Tag.cartan .F4 ⟨2, by decide⟩ ⟨1, by decide⟩ : ℤ) = -2 := by decide
  have c23 : (Tag.cartan .F4 ⟨2, by decide⟩ ⟨3, by decide⟩ : ℤ) = -1 := by decide
  have c32 : (Tag.cartan .F4 ⟨3, by decide⟩ ⟨2, by decide⟩ : ℤ) = -1 := by decide
  rw [c01, c10] at h01
  rw [c12, c21] at h12
  rw [c23, c32] at h23
  push_cast at h01 h12 h23
  have d1 : symmetrizer hA ⟨1, by decide⟩ = symmetrizer hA ⟨0, by decide⟩ := by linarith
  have d2 : symmetrizer hA ⟨1, by decide⟩ = 2 * symmetrizer hA ⟨2, by decide⟩ := by linarith
  have d3 : symmetrizer hA ⟨2, by decide⟩ = symmetrizer hA ⟨3, by decide⟩ := by linarith
  set c := symmetrizer hA ⟨3, by decide⟩ with hc
  have hd : ∀ i, symmetrizer hA i = c * (Tag.symmetrizer .F4 i i : ℚ) := by
    intro i
    fin_cases i
    · have e : (Tag.symmetrizer .F4 ⟨0, by decide⟩ ⟨0, by decide⟩ : ℤ) = 2 := by decide
      show symmetrizer hA ⟨0, _⟩ = c * ((Tag.symmetrizer .F4 ⟨0, by decide⟩ ⟨0, by decide⟩ : ℤ) : ℚ)
      rw [e]; push_cast; linarith
    · have e : (Tag.symmetrizer .F4 ⟨1, by decide⟩ ⟨1, by decide⟩ : ℤ) = 2 := by decide
      show symmetrizer hA ⟨1, _⟩ = c * ((Tag.symmetrizer .F4 ⟨1, by decide⟩ ⟨1, by decide⟩ : ℤ) : ℚ)
      rw [e]; push_cast; linarith
    · have e : (Tag.symmetrizer .F4 ⟨2, by decide⟩ ⟨2, by decide⟩ : ℤ) = 1 := by decide
      show symmetrizer hA ⟨2, _⟩ = c * ((Tag.symmetrizer .F4 ⟨2, by decide⟩ ⟨2, by decide⟩ : ℤ) : ℚ)
      rw [e]; push_cast; linarith
    · have e : (Tag.symmetrizer .F4 ⟨3, by decide⟩ ⟨3, by decide⟩ : ℤ) = 1 := by decide
      show symmetrizer hA ⟨3, _⟩ = c * ((Tag.symmetrizer .F4 ⟨3, by decide⟩ ⟨3, by decide⟩ : ℤ) : ℚ)
      rw [e]; push_cast; ring
  refine ⟨c, hpos _, fun x y => ?_⟩
  have hxy : form hA (toRat x) (toRat y) =
      ∑ l, (y l : ℚ) * ∑ i, (x i : ℚ) * (symmetrizer hA l * (Tag.cartan .F4 l i : ℚ)) := by
    rw [form_eq_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [toRat_apply, form_comm, form_eq_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [toRat_apply, form_single_left]
    simp [Pi.single_apply]
  rw [hxy]
  simp only [iform, hd]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hB : (Tag.symmetrizedCartan .F4 i l : ℤ) = Tag.symmetrizedCartan .F4 l i :=
    symmetrizedCartan_symm .F4 i l
  rw [symmetrizedCartan_apply, symmetrizedCartan_apply] at hB
  have hB' : ((Tag.symmetrizer .F4 i i : ℤ) : ℚ) * (Tag.cartan .F4 i l : ℚ) =
      (Tag.symmetrizer .F4 l l : ℚ) * (Tag.cartan .F4 l i : ℚ) := by exact_mod_cast hB
  rw [symmetrizedCartan_apply]
  push_cast
  linear_combination (-(c * (y l : ℚ) * (x i : ℚ))) * hB'

theorem isPartnerF4_of_isPartner {K : Type} [Field K] {δ : Fin (Tag.rank .F4) → ℤ}
    (hlong : ModelFacts.IsLongestRoot (f4Datum K) δ)
    (hp : IsPartner (f4Datum K).isFiniteType thetaF4 δ) : IsPartnerF4 δ := by
  obtain ⟨hmem, hmax⟩ := (isLongestRoot_iff _ _).1 hlong
  have hδ : IsRoot .F4 δ := isRoot_iff_mem_roots.2 hmem
  obtain ⟨c, hc, hform⟩ := form_eq_iform_F4 (f4Datum K).isFiniteType
  have hθ : thetaF4 ∈ (f4Datum K).roots := isRoot_iff_mem_roots.1 isRoot_thetaF4
  have h1 := hmax thetaF4 hθ
  rw [hform, hform] at h1
  have h2 : iform thetaF4 thetaF4 ≤ iform δ δ := by
    have := le_of_mul_le_mul_left h1 hc
    exact_mod_cast this
  rw [iform_thetaF4_self] at h2
  have hl : iform δ δ = 4 := by
    rcases iform_self_isRoot_F4 hδ with h | h <;> omega
  refine ⟨hδ, hl, ?_⟩
  rw [IsPartner, lenSq, hform, hform] at hp
  have h3 : c * (2 * (iform thetaF4 δ : ℚ)) = c * (-4) := by
    have : (iform δ δ : ℚ) = 4 := by exact_mod_cast hl
    rw [this] at hp
    linear_combination hp
  have h4 := mul_left_cancel₀ hc.ne' h3
  have : (iform thetaF4 δ : ℚ) = -2 := by linarith
  exact_mod_cast this

end Partner

section Final

variable {K : Type} [Field K]

theorem conj_mem_stdRankOne_iff_F4 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .F4 K)}
    (hu : (u : ModGL .F4 K) * signDiagF4 K thetaF4 = signDiagF4 K thetaF4 * (u : ModGL .F4 K))
    {w : ↥(adjointGroup .F4 K)} :
    u * w * u⁻¹ ∈ stdRankOne (f4Datum K) thetaF4 ↔ w ∈ stdRankOne (f4Datum K) thetaF4 := by
  have hu1 := mem_h1F4_of_commute_signDiagF4 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .F4 K)) : ModGL .F4 K) ∈ h1F4 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  constructor
  · intro hw
    have := conj_mem_stdRankOne_of_mem_h1F4 hu' hw
    simpa [mul_assoc] using this
  · exact conj_mem_stdRankOne_of_mem_h1F4 hu1

end Final

section Unique

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

omit [NeZero e] in
theorem stdRankOne_mem_longestFundamental {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β)
    (hl : iform β β = 4) :
    stdRankOne (f4Datum (GaloisField p e)) β ∈
      longestFundamental (f4Datum (GaloisField p e)) := by
  refine ⟨1, β, isLongestRoot_f4Datum_of_iform_eq_four hβ hl, ?_⟩
  have : (MulAut.conj (1 : ↥(adjointGroup .F4 (GaloisField p e)))).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]
  rfl

omit [NeZero e] in
theorem eq_of_mem_longestFundamental_F4 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .F4 0 p e)
    {R R' : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (hR : R ∈ longestFundamental (f4Datum (GaloisField p e)))
    (hR' : R' ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c : ↥(adjointGroup .F4 (GaloisField p e))} (hc : c ∈ R) (hc' : c ∈ R')
    (hc2 : orderOf c = 2) : R = R' := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .F4 (f4Datum (GaloisField p e)) :=
    fundamentalSingleClass .F4 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (f4Datum (GaloisField p e)) thetaF4 ∈
      Generic.fundamentalSubgroups .F4 (f4Datum (GaloisField p e)) :=
    ⟨1, thetaF4, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4
      iform_thetaF4_self), (Generic.conjSub_one _).symm⟩
  obtain ⟨x, hx⟩ := hsingle _ hθmem R (longestFundamental_subset .F4 _ hR)
  obtain ⟨x', hx'⟩ := hsingle _ hθmem R' (longestFundamental_subset .F4 _ hR')
  have h1 : x⁻¹ * c * x ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4 :=
    Generic.mem_conjSub_iff.1 (hx ▸ hc)
  have h1' : x'⁻¹ * c * x' ∈ stdRankOne (f4Datum (GaloisField p e)) thetaF4 :=
    Generic.mem_conjSub_iff.1 (hx' ▸ hc')
  have ord : ∀ y : ↥(adjointGroup .F4 (GaloisField p e)), orderOf (y⁻¹ * c * y) = 2 := fun y => by
    rw [← hc2]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective c
    simpa [MulAut.conj_apply] using this
  have z1 := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self h1 (ord x)
  have z1' := eq_signDiagF4_of_orderOf_eq_two hK isRoot_thetaF4 iform_thetaF4_self h1' (ord x')
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at z1 z1'
  have hu : ((x'⁻¹ * x : ↥(adjointGroup .F4 (GaloisField p e))) : ModGL .F4 (GaloisField p e)) *
      signDiagF4 (GaloisField p e) thetaF4 = signDiagF4 (GaloisField p e) thetaF4 *
        ((x'⁻¹ * x : ↥(adjointGroup .F4 (GaloisField p e))) : ModGL .F4 (GaloisField p e)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (↑x')⁻¹ * ↑x * signDiagF4 (GaloisField p e) thetaF4 =
        (↑x')⁻¹ * ↑x * ((↑x)⁻¹ * ↑c * ↑x) := by rw [z1]
      _ = (↑x')⁻¹ * ↑c * ↑x := by group
      _ = ((↑x')⁻¹ * ↑c * ↑x') * ((↑x')⁻¹ * ↑x) := by group
      _ = _ := by rw [z1']
  ext y
  rw [hx, hx', Generic.mem_conjSub_iff, Generic.mem_conjSub_iff]
  have e1 : x'⁻¹ * y * x' = (x'⁻¹ * x) * (x⁻¹ * y * x) * (x'⁻¹ * x)⁻¹ := by group
  rw [e1, conj_mem_stdRankOne_iff_F4 hK hu]

end Unique


section Split

variable {p e : ℕ} [Fact p.Prime]

local notation "Kq" => GaloisField p e

theorem signDiagF4_mem_adjointGroup {K : Type} [Field K] {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) (hl : iform β β = 4) : signDiagF4 K β ∈ adjointGroup .F4 K := by
  rw [signDiagF4, ← rootTorusSL2_corootDiagF4 hβ hl (-1)]
  exact rootSL2_mem_adjointGroup _ _

theorem orderOf_signDiagF4 {K : Type} [Field K] (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .F4) → ℤ}
    (hβ : IsRoot .F4 β) (hl : iform β β = 4) :
    orderOf (⟨signDiagF4 K β, signDiagF4_mem_adjointGroup hβ hl⟩ : ↥(adjointGroup .F4 K)) = 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .F4 K β) :=
    ((exceptional_Lang_root_rank_one_data .F4 K β).2.2.2.2.2.2.2.1 hK).1
  refine (orderOf_eq_prime_iff (p := 2)).2 ⟨?_, ?_⟩
  · refine Subtype.ext ?_
    show signDiagF4 K β * signDiagF4 K β = 1
    exact rootDiagUnit_corootDiagF4_mul_self β
  · intro h
    have h1 : signDiagF4 K β = 1 := congrArg Subtype.val h
    have h2' : rootSL2 .F4 K β (HSL (-1)) = 1 := by
      rw [rootTorusSL2_corootDiagF4 hβ hl (-1)]
      exact h1
    have := hinj (h2'.trans (map_one _).symm)
    have h3 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simp [coe_HSL] at h3
    exact Ring.neg_one_ne_one_of_char_ne_two hK h3

theorem linearBlockStandardPair_theta_deltaF4 [NeZero e] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4)
      (stdRankOne (f4Datum (GaloisField p e)) deltaF4) := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hδ₀ := isPartnerF4_deltaF4
  have hθlong : ModelFacts.IsLongestRoot (f4Datum (GaloisField p e)) thetaF4 :=
    isLongestRoot_f4Datum_of_iform_eq_four isRoot_thetaF4 iform_thetaF4_self
  obtain ⟨δ', hδ'l, hδ'p, W, hW⟩ := exists_standardPair_partner_F4 p e hadm hθlong
  have hδ'PF : IsPartnerF4 δ' := isPartnerF4_of_isPartner hδ'l hδ'p
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup ↥(adjointGroup .F4 (GaloisField p e)),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W'
        (stdRankOne (f4Datum (GaloisField p e)) thetaF4)
        (stdRankOne (f4Datum (GaloisField p e)) δ') := ⟨W, hW⟩
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerF4 (F := GaloisField p e) hδ'PF
  have hnG : n ∈ adjointGroup .F4 (GaloisField p e) := parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JF4 hn)
  let ν : ↥(adjointGroup .F4 (GaloisField p e)) := ⟨n⁻¹, inv_mem hnG⟩
  have hνθ : (ν : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (ν : ModGL .F4 (GaloisField p e)) :=
    (rootDiagUnit_corootDiagF4_comm_levi (-1 : (GaloisField p e)ˣ) (inv_mem hn)).symm
  let dδ' : ↥(adjointGroup .F4 (GaloisField p e)) :=
    ⟨signDiagF4 (GaloisField p e) δ', signDiagF4_mem_adjointGroup hδ'PF.1 hδ'PF.2.1⟩
  let dδ₀ : ↥(adjointGroup .F4 (GaloisField p e)) :=
    ⟨signDiagF4 (GaloisField p e) deltaF4, signDiagF4_mem_adjointGroup hδ₀.1 hδ₀.2.1⟩
  have hdδ' : dδ' ∈ stdRankOne (f4Datum (GaloisField p e)) δ' :=
    signDiagF4_mem_stdRankOne hδ'PF.1 hδ'PF.2.1
  have hdδ₀ : dδ₀ ∈ stdRankOne (f4Datum (GaloisField p e)) deltaF4 :=
    signDiagF4_mem_stdRankOne hδ₀.1 hδ₀.2.1
  have hνd : ν * dδ' * ν⁻¹ = dδ₀ := by
    refine Subtype.ext ?_
    have h1 : n * signDiagF4 (GaloisField p e) deltaF4 * n⁻¹ =
        signDiagF4 (GaloisField p e) δ' := hnd
    show n⁻¹ * signDiagF4 (GaloisField p e) δ' * (n⁻¹)⁻¹ = signDiagF4 (GaloisField p e) deltaF4
    rw [← h1]
    group
  have hRδ₀ := stdRankOne_mem_longestFundamental (p := p) (e := e) hδ₀.1 hδ₀.2.1
  have hRδ' := stdRankOne_mem_longestFundamental (p := p) (e := e) hδ'PF.1 hδ'PF.2.1
  have hν_R : (stdRankOne (f4Datum (GaloisField p e)) δ').map (MulAut.conj ν).toMonoidHom =
      stdRankOne (f4Datum (GaloisField p e)) deltaF4 :=
    eq_of_mem_longestFundamental_F4 hp2 hadm (map_conj_mem_longestFundamental ν hRδ') hRδ₀
      (c := dδ₀) ⟨dδ', hdδ', hνd⟩ hdδ₀ (orderOf_signDiagF4 hK hδ₀.1 hδ₀.2.1)
  have hpair := linearBlockStandardPair_map_conj hW' ν
  rw [map_conj_stdRankOne_theta_F4 hK hνθ, hν_R] at hpair
  exact ⟨_, hpair⟩

theorem linearBlockStandardPair_of_split_F4 [NeZero e] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .F4 0 p e)
    {R₂ : Subgroup ↥(adjointGroup .F4 (GaloisField p e))}
    (hR₂ : R₂ ∈ longestFundamental (f4Datum (GaloisField p e)))
    {c₂ u : ↥(adjointGroup .F4 (GaloisField p e))} (hc₂ : c₂ ∈ R₂) (ho : orderOf c₂ = 2)
    (hu : (u : ModGL .F4 (GaloisField p e)) * signDiagF4 (GaloisField p e) thetaF4 =
      signDiagF4 (GaloisField p e) thetaF4 * (u : ModGL .F4 (GaloisField p e)))
    (hcu : ((u * c₂ * u⁻¹ : ↥(adjointGroup .F4 (GaloisField p e))) :
      ModGL .F4 (GaloisField p e)) = signDiagF4 (GaloisField p e) deltaF4) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (f4Datum (GaloisField p e)) thetaF4) R₂ := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hδ₀ := isPartnerF4_deltaF4
  let dδ₀ : ↥(adjointGroup .F4 (GaloisField p e)) :=
    ⟨signDiagF4 (GaloisField p e) deltaF4, signDiagF4_mem_adjointGroup hδ₀.1 hδ₀.2.1⟩
  have hdG : dδ₀ ∈ stdRankOne (f4Datum (GaloisField p e)) deltaF4 :=
    signDiagF4_mem_stdRankOne hδ₀.1 hδ₀.2.1
  have hc₂' : u * c₂ * u⁻¹ = dδ₀ := Subtype.ext hcu
  have hRδ₀ := stdRankOne_mem_longestFundamental (p := p) (e := e) hδ₀.1 hδ₀.2.1
  have hR₂u : R₂.map (MulAut.conj u).toMonoidHom = stdRankOne (f4Datum (GaloisField p e)) deltaF4 :=
    eq_of_mem_longestFundamental_F4 hp2 hadm (map_conj_mem_longestFundamental u hR₂) hRδ₀
      (c := u * c₂ * u⁻¹) ⟨c₂, hc₂, rfl⟩ (hc₂' ▸ hdG) (a2_orderOf_conj_eq_two ho u)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaF4 hp2 hadm
  have huinv : ((u⁻¹ : ↥(adjointGroup .F4 (GaloisField p e))) : ModGL .F4 (GaloisField p e)) *
      signDiagF4 (GaloisField p e) thetaF4 = signDiagF4 (GaloisField p e) thetaF4 *
        ((u⁻¹ : ↥(adjointGroup .F4 (GaloisField p e))) : ModGL .F4 (GaloisField p e)) := by
    rw [Subgroup.coe_inv]
    calc (u : ModGL .F4 (GaloisField p e))⁻¹ * signDiagF4 (GaloisField p e) thetaF4 =
        (u : ModGL .F4 (GaloisField p e))⁻¹ * (signDiagF4 (GaloisField p e) thetaF4 *
          (u : ModGL .F4 (GaloisField p e))) * (u : ModGL .F4 (GaloisField p e))⁻¹ := by group
      _ = (u : ModGL .F4 (GaloisField p e))⁻¹ * ((u : ModGL .F4 (GaloisField p e)) *
          signDiagF4 (GaloisField p e) thetaF4) * (u : ModGL .F4 (GaloisField p e))⁻¹ := by
        rw [hu]
      _ = _ := by group
  have hfin := linearBlockStandardPair_map_conj hW₁ u⁻¹
  rw [map_conj_stdRankOne_theta_F4 hK huinv, ← hR₂u, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

end Split

end CFSG.ClassicalInvolution.ModelFacts.Levi
