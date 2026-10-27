module

public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Rational
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2E8Levi
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Form
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairChevalley
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
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main
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

theorem mem_stdRankOne_e8_iff' {β : Fin (Tag.rank .E8) → ℤ} (hβ : IsRoot .E8 β)
    (r : ↥(adjointGroup .E8 K)) :
    r ∈ stdRankOne (e8Datum K) β ↔
      ∃ A : SL2 K, (r : ModGL .E8 K) = rootSL2 .E8 K β A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E8) hβ
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E8 K hβ).1
  change r ∈ rootGroup (rootOperatorFamily .E8) K β ⊔
    rootGroup (rootOperatorFamily .E8) K (-β) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem rootSL2_HSL_eq_thetaDiag_E8 {β : Fin (Tag.rank .E8) → ℤ} (hβ : IsRoot .E8 β) (c : Kˣ) :
    rootSL2 .E8 K β (HSL c) = rootDiagUnit .E8 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E8 K hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  change rootTorusSL2 .E8 K β c = _
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E8 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E8 a : ModGL .E8 K) : Module.End K (RootModule .E8 K))
      (rootVec .E8 K (Pi.single i 1))) = ((a i : Kˣ) : K) • rootVec .E8 K (Pi.single i 1) := by
    change rootDiag a (rootVec .E8 K (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E8) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E8 i), hs]
  rw [h2] at h1
  have hne : rootVec .E8 K (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E8 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective K hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E8 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3

end RankOne

section Involutions

variable {K : Type} [Field K]

theorem eq_signDiagE8_of_orderOf_eq_two (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .E8) → ℤ}
    (hβ : IsRoot .E8 β) {c : ↥(adjointGroup .E8 K)}
    (hc : c ∈ stdRankOne (e8Datum K) β) (hc2 : orderOf c = 2) :
    (c : ModGL .E8 K) = signDiagE8 K β := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .E8 K β) :=
    ((exceptional_Lang_root_rank_one_data .E8 K β).2.2.2.2.2.2.2.1 hK).1
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e8_iff' hβ c).1 hc
  obtain ⟨hc1, hne⟩ := (orderOf_eq_prime_iff (p := 2)).1 hc2
  have hAA : A * A = 1 := by
    apply hinj
    rw [map_mul, map_one, ← hA]
    have := congrArg (fun x : ↥(adjointGroup .E8 K) => (x : ModGL .E8 K)) hc1
    simpa [sq] using this
  rcases sl2_sq_eq_one_A2 h2 hAA with rfl | rfl
  · exfalso
    apply hne
    exact Subtype.ext (by rw [hA, map_one]; rfl)
  · rw [hA]
    exact rootSL2_HSL_eq_thetaDiag_E8 hβ (-1)

theorem signDiagE8_mem_stdRankOne {β : Fin (Tag.rank .E8) → ℤ} (hβ : IsRoot .E8 β) :
    (⟨signDiagE8 K β, by
        rw [signDiagE8, ← rootSL2_HSL_eq_thetaDiag_E8 hβ (-1)]
        exact rootSL2_mem_adjointGroup _ _⟩ : ↥(adjointGroup .E8 K)) ∈
      stdRankOne (e8Datum K) β :=
  (mem_stdRankOne_e8_iff' hβ _).2 ⟨HSL (-1), (rootSL2_HSL_eq_thetaDiag_E8 hβ (-1)).symm⟩

theorem conj_mem_stdRankOne_of_mem_h1E8 {g : ↥(adjointGroup .E8 K)}
    (hg : (g : ModGL .E8 K) ∈ h1E8 K) {x : ↥(adjointGroup .E8 K)}
    (hx : x ∈ stdRankOne (e8Datum K) thetaE8) : g * x * g⁻¹ ∈ stdRankOne (e8Datum K) thetaE8 := by
  obtain ⟨B, hB⟩ := (mem_stdRankOne_e8_iff' isRoot_thetaE8 x).1 hx
  obtain ⟨n, hn, A, hgA⟩ := hg
  obtain ⟨A', hA'⟩ := exists_levi_conj_rootSL2_eq hn (A * B * A⁻¹)
  refine (mem_stdRankOne_e8_iff' isRoot_thetaE8 _).2 ⟨A', ?_⟩
  rw [← hA']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgA, hB, map_mul, map_inv]
  group

theorem mem_h1E8_of_commute_signDiagE8 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E8 K)}
    (hu : (u : ModGL .E8 K) * signDiagE8 K thetaE8 = signDiagE8 K thetaE8 * (u : ModGL .E8 K)) :
    (u : ModGL .E8 K) ∈ h1E8 K := by
  have hcT : (u : ModGL .E8 K) ∈ toralCentralizer .E8 K (thetaDiag thetaE8 (-1 : Kˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨u.2, ?_⟩
    show signDiagE8 K thetaE8 * (u : ModGL .E8 K) * (signDiagE8 K thetaE8)⁻¹ = u
    rw [mul_inv_eq_iff_eq_mul, hu]
  exact toralRootGroup_le_h1E8 hK
    (toralCentralizer_le_toralRootGroup_of_sign (Or.inr (Or.inr (Or.inr rfl))) hK
      (thetaDiag_neg_one_sign thetaE8) hcT)

theorem map_conj_stdRankOne_theta_E8 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E8 K)}
    (hu : (u : ModGL .E8 K) * signDiagE8 K thetaE8 = signDiagE8 K thetaE8 * (u : ModGL .E8 K)) :
    (stdRankOne (e8Datum K) thetaE8).map (MulAut.conj u).toMonoidHom =
      stdRankOne (e8Datum K) thetaE8 := by
  have hu1 := mem_h1E8_of_commute_signDiagE8 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .E8 K)) : ModGL .E8 K) ∈ h1E8 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact conj_mem_stdRankOne_of_mem_h1E8 hu1 hr
  · intro hx
    refine ⟨u⁻¹ * x * u, ?_, ?_⟩
    · have := conj_mem_stdRankOne_of_mem_h1E8 hu' hx
      simpa using this
    · show u * (u⁻¹ * x * u) * u⁻¹ = x
      group

end Involutions

section Partner

theorem isPartnerE8_of_isPartner {K : Type} [Field K] {δ : Fin (Tag.rank .E8) → ℤ}
    (hlong : ModelFacts.IsLongestRoot (e8Datum K) δ)
    (hp : IsPartner (e8Datum K).isFiniteType thetaE8 δ) : IsPartnerE8 δ := by
  obtain ⟨hmem, -⟩ := (isLongestRoot_iff _ _).1 hlong
  have hδ : IsRoot .E8 δ := isRoot_iff_mem_roots.2 hmem
  obtain ⟨c, hc, hform⟩ := form_eq_iform_tag .E8 (e8Datum K).isFiniteType
  refine ⟨hδ, ?_⟩
  rw [IsPartner, lenSq, hform, hform] at hp
  have h3 : c * (2 * (iform thetaE8 δ : ℚ)) = c * (-2) := by
    have : (iform δ δ : ℚ) = 2 := by exact_mod_cast iform_self_isRoot_E8 hδ
    rw [this] at hp
    linear_combination hp
  have h4 := mul_left_cancel₀ hc.ne' h3
  have : (iform thetaE8 δ : ℚ) = -1 := by linarith
  exact_mod_cast this

end Partner

section Final

variable {K : Type} [Field K]

theorem conj_mem_stdRankOne_iff_E8 (hK : ringChar K ≠ 2) {u : ↥(adjointGroup .E8 K)}
    (hu : (u : ModGL .E8 K) * signDiagE8 K thetaE8 = signDiagE8 K thetaE8 * (u : ModGL .E8 K))
    {w : ↥(adjointGroup .E8 K)} :
    u * w * u⁻¹ ∈ stdRankOne (e8Datum K) thetaE8 ↔ w ∈ stdRankOne (e8Datum K) thetaE8 := by
  have hu1 := mem_h1E8_of_commute_signDiagE8 hK hu
  have hu' : ((u⁻¹ : ↥(adjointGroup .E8 K)) : ModGL .E8 K) ∈ h1E8 K := by
    rw [Subgroup.coe_inv]
    exact inv_mem hu1
  constructor
  · intro hw
    have := conj_mem_stdRankOne_of_mem_h1E8 hu' hw
    simpa [mul_assoc] using this
  · exact conj_mem_stdRankOne_of_mem_h1E8 hu1

end Final

section Unique

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

omit [NeZero e] in
theorem isLongestRoot_e8Datum (hadm : StatedLieAdmissible .E8 0 p e) {β : Fin (Tag.rank .E8) → ℤ}
    (hβ : IsRoot .E8 β) : ModelFacts.IsLongestRoot (e8Datum (GaloisField p e)) β :=
  isLongestRoot_of_mem_roots_of_forall_single _ rfl
    (fun k => isLongestRoot_single .E8 0 p e Fact.out trivial hadm k trivial)
    (mem_adjDatum_roots.2 hβ)

omit [NeZero e] in
theorem stdRankOne_mem_longestFundamental_E8 (hadm : StatedLieAdmissible .E8 0 p e)
    {β : Fin (Tag.rank .E8) → ℤ} (hβ : IsRoot .E8 β) :
    stdRankOne (e8Datum (GaloisField p e)) β ∈
      longestFundamental (e8Datum (GaloisField p e)) := by
  refine ⟨1, β, isLongestRoot_e8Datum hadm hβ, ?_⟩
  have : (MulAut.conj (1 : ↥(adjointGroup .E8 (GaloisField p e)))).toMonoidHom =
      MonoidHom.id _ := by
    ext x
    simp
  rw [this, Subgroup.map_id]
  rfl

omit [NeZero e] in
theorem eq_of_mem_longestFundamental_E8 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E8 0 p e)
    {R R' : Subgroup ↥(adjointGroup .E8 (GaloisField p e))}
    (hR : R ∈ longestFundamental (e8Datum (GaloisField p e)))
    (hR' : R' ∈ longestFundamental (e8Datum (GaloisField p e)))
    {c : ↥(adjointGroup .E8 (GaloisField p e))} (hc : c ∈ R) (hc' : c ∈ R')
    (hc2 : orderOf c = 2) : R = R' := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hsingle : Generic.FundamentalSingleClass .E8 (e8Datum (GaloisField p e)) :=
    fundamentalSingleClass .E8 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hθmem : stdRankOne (e8Datum (GaloisField p e)) thetaE8 ∈
      Generic.fundamentalSubgroups .E8 (e8Datum (GaloisField p e)) :=
    ⟨1, thetaE8, Or.inl (isLongestRoot_e8Datum hadm isRoot_thetaE8),
      (Generic.conjSub_one _).symm⟩
  obtain ⟨x, hx⟩ := hsingle _ hθmem R (longestFundamental_subset .E8 _ hR)
  obtain ⟨x', hx'⟩ := hsingle _ hθmem R' (longestFundamental_subset .E8 _ hR')
  have h1 : x⁻¹ * c * x ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8 :=
    Generic.mem_conjSub_iff.1 (hx ▸ hc)
  have h1' : x'⁻¹ * c * x' ∈ stdRankOne (e8Datum (GaloisField p e)) thetaE8 :=
    Generic.mem_conjSub_iff.1 (hx' ▸ hc')
  have ord : ∀ y : ↥(adjointGroup .E8 (GaloisField p e)), orderOf (y⁻¹ * c * y) = 2 := fun y => by
    rw [← hc2]
    have := orderOf_injective (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective c
    simpa [MulAut.conj_apply] using this
  have z1 := eq_signDiagE8_of_orderOf_eq_two hK isRoot_thetaE8 h1 (ord x)
  have z1' := eq_signDiagE8_of_orderOf_eq_two hK isRoot_thetaE8 h1' (ord x')
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at z1 z1'
  have hu : ((x'⁻¹ * x : ↥(adjointGroup .E8 (GaloisField p e))) : ModGL .E8 (GaloisField p e)) *
      signDiagE8 (GaloisField p e) thetaE8 = signDiagE8 (GaloisField p e) thetaE8 *
        ((x'⁻¹ * x : ↥(adjointGroup .E8 (GaloisField p e))) : ModGL .E8 (GaloisField p e)) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (↑x')⁻¹ * ↑x * signDiagE8 (GaloisField p e) thetaE8 =
        (↑x')⁻¹ * ↑x * ((↑x)⁻¹ * ↑c * ↑x) := by rw [z1]
      _ = (↑x')⁻¹ * ↑c * ↑x := by group
      _ = ((↑x')⁻¹ * ↑c * ↑x') * ((↑x')⁻¹ * ↑x) := by group
      _ = _ := by rw [z1']
  ext y
  rw [hx, hx', Generic.mem_conjSub_iff, Generic.mem_conjSub_iff]
  have e1 : x'⁻¹ * y * x' = (x'⁻¹ * x) * (x⁻¹ * y * x) * (x'⁻¹ * x)⁻¹ := by group
  rw [e1, conj_mem_stdRankOne_iff_E8 hK hu]

end Unique


section Split

variable {p e : ℕ} [Fact p.Prime]

local notation "Kq" => GaloisField p e

theorem signDiagE8_mem_adjointGroup {K : Type} [Field K] {β : Fin (Tag.rank .E8) → ℤ}
    (hβ : IsRoot .E8 β) : signDiagE8 K β ∈ adjointGroup .E8 K := by
  rw [signDiagE8, ← rootSL2_HSL_eq_thetaDiag_E8 hβ (-1)]
  exact rootSL2_mem_adjointGroup _ _

theorem orderOf_signDiagE8 {K : Type} [Field K] (hK : ringChar K ≠ 2) {β : Fin (Tag.rank .E8) → ℤ}
    (hβ : IsRoot .E8 β) :
    orderOf (⟨signDiagE8 K β, signDiagE8_mem_adjointGroup hβ⟩ : ↥(adjointGroup .E8 K)) = 2 := by
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hinj : Function.Injective (rootSL2 .E8 K β) :=
    ((exceptional_Lang_root_rank_one_data .E8 K β).2.2.2.2.2.2.2.1 hK).1
  refine (orderOf_eq_prime_iff (p := 2)).2 ⟨?_, ?_⟩
  · refine Subtype.ext ?_
    show signDiagE8 K β * signDiagE8 K β = 1
    exact rootDiagUnit_thetaDiag_mul_self β
  · intro h
    have h1 : signDiagE8 K β = 1 := congrArg Subtype.val h
    have h2' : rootSL2 .E8 K β (HSL (-1)) = 1 := by
      rw [rootSL2_HSL_eq_thetaDiag_E8 hβ (-1)]
      exact h1
    have := hinj (h2'.trans (map_one _).symm)
    have h3 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) this
    simp [coe_HSL] at h3
    exact Ring.neg_one_ne_one_of_char_ne_two hK h3

theorem linearBlockStandardPair_theta_deltaE8 [NeZero e] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e8Datum (GaloisField p e)) thetaE8)
      (stdRankOne (e8Datum (GaloisField p e)) deltaE8) := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hδ₀ := isPartnerE8_deltaE8
  have hθlong : ModelFacts.IsLongestRoot (e8Datum (GaloisField p e)) thetaE8 :=
    isLongestRoot_e8Datum hadm isRoot_thetaE8
  obtain ⟨δ', hδ'l, hδ'p, W, hW⟩ := exists_standardPair_partner_E8 p e hadm hθlong
  have hδ'PF : IsPartnerE8 δ' := isPartnerE8_of_isPartner hδ'l hδ'p
  obtain ⟨W', hW'⟩ : ∃ W' : Subgroup ↥(adjointGroup .E8 (GaloisField p e)),
      WeakCT.LinearBlockStandardPair (GaloisField p e) W'
        (stdRankOne (e8Datum (GaloisField p e)) thetaE8)
        (stdRankOne (e8Datum (GaloisField p e)) δ') := ⟨W, hW⟩
  obtain ⟨n, hn, hnd⟩ := exists_levi_conj_partnerE8 (F := GaloisField p e) hδ'PF
  have hnG : n ∈ adjointGroup .E8 (GaloisField p e) := parabolicSubgroup_le_adjointGroup _ _ _
    (parabolicLevi_le_parabolicSubgroup JE8 hn)
  let ν : ↥(adjointGroup .E8 (GaloisField p e)) := ⟨n⁻¹, inv_mem hnG⟩
  have hνθ : (ν : ModGL .E8 (GaloisField p e)) * signDiagE8 (GaloisField p e) thetaE8 =
      signDiagE8 (GaloisField p e) thetaE8 * (ν : ModGL .E8 (GaloisField p e)) :=
    (rootDiagUnit_thetaDiag_comm_levi (-1 : (GaloisField p e)ˣ) (inv_mem hn)).symm
  let dδ' : ↥(adjointGroup .E8 (GaloisField p e)) :=
    ⟨signDiagE8 (GaloisField p e) δ', signDiagE8_mem_adjointGroup hδ'PF.1⟩
  let dδ₀ : ↥(adjointGroup .E8 (GaloisField p e)) :=
    ⟨signDiagE8 (GaloisField p e) deltaE8, signDiagE8_mem_adjointGroup hδ₀.1⟩
  have hdδ' : dδ' ∈ stdRankOne (e8Datum (GaloisField p e)) δ' :=
    signDiagE8_mem_stdRankOne hδ'PF.1
  have hdδ₀ : dδ₀ ∈ stdRankOne (e8Datum (GaloisField p e)) deltaE8 :=
    signDiagE8_mem_stdRankOne hδ₀.1
  have hνd : ν * dδ' * ν⁻¹ = dδ₀ := by
    refine Subtype.ext ?_
    have h1 : n * signDiagE8 (GaloisField p e) deltaE8 * n⁻¹ =
        signDiagE8 (GaloisField p e) δ' := hnd
    show n⁻¹ * signDiagE8 (GaloisField p e) δ' * (n⁻¹)⁻¹ = signDiagE8 (GaloisField p e) deltaE8
    rw [← h1]
    group
  have hRδ₀ := stdRankOne_mem_longestFundamental_E8 (p := p) (e := e) hadm hδ₀.1
  have hRδ' := stdRankOne_mem_longestFundamental_E8 (p := p) (e := e) hadm hδ'PF.1
  have hν_R : (stdRankOne (e8Datum (GaloisField p e)) δ').map (MulAut.conj ν).toMonoidHom =
      stdRankOne (e8Datum (GaloisField p e)) deltaE8 :=
    eq_of_mem_longestFundamental_E8 hp2 hadm (map_conj_mem_longestFundamental ν hRδ') hRδ₀
      (c := dδ₀) ⟨dδ', hdδ', hνd⟩ hdδ₀ (orderOf_signDiagE8 hK hδ₀.1)
  have hpair := linearBlockStandardPair_map_conj hW' ν
  rw [map_conj_stdRankOne_theta_E8 hK hνθ, hν_R] at hpair
  exact ⟨_, hpair⟩

theorem linearBlockStandardPair_of_split_E8 [NeZero e] (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .E8 0 p e)
    {R₂ : Subgroup ↥(adjointGroup .E8 (GaloisField p e))}
    (hR₂ : R₂ ∈ longestFundamental (e8Datum (GaloisField p e)))
    {c₂ u : ↥(adjointGroup .E8 (GaloisField p e))} (hc₂ : c₂ ∈ R₂) (ho : orderOf c₂ = 2)
    (hu : (u : ModGL .E8 (GaloisField p e)) * signDiagE8 (GaloisField p e) thetaE8 =
      signDiagE8 (GaloisField p e) thetaE8 * (u : ModGL .E8 (GaloisField p e)))
    (hcu : ((u * c₂ * u⁻¹ : ↥(adjointGroup .E8 (GaloisField p e))) :
      ModGL .E8 (GaloisField p e)) = signDiagE8 (GaloisField p e) deltaE8) :
    ∃ W, WeakCT.LinearBlockStandardPair (GaloisField p e) W
      (stdRankOne (e8Datum (GaloisField p e)) thetaE8) R₂ := by
  have hK := ringChar_galoisField_ne_two (p := p) (e := e) hp2
  have hδ₀ := isPartnerE8_deltaE8
  let dδ₀ : ↥(adjointGroup .E8 (GaloisField p e)) :=
    ⟨signDiagE8 (GaloisField p e) deltaE8, signDiagE8_mem_adjointGroup hδ₀.1⟩
  have hdG : dδ₀ ∈ stdRankOne (e8Datum (GaloisField p e)) deltaE8 :=
    signDiagE8_mem_stdRankOne hδ₀.1
  have hc₂' : u * c₂ * u⁻¹ = dδ₀ := Subtype.ext hcu
  have hRδ₀ := stdRankOne_mem_longestFundamental_E8 (p := p) (e := e) hadm hδ₀.1
  have hR₂u : R₂.map (MulAut.conj u).toMonoidHom = stdRankOne (e8Datum (GaloisField p e)) deltaE8 :=
    eq_of_mem_longestFundamental_E8 hp2 hadm (map_conj_mem_longestFundamental u hR₂) hRδ₀
      (c := u * c₂ * u⁻¹) ⟨c₂, hc₂, rfl⟩ (hc₂' ▸ hdG) (a2_orderOf_conj_eq_two ho u)
  obtain ⟨W₁, hW₁⟩ := linearBlockStandardPair_theta_deltaE8 hp2 hadm
  have huinv : ((u⁻¹ : ↥(adjointGroup .E8 (GaloisField p e))) : ModGL .E8 (GaloisField p e)) *
      signDiagE8 (GaloisField p e) thetaE8 = signDiagE8 (GaloisField p e) thetaE8 *
        ((u⁻¹ : ↥(adjointGroup .E8 (GaloisField p e))) : ModGL .E8 (GaloisField p e)) := by
    rw [Subgroup.coe_inv]
    calc (u : ModGL .E8 (GaloisField p e))⁻¹ * signDiagE8 (GaloisField p e) thetaE8 =
        (u : ModGL .E8 (GaloisField p e))⁻¹ * (signDiagE8 (GaloisField p e) thetaE8 *
          (u : ModGL .E8 (GaloisField p e))) * (u : ModGL .E8 (GaloisField p e))⁻¹ := by group
      _ = (u : ModGL .E8 (GaloisField p e))⁻¹ * ((u : ModGL .E8 (GaloisField p e)) *
          signDiagE8 (GaloisField p e) thetaE8) * (u : ModGL .E8 (GaloisField p e))⁻¹ := by
        rw [hu]
      _ = _ := by group
  have hfin := linearBlockStandardPair_map_conj hW₁ u⁻¹
  rw [map_conj_stdRankOne_theta_E8 hK huinv, ← hR₂u, a2_map_conj_inv_map_conj] at hfin
  exact ⟨_, hfin⟩

end Split

end CFSG.ClassicalInvolution.ModelFacts.Levi
