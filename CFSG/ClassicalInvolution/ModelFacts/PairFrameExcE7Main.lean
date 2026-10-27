module

public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE7Rational
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcSigns
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcReduceToral
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE7
public import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Main
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.BootstrapDischarge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationInner
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalE6
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLayer
public import CFSG.ClassicalInvolution.Models.Transfer
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

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section Adjoint

variable {K : Type} [Field K]

noncomputable abbrev e7AdjDatum (K : Type) [Field K] : UniversalRootDatum ↥(adjointGroup .E7 K) :=
  CFSG.LieType.Steinberg.Adjoint.adjDatum (rootOperatorFamily .E7) K

theorem rootDiagUnit_thetaDiag_mul_self_E7 (δ : Fin (Tag.rank .E7) → ℤ) :
    rootDiagUnit .E7 (thetaDiag δ (-1 : Kˣ)) * rootDiagUnit .E7 (thetaDiag δ (-1 : Kˣ)) = 1 := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  funext i
  rcases thetaDiag_neg_one_sign_E7 (F := K) δ i with h | h <;> simp [h]

theorem mem_stdRankOne_e7_iff (r : ↥(adjointGroup .E7 K)) :
    r ∈ stdRankOne (e7AdjDatum K) thetaE7 ↔
      ∃ A : SL2 K, (r : ModGL .E7 K) = rootSL2 .E7 K thetaE7 A := by
  have hb := subgroupOf_rootSubgroup_sup_eq (K := K) (rootOperatorFamily .E7) isRoot_thetaE7
  have hL := (exceptional_Lang_root_rank_one_torus_transport .E7 K isRoot_thetaE7).1
  change r ∈ rootGroup (rootOperatorFamily .E7) K thetaE7 ⊔
    rootGroup (rootOperatorFamily .E7) K (-thetaE7) ↔ _
  rw [← hb, Subgroup.mem_subgroupOf, ← hL, rootRankOneGroup, MonoidHom.mem_range]
  exact exists_congr fun A => eq_comm

theorem central_stdRankOne_e7 (hK : ringChar K ≠ 2) {z : ↥(adjointGroup .E7 K)}
    (hz : z ∈ stdRankOne (e7AdjDatum K) thetaE7)
    (hzc : ∀ r ∈ stdRankOne (e7AdjDatum K) thetaE7, z * r = r * z) :
    (z : ModGL .E7 K) = 1 ∨
      (z : ModGL .E7 K) = rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Kˣ)) := by
  obtain ⟨A, hA⟩ := (mem_stdRankOne_e7_iff z).1 hz
  have hinj : Function.Injective (rootSL2 .E7 K thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 K thetaE7).2.2.2.2.2.2.2.1 hK).1
  have hcomm : ∀ B : SL2 K, A * B = B * A := fun B => by
    apply hinj
    have hB : (⟨rootSL2 .E7 K thetaE7 B, rootSL2_mem_adjointGroup _ _⟩ :
        ↥(adjointGroup .E7 K)) ∈ stdRankOne (e7AdjDatum K) thetaE7 :=
      (mem_stdRankOne_e7_iff _).2 ⟨B, rfl⟩
    have := congrArg Subtype.val (hzc _ hB)
    simp only [Subgroup.coe_mul] at this
    rw [hA] at this
    rw [map_mul, map_mul]
    exact this
  rcases eq_one_or_HSL_neg_one_of_forall_commute hcomm with h | h
  · left
    rw [hA, h, map_one]
  · right
    rw [hA, h]
    exact rootTorusSL2_thetaE7 (-1)

end Adjoint

section Model

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

local notation "ε" => e7Isogeny (GaloisField p e)

abbrev E7sc (p e : ℕ) [Fact p.Prime] : Type := ↥(e7Data_valid.minGroup (GaloisField p e))

omit [NeZero e] in
theorem map_stdRankOne_e7 :
    (stdRankOne (e7Datum (GaloisField p e)) thetaE7).map (e7Isogeny (GaloisField p e)) =
      stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7 := by
  change ((e7Datum (GaloisField p e)).rootGroup thetaE7 ⊔
      (e7Datum (GaloisField p e)).rootGroup (-thetaE7)).map (e7Isogeny (GaloisField p e)) =
    rootGroup (rootOperatorFamily .E7) (GaloisField p e) thetaE7 ⊔
      rootGroup (rootOperatorFamily .E7) (GaloisField p e) (-thetaE7)
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) (map_e7Isogeny_rootGroup _ isRoot_thetaE7)
    (map_e7Isogeny_rootGroup _ (IsRoot.neg isRoot_thetaE7))

theorem mem_excSignGroup_e7 {u : E7sc p e} (δ : Fin (Tag.rank .E7) → ℤ)
    (hu : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) =
        rootDiagUnit .E7 (thetaDiag δ (-1 : (GaloisField p e)ˣ))) : u ∈ excSignGroup .E7 p e :=
  mem_excSignGroup.2 ⟨thetaDiag δ (-1), thetaDiag_neg_one_sign_E7 δ, hu⟩

theorem mem_excSignGroup_e7_of_eq_one {u : E7sc p e}
    (hu : ((e7Isogeny (GaloisField p e) u : ↥(adjointGroup .E7 (GaloisField p e))) :
      ModGL .E7 (GaloisField p e)) = 1) : u ∈ excSignGroup .E7 p e :=
  mem_excSignGroup.2 ⟨1, fun _ => Or.inl rfl, hu.trans rootDiagUnit_one.symm⟩

theorem hbase_e7 (hp2 : p ≠ 2) :
    ∀ c : E7sc p e,
      (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, c * r = r * c) →
      (∃ g z : E7sc p e, z ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7 ∧
        (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, z * r = r * z) ∧
        c = g * z * g⁻¹) →
      ∃ x : E7sc p e,
        (∀ z ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7,
          (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, z * r = r * z) →
            x * z * x⁻¹ ∈ excSignGroup .E7 p e) ∧
        x * c * x⁻¹ ∈ excSignGroup .E7 p e := by
  intro c hcR ⟨g, z, hz, hzc, hcg⟩
  have hK : ringChar (GaloisField p e) ≠ 2 := ringChar_galoisField_ne_two hp2
  have hKodd := odd_natCard_galoisField_of_ne_two (p := p) (e := e) hp2
  have hmap := map_stdRankOne_e7 (p := p) (e := e)
  have himg : ∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7,
      ε r ∈ stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7 := fun r hr => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hr
  have hlift : ∀ r' ∈ stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7,
      ∃ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, ε r = r' := fun r' hr' => by
    rw [← hmap] at hr'
    obtain ⟨r, hr, h⟩ := Subgroup.mem_map.1 hr'
    exact ⟨r, hr, h⟩
  have hcentral : ∀ z' ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7,
      (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, z' * r = r * z') →
        ((ε z' : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) = 1 ∨
        ((ε z' : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) =
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) := by
    intro z' hz' hz'c
    refine central_stdRankOne_e7 hK (himg z' hz') fun r' hr' => ?_
    obtain ⟨r, hr, rfl⟩ := hlift r' hr'
    rw [← map_mul, ← map_mul, hz'c r hr]
  have hcentral_mem : ∀ z' ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7,
      (∀ r ∈ stdRankOne (e7Datum (GaloisField p e)) thetaE7, z' * r = r * z') →
        ∀ ū : ModGL .E7 (GaloisField p e),
          ū * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) =
            rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) * ū →
          ∀ x : E7sc p e, ((ε x : ↥(adjointGroup .E7 (GaloisField p e))) :
              ModGL .E7 (GaloisField p e)) = ū → x * z' * x⁻¹ ∈ excSignGroup .E7 p e := by
    intro z' hz' hz'c ū hū x hx
    rcases hcentral z' hz' hz'c with h | h
    · refine mem_excSignGroup_e7_of_eq_one ?_
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h]
      group
    · refine mem_excSignGroup_e7 thetaE7 ?_
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, h, hx]
      calc ū * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) * ū⁻¹ =
          rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) * ū * ū⁻¹ := by
            rw [hū]
        _ = _ := by group
  rcases hcentral z hz hzc with hz1 | hzd
  ·
    have hc1 : ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) =
        1 := by
      rw [hcg, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hz1]
      group
    refine ⟨1, fun z' hz' hz'c => ?_, ?_⟩
    · have := hcentral_mem z' hz' hz'c 1 (by simp) 1 (by simp)
      simpa using this
    · rw [one_mul, inv_one, mul_one]
      exact mem_excSignGroup_e7_of_eq_one hc1
  ·
    have hcom : ∀ B : SL2 (GaloisField p e),
        ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) *
            rootSL2 .E7 (GaloisField p e) thetaE7 B =
          rootSL2 .E7 (GaloisField p e) thetaE7 B *
            ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) :=
      fun B => by
        have hB : (⟨rootSL2 .E7 (GaloisField p e) thetaE7 B, rootSL2_mem_adjointGroup _ _⟩ :
            ↥(adjointGroup .E7 (GaloisField p e))) ∈
              stdRankOne (e7AdjDatum (GaloisField p e)) thetaE7 :=
          (mem_stdRankOne_e7_iff _).2 ⟨B, rfl⟩
        obtain ⟨r, hr, hrB⟩ := hlift _ hB
        have := congrArg (fun y => ((ε y : ↥(adjointGroup .E7 (GaloisField p e))) :
          ModGL .E7 (GaloisField p e))) (hcR r hr)
        simp only [map_mul, Subgroup.coe_mul, hrB] at this
        exact this
    have hcL := mem_parabolicLevi_of_commute_rootSL2_E7 hK (ε c).2 hcom
    have hgc : ((ε g : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) *
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) *
          ((ε g : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))⁻¹ =
            ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) := by
      rw [← hzd, hcg, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hc2 : ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) *
        ((ε c : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) = 1 := by
      rw [← hgc]
      calc _ = ((ε g : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) *
          (rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ)) *
            rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField p e)ˣ))) *
          ((ε g : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e))⁻¹ := by
            group
        _ = 1 := by rw [rootDiagUnit_thetaDiag_mul_self_E7]; group
    rcases exists_rational_conj_e7 hKodd (ε c).2 (ε g).2 hc2 hcL (hcom (uSL 1)) hgc with
      hd | ⟨δ, hδ, ū, hū, hu1, hu2⟩
    · refine ⟨1, fun z' hz' hz'c => ?_, ?_⟩
      · have := hcentral_mem z' hz' hz'c 1 (by simp) 1 (by simp)
        simpa using this
      · rw [one_mul, inv_one, mul_one]
        exact mem_excSignGroup_e7 thetaE7 hd
    · obtain ⟨u, hu⟩ := e7Isogeny_surjective (GaloisField p e) ⟨ū, hū⟩
      have hu' : ((ε u : ↥(adjointGroup .E7 (GaloisField p e))) : ModGL .E7 (GaloisField p e)) =
          ū := congrArg Subtype.val hu
      refine ⟨u, fun z' hz' hz'c => hcentral_mem z' hz' hz'c ū hu2 u hu', ?_⟩
      refine mem_excSignGroup_e7 δ ?_
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu']
      exact hu1

theorem pairFrame_e7 (hp2 : p ≠ 2) (hadm : StatedLieAdmissible .E7 0 p e) :
    PairFrame (excSignGroup .E7 p e)
      (fundamentalSubgroups .E7 (Generic.modelUniv .E7 0 p e Fact.out).D) := by
  have hsingle : Generic.FundamentalSingleClass .E7 (Generic.modelUniv .E7 0 p e Fact.out).D :=
    fundamentalSingleClass .E7 0 p e Fact.out trivial hadm (by decide) (by decide)
  have hlong := isLongestRoot_single .E7 0 p e Fact.out trivial hadm
  have hθ : Generic.IsLongestRoot (Generic.modelUniv .E7 0 p e Fact.out).D thetaE7 :=
    isLongestRoot_of_mem_roots_of_forall_single _ rfl (fun k => hlong k trivial)
      ((e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 (GaloisField p e)).2
        isRoot_thetaE7)
  exact pairFrame_of_centralizer_toral (Generic.modelUniv .E7 0 p e Fact.out).D
    (excSignGroup .E7 p e) thetaE7 hθ hsingle (hbase_e7 hp2)

end Model

end CFSG.ClassicalInvolution.ModelFacts
