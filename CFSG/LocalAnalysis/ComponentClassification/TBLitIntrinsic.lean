module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalSimpleFitting
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerRankOneTwoGroups
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.StandardRecognition
open scoped MatrixGroups

structure TBSetting (X : Type) [Group X] [Finite X] : Prop where
  simple : IsSimpleGroup X
  nonab : ∃ a b : X, a * b ≠ b * a
  kProper : Assembly.KProper Catalog X
  unbalanced : ∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥
  notU : ¬ OutcomeLocal.UOutcome X

variable {X : Type} [Group X] [Finite X]

theorem TBSetting.not_catalog (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (hX : TBSetting X) : ¬ Catalog X := by
  intro hcat
  have := hX.simple
  obtain ⟨-, -, -, -, htop⟩ := SmallLocal.simple_generalized_fitting_self_local X hX.nonab
  let e : GeneralizedFitting.subgroup X ≃* X := (MulEquiv.subgroupCongr htop).trans topEquiv
  have hs : IsSimpleGroup (GeneralizedFitting.subgroup X) := e.isSimpleGroup
  have hn : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hX.nonab
    refine ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact hX.notU (hUc X hs hn (SectionRank.catalog_of_mulEquiv e hcat) hX.unbalanced)

theorem open_isSubnormal_map_subtype {G : Type*} [Group G] {C : Subgroup G} {H K : Subgroup C}
    (h : Open.IsSubnormal H K) : Open.IsSubnormal (H.map C.subtype) (K.map C.subtype) :=
  h.map C.subtype

theorem open_isSubnormal_of_isPComponent {G : Type*} [Group G] {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Open.IsSubnormal J C := by
  obtain ⟨-, -, hsub, -, -⟩ := hJ
  have h := open_isSubnormal_map_subtype (Components.chain_of_mathlib_subnormal hsub)
  rwa [subgroupOf_map_subtype, inf_eq_left.mpr hJC, ← MonoidHom.range_eq_map,
    range_subtype] at h

theorem pRank_two_SL2_le_one {k : Type*} [Field k] (hk : ringChar k ≠ 2) :
    CFSG.pRank 2 (Matrix.SpecialLinearGroup (Fin 2) k) ≤ 1 := by
  classical
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have hsub : (A : Set (Matrix.SpecialLinearGroup (Fin 2) k)) ⊆ {1, -1} := by
    intro a ha
    have h2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    rcases (LocalAnalysis.ComponentInitial.sl2_sq_eq_one_iff hk a).mp h2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hle : Nat.card A ≤ 2 := by
    calc Nat.card A = Nat.card (A : Set (Matrix.SpecialLinearGroup (Fin 2) k)) := rfl
      _ ≤ Nat.card ({1, -1} : Set (Matrix.SpecialLinearGroup (Fin 2) k)) :=
        Nat.card_mono (Set.toFinite _) hsub
      _ ≤ 2 := by
        rw [Nat.card_coe_set_eq]
        exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  rw [hcard] at hle
  by_contra hr
  have : 2 ^ 2 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem classicalInvolutionOddCore_eq (J : Type*) [Group J] :
    Open.classicalInvolutionOddCore J = pPrimeCore 2 J :=
  oddCore_eq_pPrimeCore_two J

theorem intrinsic_SL2_exclusion (hCI : ClassicalInvolutionTheoremModels)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hX : TBSetting X) {δ : X}
    (hδ : orderOf δ = 2) {J : Subgroup X} (hJδ : J ≤ centralizer ({δ} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({δ} : Set X)))) (hδJ : δ ∈ J)
    {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (e : J ⧸ pPrimeCore 2 J ≃* SL(2, GaloisField p n)) : False := by
  have := hX.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar (GaloisField p n) ≠ 2 := by
    rw [ringChar.eq (GaloisField p n) p]
    exact hp2
  have hrank : CFSG.pRank 2 J ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 J) := fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
    rw [← GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd,
      UnbalancedLayer.pRank_eq_of_mulEquiv one_lt_two e]
    exact pRank_two_SL2_le_one hchar
  have hA : IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two J)).symm
      (twoComponent_coreQuotient_quasisimple hJδ hJ)
  obtain ⟨-, -, -, -, -, -, r, hr, hSJ, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hA
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨eS⟩ := hSJ S
  let eF : Open.genFittingFStar X ≃* X :=
    (MulEquiv.subgroupCongr (genFittingFStar_eq_top_of_isSimpleGroup hX.nonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hX.nonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  have hwit : Open.classicalInvolutionWitness J :=
    .inl ⟨p, n, inferInstance, hp2, hn,
      ⟨(QuotientGroup.quotientMulEquivOfEq (classicalInvolutionOddCore_eq J)).trans e⟩⟩
  have hout := (hCI X hFnonab δ hδ J hδJ (open_isSubnormal_of_isPComponent hJδ hJ) S
    ⟨r, hr, ⟨eS⟩⟩).1 hwit
  have hcatF : Catalog (Open.genFittingFStar X) := by
    rcases hout with ⟨t, m, q, f, -, -, -, hm⟩ | h
    · exact lieModel_catalog _ t m q f hm
    · exact .inr (.inr (.inr (.inr ⟨.M11, h⟩)))
  exact hX.not_catalog hUc (SectionRank.catalog_of_mulEquiv eF.symm hcatF)

end CFSG.ComponentClassification.TBLit
