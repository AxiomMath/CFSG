module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SFL
public import CFSG.LocalAnalysis.ComponentClassification.Foote5WLemma14
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsFinal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsSuz
public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClass
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4

public section

namespace CFSG.ComponentClassification.GrSLit.SFL

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

theorem solomonFixedLayer_at_of_solomonMaximal (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hsF : IsSimpleGroup (GeneralizedFitting.subgroup G))
    (hnF : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hoF : ¬ Blueprint.OddLieType (GeneralizedFitting.subgroup G))
    (hK : Assembly.KProper Blueprint.Catalog G) {a : G} {J : Subgroup G} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G))))
    (hL34 : IsL34Type (J ⧸ Open.fusionZStar J)) (hJmax : FooteLit.IsSolomonMaximal J) (g : G)
    (hbN : g⁻¹ * a * g ∈ normalizer (J : Set G))
    (hbO : ∀ j ∈ J, j⁻¹ * (g⁻¹ * a * g)⁻¹ * j * (g⁻¹ * a * g) ∈ oddIn J) :
    gsFixedLayer J (g⁻¹ * a * g) ≤ oddIn (centralizer ({g⁻¹ * a * g} : Set G)) ⊔ conjugate J g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnab : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnF
    exact ⟨x, y, fun h => hxy (Subtype.ext h)⟩
  have hA := Sol76.aschbacherRankOneInput_of_classicalInvolution hCI hGA
  have hJs : J ∈ FooteLit.solomonKStar G :=
    Sol76.mem_solomonKStar_of_aschbacher hA hsF hnF hoF hJmax
  set b := g⁻¹ * a * g
  have hb2 : orderOf b = 2 := by
    have h1 : (MulAut.conj g⁻¹) a = b := by
      rw [MulAut.conj_apply, inv_inv]
    rw [← h1, MulEquiv.orderOf_eq]
    exact ha
  have hbK : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨hbN, hbO⟩
  have hT2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hTne : zpowers b ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hb2
    norm_num at hb2
  have hCT : centralizer ((zpowers b : Subgroup G) : Set G) = centralizer ({b} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have h212 := Sol76.lemma212Input G J (zpowers b) hJs hTne hT2 (zpowers_le.mpr hbK)
  rw [hCT] at h212
  have hJtc : FooteLit.IsTwoComponentIn J (centralizer ({a} : Set G)) := ⟨hJa, hJp⟩
  have hJgtc : FooteLit.IsTwoComponentIn (conjugate J g) (centralizer ({b} : Set G)) := by
    have h := Sol76.isTwoComponentIn_map (MulAut.conj g⁻¹) hJtc
    have h2 : (centralizer ({a} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        centralizer ({b} : Set G) := conjugate_centralizer_eq a g
    rw [h2] at h
    exact h
  have hJgs : conjugate J g ∈ FooteLit.solomonKStar G := Sol76.conjugate_mem_solomonKStar hJs g
  have huniq : ∀ M : Subgroup G, M ∈ Sol76.kStarComponents (centralizer ({b} : Set G)) →
      M = conjugate J g := by
    intro M hM
    by_contra hne
    rcases Foote5.SolMax.isKBalanced_or_psp4_of_centralizer
        (Sol76T13.R12.Pcls.quasisimpleRankTwoSymplecticInput_of_suz
            Sol76T13.R12.Pcls.sporadicCoverRankInput_Suz) hnab hK hb2
        (M := conjugate J g) ⟨hJgtc, hJgs⟩ hM (Ne.symm hne) with
      hbal | ⟨k, _, _, hk, ⟨eM⟩⟩
    · exact h13 G inferInstance hnab hK _ hbal
    · obtain ⟨e⟩ := FooteLit.nonempty_quotient_fusionZStar_equiv
        (J.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective)
      exact Sol78.not_psp4_of_l34 hL34 ⟨k, inferInstance, inferInstance, hk, ⟨e.trans eM⟩⟩
  have hKJ : FooteLit.solomonKStarOf (centralizer ({b} : Set G)) ≤ conjugate J g :=
    iSup₂_le fun M hM => (huniq M hM).le
  exact (h212.trans hKJ).trans le_sup_right

end CFSG.ComponentClassification.GrSLit.SFL
