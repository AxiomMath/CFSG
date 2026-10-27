module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankOneCover
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.Milestones.LR_dihedral_simple_recognition
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularity
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] : oddCore G = pPrimeCore 2 G := by
  simp only [oddCore, pPrimeCore, Nat.coprime_two_left]

theorem open_isSubnormal_of_isPComponent {X : Type*} [Group X] {C J : Subgroup X} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) : Open.IsSubnormal J C := by
  obtain ⟨-, -, hsub, -, -⟩ := hJ
  have h := Components.chain_of_mathlib_subnormal hsub
  have hmap : ∀ {H K : Subgroup ↥C}, Open.IsSubnormal H K →
      Open.IsSubnormal (H.map C.subtype) (K.map C.subtype) := by
    intro H K hHK
    induction hHK with
    | refl H => exact .refl _
    | @step H M K hHM hn _ ih =>
      refine .step (map_mono hHM) ?_ ih
      rw [normal_subgroupOf_iff (map_mono hHM)]
      rintro _ _ ⟨h, hh, rfl⟩ ⟨m, hm, rfl⟩
      exact ⟨m * h * m⁻¹, (normal_subgroupOf_iff hHM).mp hn h m hh hm, by simp⟩
  have h' := hmap h
  rwa [subgroupOf_map_subtype, inf_eq_left.mpr hJC, ← MonoidHom.range_eq_map,
    range_subtype] at h'

theorem isQuasisimple_quotient_of_isPComponent {X : Type*} [Group X] [Finite X]
    {C J : Subgroup X} (hJC : J ≤ C) (hJ : IsPComponent 2 (J.subgroupOf C)) :
    IsQuasisimple (J ⧸ pPrimeCore 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CatalogueBPrimeJoin.quasisimple_primeCore_quotient_of_equiv 2 (subgroupOfEquivOfLe hJC)
    (CatalogueBHeldSmallCore.pComponent_coreQuotient_quasisimple 2 _ hJ)

theorem ringChar_ne_two_of_card {K : Type*} [Field K] [Finite K] {p f : ℕ} (hp : Odd p)
    (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  have : Fintype K := Fintype.ofFinite K
  intro h
  have h0 := FiniteField.even_card_iff_char_two.mp h
  rw [← Nat.card_eq_fintype_card, hK] at h0
  have h1 : p ^ f % 2 = 1 := Nat.odd_iff.mp hp.pow
  omega

theorem classicalInvolutionWitness_of_pRank_le_one {G : Type} [Group G] (J : Subgroup G)
    [Finite J] (hJq : IsQuasisimple (J ⧸ pPrimeCore 2 J)) (hrank : CFSG.pRank 2 J ≤ 1) :
    Open.classicalInvolutionWitness J ∧ ∃ r : ℕ, 3 ≤ r ∧
      ∀ S : Sylow 2 J, Nonempty ((S : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hAn : IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (oddCore_eq_pPrimeCore_two J)).symm hJq
  have hAq : Open.IsQuasisimple (J ⧸ CFSG.oddCore J) :=
    (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hAn
  obtain ⟨-, _, -, -, -, hZcard, r, hr, hSJ, -, hTs, hTnab, hTsyl, hcover⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrank hAn
  refine ⟨?_, r, hr, hSJ⟩
  have : IsSimpleGroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J)) := hTs
  obtain ⟨P⟩ : Nonempty (Sylow 2 ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) :=
    inferInstance
  obtain ⟨⟨eP⟩, -, -⟩ := hTsyl P
  have hP : Nonempty ((P : Subgroup ((J ⧸ CFSG.oddCore J) ⧸ center (J ⧸ CFSG.oddCore J))) ≃*
      DihedralGroup (2 ^ ((r - 1) - 1))) := by
    rw [show r - 1 - 1 = r - 2 by omega]
    exact ⟨eP⟩
  rcases CFSG.Milestones.lr_dihedral_simple_recognition _ hTnab P (r - 1) (by omega) hP with
    ⟨p, f, hp, hp2, hf, hmodel⟩ | h7
  · have hfact : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hmodel
    obtain ⟨F, -, -⟩ := hcover K (ringChar_ne_two_of_card (hp.odd_of_ne_two hp2) hK)
      (eK.trans ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        (LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K)))
    exact Or.inl ⟨p, f, hfact, hp2, hf, ⟨F.trans (ClassicalModels.specialLinearFieldEquiv
      (ClassicalModels.finiteFieldEquivGaloisField K p f hf hK) (Fin 2))⟩⟩
  · exact Or.inr ⟨hAq, hZcard, h7⟩

theorem oddLieType_of_classical_twoComponent (hCI : GSLit.ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    {z : X} (hz : orderOf z = 2) {J : Subgroup X} (hJz : J ≤ centralizer ({z} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({z} : Set X)))) (hzJ : z ∈ J)
    (hrank : CFSG.pRank 2 J ≤ 1) : Blueprint.OddLieType X := by
  have hJq := isQuasisimple_quotient_of_isPComponent hJz hJ
  obtain ⟨hwit, r, hr, hSJ⟩ := classicalInvolutionWitness_of_pRank_le_one J hJq hrank
  obtain ⟨S⟩ : Nonempty (Sylow 2 J) := inferInstance
  obtain ⟨eS⟩ := hSJ S
  let eF : Open.genFittingFStar X ≃* X :=
    (MulEquiv.subgroupCongr (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup
      hnonab)).trans Subgroup.topEquiv
  have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨eF.symm a, eF.symm b, fun h => hab (eF.symm.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  rcases (hCI X hFnonab z hz J hzJ (open_isSubnormal_of_isPComponent hJz hJ) S
      ⟨r, hr, ⟨eS⟩⟩).1 hwit with h | h
  · exact (ClassicalInvolution.oddLieType_congr eF).1 h
  ·
    exfalso
    obtain ⟨e⟩ := (ClassicalInvolution.isSporadic_congr eF).1 h
    let e' : X ≃* Blueprint.NativeSporadic.M11 := e
    have hez : orderOf (e' z) = 2 :=
      (orderOf_injective e'.toMonoidHom e'.injective z).trans hz
    obtain ⟨hc, hN⟩ :=
      Semidihedral.ProperSubgroupRegularity.m11_involution_centralizer_card_and_odd_core
        (e' z) hez
    obtain ⟨hc', -⟩ :=
      Semidihedral.ProperSubgroupRegularity.centralizer_card_and_core_of_equiv e' z hc hN
    have hJle : Nat.card J ≤ 48 := by
      rw [← hc']
      exact Subgroup.card_le_of_le hJz
    obtain ⟨-, hsimple, hna⟩ := hJq
    have h60 : 60 ≤ Nat.card ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) :=
      GroupTheory.nonabelian_simple_order_at_least_sixty hsimple hna
    have h1 : Nat.card ((J ⧸ pPrimeCore 2 J) ⧸ center (J ⧸ pPrimeCore 2 J)) ≤
        Nat.card (J ⧸ pPrimeCore 2 J) :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    have h2 : Nat.card (J ⧸ pPrimeCore 2 J) ≤ Nat.card J :=
      Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    omega

end CFSG.ComponentClassification.FooteLit
