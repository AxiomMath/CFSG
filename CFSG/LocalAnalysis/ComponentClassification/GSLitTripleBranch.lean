module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitBridge
public import CFSG.LocalAnalysis.ComponentClassification.UFrontierBranches
public import CFSG.LocalAnalysis.ComponentClassification.AlternatingUnbalancedDegree
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUMathieuVanishing
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.Sporadic.SmallOddCore.J2
public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneQuaternionRecognition
public import CFSG.ClassicalInvolution.Basic
public import CFSG.ClassicalInvolution.OrderForm

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

theorem pRank_two_le_of_injective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) : CFSG.pRank 2 A ≤ CFSG.pRank 2 B := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact SectionRank.pRank_top_le_of_injective (by norm_num) f hf

theorem sylow_cyclic_or_quaternion_of_pRank_eq_one {G : Type*} [Group G] [Finite G]
    (h : CFSG.pRank 2 G = 1) (P : Sylow 2 G) :
    IsCyclic (P : Subgroup G) ∨
      ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank : DisconnectedInvolutionGraph.Helpers.NoCommutingDistinctInvolutions
      (P : Subgroup G) := by
    intro a b hab
    by_contra hne
    have ha : orderOf ((a : P) : G) = 2 := by rw [Subgroup.orderOf_coe]; exact a.2
    have hb : orderOf ((b : P) : G) = 2 := by rw [Subgroup.orderOf_coe]; exact b.2
    have hne' : ((b : P) : G) ∉ zpowers ((a : P) : G) := by
      intro hmem
      rcases UnbalancedGS.DihedralPair.mem_zpowers_eq_one_or_eq ha hmem with h1 | h1
      · rw [h1, orderOf_one] at hb
        exact absurd hb (by norm_num)
      · exact hne (Subtype.ext (Subtype.ext h1.symm))
    have h2 := UnbalancedGS.RankSmallSources.two_le_pRank_of_commuting ha hb
      (congrArg Subtype.val hab) hne'
    omega
  rcases DisconnectedInvolutionGraph.Helpers.rank_one_two_cyclic_or_quaternion P.isPGroup'
    hrank with hc | ⟨k, hk, ⟨φ⟩⟩
  · exact Or.inl hc
  · refine Or.inr ⟨k + 2, by omega, ⟨?_⟩⟩
    rw [Nat.add_sub_cancel]
    exact φ.symm

theorem card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

theorem card_sylow_two_of_card_eq_2520 {G : Type*} [Group G] [Finite G]
    (h : Nat.card G = 2520) (P : Sylow 2 G) : Nat.card (P : Subgroup G) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity P, h, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (315 : ℕ))]

theorem pRank_alternating_seven_le_two : CFSG.pRank 2 (alternatingGroup (Fin 7)) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [SectionRank.pRank_eq_open_pRank_top]
  refine SectionRank.pRank_le (by norm_num) fun E _ hE => ?_
  have hE2 : IsPGroup 2 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨P, hP⟩ := hE2.exists_le_sylow
  have hP8 := card_sylow_two_of_card_eq_2520 card_alternating_seven P
  have hdvd : Nat.card E ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hP8]
    exact Subgroup.card_dvd_of_le hP
  obtain ⟨k, hk, hkE⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hkE]
  by_cases hk2 : k ≤ 2
  · exact Nat.pow_le_pow_right (by norm_num) hk2
  exfalso
  have hk3 : k = 3 := by omega
  subst hk3
  have hEP : E = P := Subgroup.eq_of_le_of_card_ge hP (by rw [hP8, hkE]; norm_num)
  obtain ⟨m, -, ⟨φ⟩⟩ := GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven P
  have hcard : 2 * 2 ^ m = 8 := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr φ.toEquiv, hP8]
  have hm : m = 2 := by
    have h4 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h4
  subst hm
  have := hE.1
  have hcomm : ∀ a b : DihedralGroup (2 ^ 2), a * b = b * a := by
    intro a b
    have ha : ((φ.symm a : P) : alternatingGroup (Fin 7)) ∈ E := by
      rw [hEP]
      exact (φ.symm a).2
    have hb : ((φ.symm b : P) : alternatingGroup (Fin 7)) ∈ E := by
      rw [hEP]
      exact (φ.symm b).2
    have h1 : ((φ.symm a : P) : alternatingGroup (Fin 7)) * (φ.symm b : P) =
        (φ.symm b : P) * (φ.symm a : P) := by
      have h2 := congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : E) ⟨_, hb⟩)
      simpa using h2
    apply φ.symm.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact h1
  exact absurd (hcomm (DihedralGroup.r 1) (DihedralGroup.sr 0)) (by decide)

theorem pRank_two_of_mulEquiv_alternating_seven {G : Type*} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 7)) : CFSG.pRank 2 G = 2 := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
    ← SectionRank.pRank_eq_open_pRank_top]
  exact le_antisymm pRank_alternating_seven_le_two
    UnbalancedGS.RankSmallSources.two_le_pRank_alternating_seven

theorem harrisSolomonFritzA7Input_of_full (h : HarrisSolomonFritzInput) :
    HarrisSolomonFritzA7Input := by
  intro X _ _ _ hnonab t ht L hLt hL ⟨e7⟩ hcyc
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))
  obtain ⟨S⟩ : Nonempty (Sylow 2 (L ⧸ pPrimeCore 2 L)) := inferInstance
  exact h X hnonab t ht L hLt hL e7.isSimpleGroup (pRank_two_of_mulEquiv_alternating_seven e7)
    ⟨S, card_sylow_two_of_card_eq_2520
      (by rw [Nat.card_congr e7.toEquiv, card_alternating_seven]) S⟩ hcyc

section Simple

variable {X : Type} [Group X] [Finite X] [IsSimpleGroup X]

theorem uOutcome_of_oddLieType (h : Blueprint.OddLieType X) : OutcomeLocal.UOutcome X :=
  Or.inl ((ClassicalInvolution.oddLieType_congr generalizedFittingEquivOfSimple).2 h)

theorem uOutcome_of_mulEquiv_alternating_eleven (e : X ≃* alternatingGroup (Fin 11)) :
    OutcomeLocal.UOutcome X :=
  Or.inr (Or.inl ⟨11, ⟨5, rfl⟩, by norm_num, ⟨generalizedFittingEquivOfSimple.trans e⟩,
    fun h => absurd h (by norm_num)⟩)

theorem mod_four_eq_three_of_mulEquiv_alternating (hnonab : ∃ a b : X, a * b ≠ b * a)
    {n : ℕ} (hn : 7 ≤ n) (e : X ≃* alternatingGroup (Fin n))
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) : n % 4 = 3 := by
  let eF : GeneralizedFitting.subgroup X ≃* X := generalizedFittingEquivOfSimple
  have : IsSimpleGroup (GeneralizedFitting.subgroup X) := eF.isSimpleGroup
  have hFnonab : ∃ a b : GeneralizedFitting.subgroup X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  obtain ⟨z, hz2, hzc⟩ := hz
  obtain ⟨hodd, h1, -⟩ := AlternatingUnbalanced.alternating_generalized_fitting_unbalanced_degree
    hFnonab hn ⟨eF.trans e⟩ hz2 hzc
  have hn1 : n % 4 ≠ 1 := fun h => (h1 h).ne generalizedFitting_eq_top_of_simple
  obtain ⟨k, rfl⟩ := hodd
  omega

noncomputable def cfsgGeneralizedFittingEquivOfSimple : CFSG.generalizedFitting X ≃* X :=
  (MulEquiv.subgroupCongr (CFSG.generalizedFitting_eq_componentClassification X)).trans
    generalizedFittingEquivOfSimple

theorem false_of_mulEquiv_j2 (e : X ≃* Blueprint.NativeSporadic.J2)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) : False := by
  let eF : CFSG.generalizedFitting X ≃* X := cfsgGeneralizedFittingEquivOfSimple
  obtain ⟨z, hz2, hzc⟩ := hz
  exact hzc
    (Sporadic.SmallOddCore.ctuc_j2_generalized_fitting_involution_centralizer_odd_core_trivial
      eF.isSimpleGroup ⟨eF.trans e⟩ z hz2)

theorem false_of_mulEquiv_mathieu (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hM : Nonempty (X ≃* Blueprint.NativeSporadic.M11) ∨
      Nonempty (X ≃* Blueprint.NativeSporadic.M12))
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) : False := by
  let eF : CFSG.generalizedFitting X ≃* X := cfsgGeneralizedFittingEquivOfSimple
  have hFnonab : ∃ a b : CFSG.generalizedFitting X, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  obtain ⟨z, hz2, hzc⟩ := hz
  refine hzc (CatalogueU.catalog_mathieu_almost_simple_odd_core_vanishing eF.isSimpleGroup
    hFnonab ?_ z hz2)
  rcases hM with ⟨⟨eM⟩⟩ | ⟨⟨eM⟩⟩
  · exact Or.inl ⟨eF.trans eM⟩
  · exact Or.inr (Or.inl ⟨eF.trans eM⟩)

end Simple

theorem false_of_quaternion_kernel (hCI : ClassicalInvolutionInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {x : X} {L : Subgroup X} (hx : orderOf x = 2)
    (hLx : L ≤ centralizer ({x} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))))
    (hL2 : 2 ≤ CFSG.pRank 2 ↥L) (hrank : CFSG.pRank 2 ↥(coreActionKernel L) = 1)
    (P : Sylow 2 ↥(coreActionKernel L)) {r : ℕ} (hr : 3 ≤ r)
    (eP : (P : Subgroup ↥(coreActionKernel L)) ≃* QuaternionGroup (2 ^ (r - 2))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxC : x ∈ coreActionKernel L := mem_coreActionKernel_of_le_centralizer hLx
  set Cx := centralizer ({x} : Set X) with hCx
  by_cases hN : Cx ≤ normalizer (L : Set X)
  ·
    set J := coreActionKernel L ⊓ Cx with hJdef
    have hJC : J ≤ coreActionKernel L := inf_le_left
    have hJx : J ≤ Cx := inf_le_right
    have hxJ : x ∈ J := mem_inf.mpr ⟨hxC, mem_centralizer_singleton_iff.mpr rfl⟩
    have hCxJ : Cx ≤ normalizer (J : Set X) := fun g hg =>
      normalizer_inf_mem (normalizer_le_normalizer_coreActionKernel L (hN hg)) (le_normalizer hg)
    have hJn : (J.subgroupOf Cx).Normal := (normal_subgroupOf_iff_le_normalizer hJx).2 hCxJ
    have hsub : Open.IsSubnormal J Cx :=
      ClassicalInvolution.isSubnormal_of_normal_subgroupOf hJx hJn
    set x' : coreActionKernel L := ⟨x, hxC⟩ with hx'
    have hx'2 : orderOf x' = 2 := by rw [hx', Subgroup.orderOf_mk]; exact hx
    have hxP2 : IsPGroup 2 (zpowers x') :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2]; simp)
    obtain ⟨Q, hxQ⟩ := hxP2.exists_le_sylow
    have hxQ' : x' ∈ (Q : Subgroup (coreActionKernel L)) := hxQ (mem_zpowers _)
    let eQ : (Q : Subgroup (coreActionKernel L)) ≃* QuaternionGroup (2 ^ (r - 2)) :=
      (Sylow.equiv Q P).trans eP
    obtain ⟨u, -, hu, -⟩ :=
      ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup eQ
    have hxu : (⟨x', hxQ'⟩ : (Q : Subgroup (coreActionKernel L))) = u :=
      hu _ (by rw [Subgroup.orderOf_mk]; exact hx'2)
    have hQx : ∀ q ∈ (Q : Subgroup (coreActionKernel L)),
        ((q : coreActionKernel L) : X) ∈ Cx := by
      intro q hq
      have hconj : (⟨q, hq⟩ : (Q : Subgroup (coreActionKernel L))) * ⟨x', hxQ'⟩ *
          (⟨q, hq⟩ : (Q : Subgroup (coreActionKernel L)))⁻¹ = ⟨x', hxQ'⟩ := by
        rw [hxu]
        exact hu _ (by rw [ClassicalInvolution.orderOf_conj_eq, ← hxu, Subgroup.orderOf_mk]
                       exact hx'2)
      have h1 : ((q : coreActionKernel L) : X) * x * ((q : coreActionKernel L) : X)⁻¹ = x :=
        congrArg (fun w : (Q : Subgroup (coreActionKernel L)) =>
          ((w : coreActionKernel L) : X)) hconj
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1)
    have hrange : (Q : Subgroup (coreActionKernel L)) ≤ (inclusion hJC).range := fun q hq =>
      ⟨⟨q, mem_inf.mpr ⟨q.2, hQx q hq⟩⟩, rfl⟩
    let SJ : Sylow 2 J := Q.comapOfInjective (inclusion hJC) (inclusion_injective hJC) hrange
    have eJ : (SJ : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)) :=
      (((Q : Subgroup (coreActionKernel L)).comap (inclusion hJC)).equivMapOfInjective _
        (inclusion_injective hJC)).trans
        ((MulEquiv.subgroupCongr (map_comap_eq_self hrange)).trans eQ)
    have hTE : Open.classicalInvolutionTightlyEmbedded J :=
      (ClassicalInvolution.tightlyEmbedded_iff_centralizer_le_normalizer hxJ hx hJx SJ
        ⟨r, hr, ⟨eJ⟩⟩).2 hCxJ
    let eF : Open.genFittingFStar X ≃* X :=
      (MulEquiv.subgroupCongr
        (StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
        Subgroup.topEquiv
    have : IsSimpleGroup (Open.genFittingFStar X) := eF.isSimpleGroup
    have hFnonab : ∃ a b : Open.genFittingFStar X, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnonab
      exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
    rcases (hCI X hFnonab x hx J hxJ hsub SJ ⟨r, hr, ⟨eJ⟩⟩).2 hTE with h | h | h
    · exact hU (uOutcome_of_oddLieType ((ClassicalInvolution.oddLieType_congr eF).1 h))
    · obtain ⟨eM⟩ := (ClassicalInvolution.isSporadic_congr eF).1 h
      exact false_of_mulEquiv_mathieu hnonab (Or.inl ⟨eM⟩) hz
    · obtain ⟨eM⟩ := (ClassicalInvolution.isSporadic_congr eF).1 h
      exact false_of_mulEquiv_mathieu hnonab (Or.inr ⟨eM⟩) hz
  ·
    obtain ⟨c, hc, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hN
    set φ : X ≃* X := MulAut.conj c⁻¹ with hφ
    have hφx : φ x = x := by
      rw [hφ, MulAut.conj_apply, inv_inv]
      have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc
      calc c⁻¹ * x * c = c⁻¹ * (x * c) := by group
        _ = c⁻¹ * (c * x) := by rw [hcx]
        _ = x := by group
    obtain ⟨hL'x, hL'⟩ := isPComponent_map_centralizer φ hLx hL
    rw [hφx] at hL'x hL'
    set L' := L.map φ.toMonoidHom with hL'def
    have hne : L.subgroupOf Cx ≠ L'.subgroupOf Cx := by
      intro heq
      rw [subgroupOf_inj, inf_of_le_left hLx, inf_of_le_left hL'x] at heq
      exact hcN (mem_normalizer_of_conjugate_eq heq.symm)
    obtain ⟨hN1, -, hcomm, -⟩ :=
      (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hL
        hL').2 hne
    have hL'C : L' ≤ coreActionKernel L := by
      intro g hg
      have hg' : (⟨g, hL'x hg⟩ : Cx) ∈ L'.subgroupOf Cx := hg
      refine ⟨mem_normalizer_of_subgroupOf hLx (hN1 hg'), fun j hj => ?_⟩
      have hj' : (⟨j, hLx hj⟩ : Cx) ∈ L.subgroupOf Cx := hj
      have h1 := hcomm (commutator_mem_commutator (inv_mem hj') (inv_mem hg'))
      have h2 := mem_map_of_mem Cx.subtype (mem_inf.mp h1).1
      rw [pPrimeCore_map_subgroupOf 2 L Cx hLx] at h2
      simpa [commutatorElement_def] using h2
    have hinj : Function.Injective ((inclusion hL'C).comp
        (L.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom) :=
      (inclusion_injective hL'C).comp (MulEquiv.injective _)
    have := pRank_two_le_of_injective _ hinj
    omega

theorem tripleBranch_of_inputs (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hGS : GriessSolomonInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hGF : GloballyFirstRankTwoInput) (hF : FooteInput) (hHSF : HarrisSolomonFritzA7Input)
    (hCI : ClassicalInvolutionInput) : UFrontier.TripleBranch := by
  intro X _ _ _ hnonab hK hz htriple
  by_contra hU
  have hsmall := hGS X hnonab hK hz hU
  obtain ⟨x, y, L, hmax, hL, htype⟩ :=
    exists_maximal_component_of_small_types hTB hSA hB hH hGF X hnonab hK hz hU hsmall htriple
  have hx : orderOf x = 2 := hmax.1.1
  have hLx : L ≤ centralizer ({x} : Set X) := hmax.1.2.2.2.1
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X))) := hmax.1.2.2.2.2.1
  rcases hF X hnonab hK x hx L hLx hLc hL htype with
    hlie | hrank | ⟨⟨e9⟩, -⟩ | ⟨⟨e10⟩, -⟩ | ⟨⟨e11⟩, -⟩ | ⟨⟨eJ⟩, -⟩
  · exact hU (uOutcome_of_oddLieType hlie)
  · obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(coreActionKernel L)) := inferInstance
    rcases sylow_cyclic_or_quaternion_of_pRank_eq_one hrank P with hcyc | ⟨r, hr, ⟨eP⟩⟩
    · have hall : ∀ Q : Sylow 2 ↥(coreActionKernel L),
          IsCyclic (Q : Subgroup ↥(coreActionKernel L)) :=
        fun Q => (MulEquiv.isCyclic (Sylow.equiv P Q)).mp hcyc
      rcases htype with ⟨⟨e7⟩⟩ | hpsl
      · rcases hHSF X hnonab x hx L hLx hLc ⟨e7⟩ hall with hlie | ⟨⟨e6⟩, -⟩
        · exact hU (uOutcome_of_oddLieType hlie)
        · have h67 := Nat.card_congr (e6.symm.trans e7).toEquiv
          rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at h67
          norm_num [Nat.factorial] at h67
      · exact hH X hnonab hK hz hU ⟨x, L, hx, hLx, hLc, hL, hpsl, hall⟩
    · exact false_of_quaternion_kernel hCI hnonab hz hU hx hLx hLc
        (two_le_pRank_of_gsUnbalancingTriple hTB hSA hnonab hK hz hU hmax.1) hrank P hr eP
  · have h9 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e9 hz
    norm_num at h9
  · have h10 := mod_four_eq_three_of_mulEquiv_alternating hnonab (by norm_num) e10 hz
    norm_num at h10
  · exact hU (uOutcome_of_mulEquiv_alternating_eleven e11)
  · exact false_of_mulEquiv_j2 eJ hz

end CFSG.ComponentClassification.GSLit
