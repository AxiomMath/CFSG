module

public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
import CFSG.LocalAnalysis.OddStandard.RouteWAlt
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup
open scoped Pointwise commutatorElement

@[expose] def SignalizerTrivialPair {X : Type*} [Group X] (t : X) (J : Subgroup X) (n : ℕ) :
    Prop :=
  IsAltTwoComponent t J n ∧
    ∃ (e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)) (E : Subgroup X), E ≤ J ∧
      Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
      (∃ D : Finset (Fin n), D.card = 4 ∧ ∀ x : J, (x : X) ∈ E → ∀ ω ∉ D,
        ((e (x : J ⧸ pPrimeCore 2 J) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ω =
          ω) ∧
      ∀ y : X, orderOf y = 2 → y ∈ centralizer (E : Set X) →
        y ∈ UnbalancedLayer.coreActionKernel J → y ∉ J →
        ∀ b ∈ E ⊔ zpowers y, b ≠ 1 → thetaFunctor E b = ⊥

@[expose] def StandardReductionOddPairInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog X →
    (∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome X →
    ∀ (t : X) (K : Subgroup X) (n : ℕ), IsAltTwoComponent t K n → Odd n → 9 ≤ n →
      (∀ (t' : X) (K' : Subgroup X) (n' : ℕ), IsAltTwoComponent t' K' n' → Odd n' → n' ≤ n) →
      ∃ (t' : X) (J : Subgroup X), SignalizerTrivialPair t' J n ∧ IsStandardSubgroup J ∧
        Nonempty (J ≃* alternatingGroup (Fin n))

theorem standardReductionOddPair_of_inputs (hmax : MaximalAltComponentInput)
    (hsig : SignalizerTrivialityInput) (hS : SchurAlternatingMultiplierInput) :
    StandardReductionOddPairInput := by
  intro X _ _ _ hnonab hK hz hU t₀ K₀ m hK₀ hmo hm9 hmaxm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, J, n, hJ, hno, hn9, hnmax, e, E, hEJ, ⟨eE⟩, hD, hθ⟩ :=
    hsig X hnonab hK hz hU t₀ K₀ m hK₀ hmo hm9
  have hnm : n = m := le_antisymm (hmaxm t J n hJ hno) (hnmax t₀ K₀ m hK₀ hmo)
  subst hnm
  obtain ⟨ht, hJC, hJP, -⟩ := id hJ
  obtain ⟨hmaxi, hmaxii⟩ := hmax X hnonab hK hz hU t J n ⟨ht, hJC, hJP, ⟨e⟩⟩ hno hn9 hnmax
  have hE4 : Nat.card E = 4 := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card]
  have hEO : ¬ E ≤ (pPrimeCore 2 J).map J.subtype := by
    refine not_le_of_card_eq_four hE4 ?_
    rw [Subgroup.card_map_of_injective J.subtype_injective]
    exact pPrimeCore_coprime_card
  have hθy : ∀ y : X, orderOf y = 2 → J ≤ centralizer ({y} : Set X) →
      E ≤ centralizer (((pPrimeCore 2 (centralizer ({y} : Set X))).map
        (centralizer ({y} : Set X)).subtype : Subgroup X) : Set X) := by
    intro y hy hJy
    have hyE : y ∈ centralizer (E : Set X) :=
      mem_centralizer_iff.2 fun x hx => mem_centralizer_singleton_iff.1 (hJy (hEJ hx))
    have hyK : y ∈ UnbalancedLayer.coreActionKernel J := by
      refine ⟨centralizer_le_normalizer _
        (mem_centralizer_iff.2 fun j hj => mem_centralizer_singleton_iff.1 (hJy hj)),
        fun j hj => ?_⟩
      have hc := mem_centralizer_singleton_iff.1 (hJy hj)
      have h1 : j⁻¹ * y⁻¹ * j * y = 1 := by
        calc j⁻¹ * y⁻¹ * j * y = j⁻¹ * y⁻¹ * (j * y) := by group
          _ = j⁻¹ * y⁻¹ * (y * j) := by rw [hc]
          _ = 1 := by group
      rw [h1]
      exact one_mem _
    have hyJ : y ∉ J := not_mem_of_le_centralizer (by omega) e hy hJy
    have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; norm_num at hy
    have h := hθ y hy hyE hyK hyJ y (mem_sup_right (mem_zpowers y)) hy1
    have h1 : ⁅(pPrimeCore 2 (centralizer ({y} : Set X))).map
        (centralizer ({y} : Set X)).subtype, E⁆ = ⊥ :=
      le_bot_iff.1 (h ▸ le_sup_left)
    exact le_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h1)
  have hJperf : Group.IsPerfect J := by
    have h := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hJP
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJC).toMonoidHom)
      (subgroupOfEquivOfLe hJC).surjective
  have hOJ : pPrimeCore 2 J = ⊥ := by
    have hOJt := UGSChain.map_pPrimeCore_le_of_isPComponent hJC hJP
    have hEOJ : E ≤ centralizer (((pPrimeCore 2 J).map J.subtype : Subgroup X) : Set X) :=
      (hθy t ht hJC).trans (centralizer_le hOJt)
    have hJN : J ≤ normalizer (((pPrimeCore 2 J).map J.subtype : Subgroup X) : Set X) :=
      le_normalizer_map_subtype (pPrimeCore 2 J)
    have hcen := le_centralizer_of_le_centralizer (by omega) hJC hJP e hJN hEJ hEO hEOJ
    have hZ : pPrimeCore 2 J ≤ center J := by
      intro o ho
      rw [mem_center_iff]
      intro g
      exact Subtype.ext ((mem_centralizer_iff.1 (hcen g.2)) o ⟨o, ho, rfl⟩).symm
    exact pPrimeCore_eq_bot_of_le_center hS (by omega) e hZ
  let eJ : J ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hOJ.symm)).trans e
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa using (show 5 ≤ n by omega))
  have : IsSimpleGroup J := eJ.isSimpleGroup
  have hq : IsQuasisimple J := LocalCores.isQuasisimple_of_mulEquiv eJ.symm
    (LocalCores.isQuasisimple_of_isSimpleGroup (alternating_nonabelian (by omega))).1
  have hJ2 : 2 ∣ Nat.card J := by
    rw [Nat.card_congr eJ.toEquiv]
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h1 : 2 * Nat.card (alternatingGroup (Fin n)) = n.factorial := by
      rw [Nat.card_eq_fintype_card, two_mul_card_alternatingGroup, Fintype.card_perm,
        Fintype.card_fin]
    have h4 : 2 * 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    rw [← h1] at h4
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h4
  have hne : ∀ y : X, orderOf y = 2 → J ≤ centralizer ({y} : Set X) →
      IsComponent (J.subgroupOf (centralizer ({y} : Set X))) := by
    intro y hy hJy
    have hJnO : J ≤ normalizer (((pPrimeCore 2 (centralizer ({y} : Set X))).map
        (centralizer ({y} : Set X)).subtype : Subgroup X) : Set X) :=
      hJy.trans (le_normalizer_map_subtype _)
    have hcent := le_centralizer_of_le_centralizer (by omega) hJC hJP e hJnO hEJ hEO
      (hθy y hy hJy)
    have hconj := fun c hc => conjugate_eq_of_centralizes_core hJ2 hOJ (hmaxii y hy hJy)
      hcent (c := c) hc
    have hnormal : (J.subgroupOf (centralizer ({y} : Set X))).Normal := by
      rw [normal_subgroupOf_iff hJy]
      intro h k hh hk
      have hk' : k⁻¹ ∈ centralizer ({y} : Set X) := inv_mem hk
      rw [← hconj k⁻¹ hk', mem_conjugate_iff_conj, inv_inv,
        show k⁻¹ * (k * h * k⁻¹) * k = h by group]
      exact hh
    exact ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJy).symm hq,
      hnormal.isSubnormal⟩
  have hcomm : ∀ g : X, ⁅J, conjugate J g⁆ ≠ ⊥ := hmaxi
  exact ⟨t, J, ⟨hJ, e, E, hEJ, ⟨eE⟩, hD, hθ⟩,
    isStandardSubgroup_of_nonembedded hq ht hJC hne hcomm, ⟨eJ⟩⟩

@[expose] def AltStdCyclicOddJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
    (∃ z : G, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set G)) ≠ ⊥) →
    ¬ OutcomeLocal.UOutcome G →
    ∀ (t : G) (J : Subgroup G) (n : ℕ), Odd n → 9 ≤ n →
      (∀ (t' : G) (K : Subgroup G) (m : ℕ), IsAltTwoComponent t' K m → Odd m → m ≤ n) →
      SignalizerTrivialPair t J n → IsStandardSubgroup J →
      Nonempty (J ≃* alternatingGroup (Fin n)) →
      ∀ S : Sylow 2 (centralizer (J : Set G)),
        IsCyclic (S : Subgroup (centralizer (J : Set G))) → False

theorem solaltlit_odd_of_inputs_cycOddJ
    (hRank2 : RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels) (hCyc : AltStdCyclicOddJ)
    (hred : StandardReductionOddPairInput) : SolomonAlternatingOddInput := by
  rintro X _ _ _ hnonab hK hz hU ⟨x, L, n, hx, hno, hn, hLC, hLP, he⟩
  obtain ⟨t, K, m, hKm, hmo, hm9, hmax⟩ :=
    exists_isAltTwoComponent_max_odd ⟨x, L, n, ⟨hx, hLC, hLP, he⟩, hno, hn⟩
  obtain ⟨t', J, hpair, hJ, ⟨e'⟩⟩ := hred X hnonab hK hz hU t K m hKm hmo hm9 hmax
  have hS : OddStandard.StandardSetting X J :=
    ⟨inferInstance, hnonab, hK, OddStandard.standardComponentIsStandard_of_cfsgStandard hJ⟩
  by_cases hrank : 2 ≤ Open.pRank 2 (centralizer (J : Set X))
  · obtain ⟨eX⟩ := OddStandard.altStd_rankTwo hRank2 hS (by omega) e' hrank
    exact hU (uOutcome_of_mulEquiv_alternating hnonab (by omega) eX hz)
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (J : Set X))) := inferInstance
  rcases StandardRecognition.standard_centralizer_rank_split hS.isStandardSubgroup S with
    h2 | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exact hrank h2
  · exact hCyc X hnonab hK hz hU t' J m hmo hm9 hmax hpair hJ ⟨e'⟩ S hcyc
  · have hlie := OddStandard.altStd_quaternionW hCIT hS (by omega) e' S hr hq
    exact hU (Or.inl
      ((ClassicalInvolution.oddLieType_congr GSLit.generalizedFittingEquivOfSimple).2 hlie))

theorem solaltlit_odd_of_sol78_inputs_cycOddJ
    (hRank2 : RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : StandardRecognition.ClassicalInvolutionTheoremModels) (hCyc : AltStdCyclicOddJ)
    (hmax : MaximalAltComponentInput) (hsig : SignalizerTrivialityInput)
    (hS : SchurAlternatingMultiplierInput) : SolomonAlternatingOddInput :=
  solaltlit_odd_of_inputs_cycOddJ hRank2 hCIT hCyc
    (standardReductionOddPair_of_inputs hmax hsig hS)

end CFSG.ComponentClassification.SolAltLit
