module

public import CFSG.ClassicalInvolution.SmallCases.Constrained
public import CFSG.ClassicalInvolution.SmallCases.Exclusion.PerfectCore
import CFSG.ClassicalInvolution.SubnormalClosure.Reduction
import CFSG.ClassicalInvolution.SmallCases.Alternating

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped commutatorElement

theorem exists_perfect_subnormal_of_witness {F : Type*} [Group F] [Finite F] {z : F}
    (hz : orderOf z = 2) {K : Subgroup F} (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) :
    ∃ P : Subgroup F, ⁅P, P⁆ = P ∧ IsSubnormal P (Subgroup.centralizer {z}) ∧ z ∈ P ∧
      classicalInvolutionWitness P := by
  have hq := isQuasisimple_oddCoreQuotient_of_witness hw hns
  obtain ⟨P, hPn, hPperf, hPsup⟩ := exists_perfect_normal_sup_oddCore_eq_top hq.1
  have hzz : (⟨z, hzK⟩ : K) * ⟨z, hzK⟩ = 1 := by
    apply Subtype.ext
    have := pow_orderOf_eq_one z
    rwa [hz, pow_two] at this
  have hzP : (⟨z, hzK⟩ : K) ∈ P :=
    mem_of_mul_self_eq_one_of_sup_oddCore_eq_top P hPsup hzz
  obtain ⟨q⟩ := nonempty_oddCoreQuotientEquiv_of_sup_eq_top P hPsup
  have hwP : classicalInvolutionWitness P := classicalInvolutionWitness_of_quotientEquiv q.symm hw
  refine ⟨P.map K.subtype, ?_, ?_, ⟨⟨z, hzK⟩, hzP, rfl⟩,
    classicalInvolutionWitness_of_mulEquiv (P.equivMapOfInjective K.subtype K.subtype_injective)
      hwP⟩
  · rw [← Subgroup.map_commutator, hPperf]
  · have h1 : P.map K.subtype ≤ K := Subgroup.map_subtype_le P
    have h3 : (P.map K.subtype).subgroupOf K = P :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
    have h2 : ((P.map K.subtype).subgroupOf K).Normal := by
      rw [h3]
      exact hPn
    exact isSubnormal_trans (isSubnormal_of_normal_subgroupOf h1 h2) hK

theorem false_of_isSolvable_centralizer {F : Type*} [Group F] [Finite F]
    (z : F) (_hz : orderOf z = 2) (K : Subgroup F) (_hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (_hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {z})) :
    False := by
  have := hsolv
  exact hns (Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (isSubnormal_le hK)))

theorem false_of_no_perfect_subnormal {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K)
    (hno : ∀ P : Subgroup F, ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {z}) → z ∉ P) :
    False := by
  obtain ⟨P, hperf, hsub, hzP, -⟩ := exists_perfect_subnormal_of_witness hz hzK hK hw hns
  exact hno P hperf hsub hzP

theorem false_of_unique_perfect_subnormal {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (Q : Subgroup F)
    (hQ : ∀ P : Subgroup F, ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {z}) → z ∈ P →
      P = Q)
    (hnw : ¬ classicalInvolutionWitness Q) : False := by
  obtain ⟨P, hperf, hsub, hzP, hwP⟩ := exists_perfect_subnormal_of_witness hz hzK hK hw hns
  exact hnw (hQ P hperf hsub hzP ▸ hwP)

theorem map_eq_one_of_perfect_of_solvable {F : Type*} [Group F] {C P : Subgroup F} (hPC : P ≤ C)
    (hperf : ⁅P, P⁆ = P) {S : Type*} [Group S] [Group.IsSolvable S] (f : C →* S) {x : F}
    (hx : x ∈ P) : f ⟨x, hPC hx⟩ = 1 := by
  let A : Subgroup C := P.subgroupOf C
  have hA : ⁅A, A⁆ = A := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPC, hperf]
  have hR : ⁅A.map f, A.map f⁆ = A.map f := by
    rw [← Subgroup.map_commutator, hA]
  by_contra hne
  have hmem : f ⟨x, hPC hx⟩ ∈ A.map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hx)
  have hbot : A.map f ≠ ⊥ := fun h => hne (by rwa [h, Subgroup.mem_bot] at hmem)
  exact (Group.IsSolvable.commutator_lt_of_ne_bot hbot).ne hR

theorem false_of_solvable_hom {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) {S : Type*} [Group S] [Group.IsSolvable S]
    (f : Subgroup.centralizer ({z} : Set F) →* S)
    (hf : ∀ h : z ∈ Subgroup.centralizer ({z} : Set F), f ⟨z, h⟩ ≠ 1) : False := by
  refine false_of_no_perfect_subnormal z hz K hzK hK hw hns ?_
  intro P hperf hsub hzP
  have hPC : P ≤ Subgroup.centralizer {z} := isSubnormal_le hsub
  exact hf (hPC hzP) (map_eq_one_of_perfect_of_solvable hPC hperf f hzP)

theorem false_of_solvable_quotient {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (N : Subgroup F)
    (hNn : (N.subgroupOf (Subgroup.centralizer {z})).Normal)
    (hsolv : Group.IsSolvable
      (↥(Subgroup.centralizer {z}) ⧸ N.subgroupOf (Subgroup.centralizer {z})))
    (hzN : z ∉ N) : False := by
  refine false_of_solvable_hom z hz K hzK hK hw hns
    (QuotientGroup.mk' (N.subgroupOf (Subgroup.centralizer {z}))) fun h hf => ?_
  exact hzN (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hf))

theorem false_of_index_two {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (N : Subgroup F)
    (hNn : (N.subgroupOf (Subgroup.centralizer {z})).Normal)
    (hidx : (N.subgroupOf (Subgroup.centralizer {z})).index = 2) (hzN : z ∉ N) : False := by
  refine false_of_solvable_quotient z hz K hzK hK hw hns N hNn ?_ hzN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥(Subgroup.centralizer {z}) ⧸ N.subgroupOf (Subgroup.centralizer {z})) :=
    isCyclic_of_prime_card hidx
  infer_instance

theorem eq_of_perfect_subnormal_of_isQuasisimple {F : Type*} [Group F] {Q P : Subgroup F}
    (hQ : CFSG.Open.IsQuasisimple Q) (hPQ : P ≤ Q) (hsub : IsSubnormal P Q) (hperf : ⁅P, P⁆ = P)
    {z : F} (hzP : z ∈ P) (hz1 : z ≠ 1) : P = Q := by
  have hsub' : IsSubnormal (P.subgroupOf Q) ⊤ := by
    have := isSubnormal_subgroupOf hsub Q
    rwa [Subgroup.subgroupOf_self] at this
  rcases CFSG.ComponentClassification.Quasisimple.subnormal_le_center_or_eq_top hQ _ hsub' with
    hcen | htop
  · exfalso
    have hbot : ⁅P, P⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro p hp q hq
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      have hpc : (⟨p, hPQ hp⟩ : Q) ∈ Subgroup.center Q :=
        hcen (Subgroup.mem_subgroupOf.mpr hp)
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hpc ⟨q, hPQ hq⟩).symm
    rw [hperf, Subgroup.eq_bot_iff_forall] at hbot
    exact hz1 (hbot z hzP)
  · exact le_antisymm hPQ (Subgroup.subgroupOf_eq_top.mp htop)

theorem false_of_isQuasisimple_normal_solvable_quotient {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (Q : Subgroup F) (hQC : Q ≤ Subgroup.centralizer {z})
    (hQn : (Q.subgroupOf (Subgroup.centralizer {z})).Normal)
    (hsolv : Group.IsSolvable
      (↥(Subgroup.centralizer {z}) ⧸ Q.subgroupOf (Subgroup.centralizer {z})))
    (hQ : CFSG.Open.IsQuasisimple Q) (hnw : ¬ classicalInvolutionWitness Q) : False := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine false_of_unique_perfect_subnormal z hz K hzK hK hw hns Q ?_ hnw
  intro P hperf hsub hzP
  have hPC : P ≤ Subgroup.centralizer {z} := isSubnormal_le hsub
  have hPQ : P ≤ Q := fun x hx =>
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp
      (map_eq_one_of_perfect_of_solvable hPC hperf
        (QuotientGroup.mk' (Q.subgroupOf (Subgroup.centralizer {z}))) hx))
  have hsubQ : IsSubnormal P Q := by
    have := isSubnormal_inf hsub Q
    rwa [inf_eq_left.mpr hPQ, inf_eq_right.mpr hQC] at this
  exact eq_of_perfect_subnormal_of_isQuasisimple hQ hPQ hsubQ hperf hzP hz1

theorem false_of_isQuasisimple_centralizer {F : Type*} [Group F] [Finite F]
    (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (hC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer {z}))
    (hnw : ¬ classicalInvolutionWitness (Subgroup.centralizer {z})) : False := by
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  refine false_of_unique_perfect_subnormal z hz K hzK hK hw hns (Subgroup.centralizer {z}) ?_ hnw
  intro P hperf hsub hzP
  exact eq_of_perfect_subnormal_of_isQuasisimple hC (isSubnormal_le hsub) hsub hperf hzP hz1

theorem natCard_specialLinearGroup_fin_two (K : Type*) [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  let := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem not_classicalInvolutionWitness_of_card {G : Type*} [Group G] [Finite G] (J : Subgroup G)
    (h5040 : Nat.card (J ⧸ classicalInvolutionOddCore J) ≠ 5040)
    (hsl : ∀ q : ℕ, Nat.card (J ⧸ classicalInvolutionOddCore J) ≠ q * (q ^ 2 - 1)) :
    ¬ classicalInvolutionWitness J := by
  rintro (⟨p, n, hp, hp2, hn, ⟨e⟩⟩ | ⟨hqs, hcard, ⟨e⟩⟩)
  · apply hsl (Nat.card (GaloisField p n))
    rw [Nat.card_congr e.toEquiv, natCard_specialLinearGroup_fin_two]
  · apply h5040
    set Q := J ⧸ classicalInvolutionOddCore J
    have h1 : Nat.card Q = Nat.card (Q ⧸ Subgroup.center Q) * Nat.card (Subgroup.center Q) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h3 : Nat.card (Q ⧸ Subgroup.center Q) = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.card_eq_fintype_card, Nat.factorial]
    rw [h1, h3, hcard]

theorem not_classicalInvolutionWitness_of_isQuasisimple_of_card {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hq : CFSG.Open.IsQuasisimple Q) (hZ : Nat.card (Subgroup.center Q) = 2)
    (h5040 : Nat.card Q ≠ 5040) (hsl : ∀ q : ℕ, Nat.card Q ≠ q * (q ^ 2 - 1)) :
    ¬ classicalInvolutionWitness Q := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore Q)) :=
    QuaternionStructure.odd_natCard_oddCore Q
  have hO : classicalInvolutionOddCore Q = ⊥ := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq
      (classicalInvolutionOddCore Q) with h | h
    · have hdvd : Nat.card (classicalInvolutionOddCore Q) ∣ 2 := by
        rw [← hZ]
        exact Subgroup.card_dvd_of_le h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact Subgroup.card_eq_one.mp h1
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have h2 : 2 ∣ Nat.card Q := by
        rw [← hZ]
        exact Subgroup.card_subgroup_dvd_card _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hcard : Nat.card (Q ⧸ classicalInvolutionOddCore Q) = Nat.card Q := by
    have h1 : Nat.card Q = Nat.card (Q ⧸ classicalInvolutionOddCore Q) *
        Nat.card (classicalInvolutionOddCore Q) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hcardO : Nat.card (classicalInvolutionOddCore Q) = 1 := by
      rw [hO]
      exact Subgroup.card_bot
    rw [hcardO, mul_one] at h1
    exact h1.symm
  exact not_classicalInvolutionWitness_of_card Q (by rwa [hcard]) fun q => by
    rw [hcard]
    exact hsl q

theorem forall_ne_sl2_card_40320 : ∀ q : ℕ, (40320 : ℕ) ≠ q * (q ^ 2 - 1) := by
  intro q h
  have hq : q ≤ 36 := by
    by_contra hlt
    push Not at hlt
    have h1 : 37 * 37 ≤ q * q := Nat.mul_le_mul hlt hlt
    have h2 : q ^ 2 - 1 ≥ 37 * 37 - 1 := by
      have : q ^ 2 = q * q := sq q
      omega
    have h3 : q * (q ^ 2 - 1) ≥ 37 * (37 * 37 - 1) := Nat.mul_le_mul hlt h2
    omega
  interval_cases q <;> omega

theorem forall_ne_sl2_card_39916800 : ∀ q : ℕ, (39916800 : ℕ) ≠ q * (q ^ 2 - 1) := by
  intro q h
  have hq : q ≤ 342 := by
    by_contra hlt
    push Not at hlt
    have h1 : 343 * 343 ≤ q * q := Nat.mul_le_mul hlt hlt
    have h2 : q ^ 2 - 1 ≥ 343 * 343 - 1 := by
      have : q ^ 2 = q * q := sq q
      omega
    have h3 : q * (q ^ 2 - 1) ≥ 343 * (343 * 343 - 1) := Nat.mul_le_mul hlt h2
    omega
  interval_cases q <;> omega

theorem not_classicalInvolutionWitness_of_card_eq_40320 {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hq : CFSG.Open.IsQuasisimple Q) (hZ : Nat.card (Subgroup.center Q) = 2)
    (hcard : Nat.card Q = 40320) : ¬ classicalInvolutionWitness Q :=
  not_classicalInvolutionWitness_of_isQuasisimple_of_card Q hq hZ (by rw [hcard]; decide)
    fun q => by rw [hcard]; exact forall_ne_sl2_card_40320 q

theorem not_classicalInvolutionWitness_of_card_eq_39916800 {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hq : CFSG.Open.IsQuasisimple Q) (hZ : Nat.card (Subgroup.center Q) = 2)
    (hcard : Nat.card Q = 39916800) : ¬ classicalInvolutionWitness Q :=
  not_classicalInvolutionWitness_of_isQuasisimple_of_card Q hq hZ (by rw [hcard]; decide)
    fun q => by rw [hcard]; exact forall_ne_sl2_card_39916800 q

theorem map_centralizer_singleton_mulEquiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (z : F) :
    (Subgroup.centralizer ({z} : Set F)).map e.toMonoidHom =
      Subgroup.centralizer ({e z} : Set F') := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩ h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := Subgroup.mem_centralizer_iff.mp hy z (Set.mem_singleton z)
    simpa using congrArg e this
  · intro hx
    refine ⟨e.symm x, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := hx (e h) (Set.mem_singleton _)
    apply e.injective
    simpa using this

theorem classicalConfig_map {F F' : Type*} [Group F] [Group F'] (e : F ≃* F') {z : F}
    (hz : orderOf z = 2) {K : Subgroup F} (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) :
    orderOf (e z) = 2 ∧ e z ∈ K.map e.toMonoidHom ∧
      IsSubnormal (K.map e.toMonoidHom) (Subgroup.centralizer {e z}) ∧
      classicalInvolutionWitness (K.map e.toMonoidHom) ∧
      ¬ Group.IsSolvable (K.map e.toMonoidHom) := by
  refine ⟨by rwa [MulEquiv.orderOf_eq], ⟨z, hzK, rfl⟩, ?_,
    classicalInvolutionWitness_of_mulEquiv (e.subgroupMap K) hw, ?_⟩
  · rw [← map_centralizer_singleton_mulEquiv e z]
    exact isSubnormal_map_mulEquiv e hK
  · intro hs
    have : Group.IsSolvable (K.map (e : F →* F')) := hs
    exact hns (Group.isSolvable_of_surjective (f := (e.subgroupMap K).symm.toMonoidHom)
      (e.subgroupMap K).symm.surjective)

theorem false_of_isSolvable_centralizer_of_mulEquiv {F F' : Type*} [Group F] [Group F']
    [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {e z})) :
    False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_isSolvable_centralizer (e z) h1 _ h2 h3 h4 h5 hsolv

theorem false_of_normal_pGroup_centralizer_solvable_of_mulEquiv {F F' : Type*} [Group F]
    [Group F'] [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F)
    (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer {z}))
    (hw : classicalInvolutionWitness K) (hns : ¬ Group.IsSolvable K) (U : Subgroup F')
    (hU : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer {e z})
    (hUn : Subgroup.centralizer {e z} ≤ Subgroup.normalizer (U : Set F'))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {e z} ⊓ Subgroup.centralizer (U : Set F'))) :
    False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_normal_pGroup_centralizer_solvable (e z) h1 _ h2 h3 h4 h5 U hU hUC hUn hsolv

theorem false_of_normal_pGroup_self_centralizing_of_mulEquiv {F F' : Type*} [Group F]
    [Group F'] [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F)
    (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer {z}))
    (hw : classicalInvolutionWitness K) (hns : ¬ Group.IsSolvable K) (U : Subgroup F')
    (hU : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer {e z})
    (hUn : Subgroup.centralizer {e z} ≤ Subgroup.normalizer (U : Set F'))
    (hcon : Subgroup.centralizer {e z} ⊓ Subgroup.centralizer (U : Set F') ≤ U) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_normal_pGroup_self_centralizing (e z) h1 _ h2 h3 h4 h5 U hU hUC hUn hcon

theorem false_of_twoConstrained_of_mulEquiv {F F' : Type*} [Group F] [Group F'] [Finite F']
    (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K)
    (hcon : Subgroup.centralizer {e z} ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer {e z}) : Set F') ≤
          pCoreOf 2 (Subgroup.centralizer {e z})) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_twoConstrained (e z) h1 _ h2 h3 h4 h5 hcon

theorem false_of_no_perfect_subnormal_of_mulEquiv {F F' : Type*} [Group F] [Group F']
    [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K)
    (hno : ∀ P : Subgroup F', ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {e z}) →
      e z ∉ P) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_no_perfect_subnormal (e z) h1 _ h2 h3 h4 h5 hno

theorem false_of_solvable_hom_of_mulEquiv {F F' : Type*} [Group F] [Group F'] [Finite F']
    (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) {S : Type*} [Group S] [Group.IsSolvable S]
    (f : Subgroup.centralizer ({e z} : Set F') →* S)
    (hf : ∀ h : e z ∈ Subgroup.centralizer ({e z} : Set F'), f ⟨e z, h⟩ ≠ 1) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_solvable_hom (e z) h1 _ h2 h3 h4 h5 f hf

theorem false_of_solvable_quotient_of_mulEquiv {F F' : Type*} [Group F] [Group F'] [Finite F']
    (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (N : Subgroup F')
    (hNn : (N.subgroupOf (Subgroup.centralizer {e z})).Normal)
    (hsolv : Group.IsSolvable
      (↥(Subgroup.centralizer {e z}) ⧸ N.subgroupOf (Subgroup.centralizer {e z})))
    (hzN : e z ∉ N) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_solvable_quotient (e z) h1 _ h2 h3 h4 h5 N hNn hsolv hzN

theorem false_of_index_two_of_mulEquiv {F F' : Type*} [Group F] [Group F'] [Finite F']
    (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (N : Subgroup F')
    (hNn : (N.subgroupOf (Subgroup.centralizer {e z})).Normal)
    (hidx : (N.subgroupOf (Subgroup.centralizer {e z})).index = 2) (hzN : e z ∉ N) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_index_two (e z) h1 _ h2 h3 h4 h5 N hNn hidx hzN

theorem false_of_unique_perfect_subnormal_of_mulEquiv {F F' : Type*} [Group F] [Group F']
    [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (Q : Subgroup F')
    (hQ : ∀ P : Subgroup F', ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {e z}) →
      e z ∈ P → P = Q)
    (hnw : ¬ classicalInvolutionWitness Q) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_unique_perfect_subnormal (e z) h1 _ h2 h3 h4 h5 Q hQ hnw

theorem false_of_isQuasisimple_normal_solvable_quotient_of_mulEquiv {F F' : Type*} [Group F]
    [Group F'] [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F)
    (hzK : z ∈ K) (hK : IsSubnormal K (Subgroup.centralizer {z}))
    (hw : classicalInvolutionWitness K) (hns : ¬ Group.IsSolvable K) (Q : Subgroup F')
    (hQC : Q ≤ Subgroup.centralizer {e z})
    (hQn : (Q.subgroupOf (Subgroup.centralizer {e z})).Normal)
    (hsolv : Group.IsSolvable
      (↥(Subgroup.centralizer {e z}) ⧸ Q.subgroupOf (Subgroup.centralizer {e z})))
    (hQ : CFSG.Open.IsQuasisimple Q) (hnw : ¬ classicalInvolutionWitness Q) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_isQuasisimple_normal_solvable_quotient (e z) h1 _ h2 h3 h4 h5 Q hQC hQn hsolv hQ
    hnw

theorem false_of_isQuasisimple_centralizer_of_mulEquiv {F F' : Type*} [Group F] [Group F']
    [Finite F'] (e : F ≃* F') (z : F) (hz : orderOf z = 2) (K : Subgroup F) (hzK : z ∈ K)
    (hK : IsSubnormal K (Subgroup.centralizer {z})) (hw : classicalInvolutionWitness K)
    (hns : ¬ Group.IsSolvable K) (hC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer {e z}))
    (hnw : ¬ classicalInvolutionWitness (Subgroup.centralizer {e z})) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact false_of_isQuasisimple_centralizer (e z) h1 _ h2 h3 h4 h5 hC hnw

@[expose] def NoNonsolvableClassicalAt {F : Type*} [Group F] (z : F) : Prop :=
  orderOf z = 2 → ∀ K : Subgroup F, z ∈ K → IsSubnormal K (Subgroup.centralizer {z}) →
    classicalInvolutionWitness K → ¬ Group.IsSolvable K → False

@[expose] def NoNonsolvableClassical (F : Type*) [Group F] : Prop :=
  ∀ z : F, NoNonsolvableClassicalAt z

theorem NoNonsolvableClassicalAt.of_map {F F' : Type*} [Group F] [Group F'] (e : F ≃* F') {z : F}
    (h : NoNonsolvableClassicalAt (e z)) : NoNonsolvableClassicalAt z := by
  intro hz K hzK hK hw hns
  obtain ⟨h1, h2, h3, h4, h5⟩ := classicalConfig_map e hz hzK hK hw hns
  exact h h1 _ h2 h3 h4 h5

theorem NoNonsolvableClassicalAt.conj {F : Type*} [Group F] {z : F}
    (h : NoNonsolvableClassicalAt z) (g : F) : NoNonsolvableClassicalAt (g * z * g⁻¹) := by
  refine NoNonsolvableClassicalAt.of_map (MulAut.conj g).symm ?_
  have : (MulAut.conj g).symm (g * z * g⁻¹) = z := by simp [MulAut.conj_symm_apply]; group
  rwa [this]

theorem NoNonsolvableClassical.of_mulEquiv {F F' : Type*} [Group F] [Group F'] (e : F ≃* F')
    (h : NoNonsolvableClassical F') : NoNonsolvableClassical F :=
  fun z => NoNonsolvableClassicalAt.of_map e (h (e z))

theorem NoNonsolvableClassical.of_conj_reps {F : Type*} [Group F] (S : Set F)
    (hS : ∀ z : F, orderOf z = 2 → ∃ s ∈ S, IsConj s z)
    (h : ∀ s ∈ S, NoNonsolvableClassicalAt s) : NoNonsolvableClassical F := by
  intro z hz
  obtain ⟨s, hs, hsz⟩ := hS z hz
  obtain ⟨c, hc⟩ := isConj_iff.mp hsz
  have := (h s hs).conj c
  rw [hc] at this
  exact this hz

theorem noNonsolvableClassical_alternating (n : ℕ) :
    NoNonsolvableClassical (alternatingGroup (Fin n)) :=
  fun z hz K hzK hK hw hns => alternating_no_classical n z hz K hzK hK hw hns

theorem NoNonsolvableClassicalAt.of_isSolvable_centralizer {F : Type*} [Group F] [Finite F]
    {z : F} (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {z})) : NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_isSolvable_centralizer z hz K hzK hK hw hns hsolv

theorem NoNonsolvableClassicalAt.of_twoConstrained {F : Type*} [Group F] [Finite F] {z : F}
    (hcon : Subgroup.centralizer {z} ⊓
        Subgroup.centralizer (pCoreOf 2 (Subgroup.centralizer {z}) : Set F) ≤
          pCoreOf 2 (Subgroup.centralizer {z})) : NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_twoConstrained z hz K hzK hK hw hns hcon

theorem NoNonsolvableClassicalAt.of_normal_pGroup_centralizer_solvable {F : Type*} [Group F]
    [Finite F] {z : F} (U : Subgroup F) (hU : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer {z})
    (hUn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (U : Set F))
    (hsolv : Group.IsSolvable ↥(Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F))) :
    NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns =>
    false_of_normal_pGroup_centralizer_solvable z hz K hzK hK hw hns U hU hUC hUn hsolv

theorem NoNonsolvableClassicalAt.of_normal_pGroup_self_centralizing {F : Type*} [Group F]
    [Finite F] {z : F} (U : Subgroup F) (hU : IsPGroup 2 U) (hUC : U ≤ Subgroup.centralizer {z})
    (hUn : Subgroup.centralizer {z} ≤ Subgroup.normalizer (U : Set F))
    (hcon : Subgroup.centralizer {z} ⊓ Subgroup.centralizer (U : Set F) ≤ U) :
    NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns =>
    false_of_normal_pGroup_self_centralizing z hz K hzK hK hw hns U hU hUC hUn hcon

theorem NoNonsolvableClassicalAt.of_no_perfect_subnormal {F : Type*} [Group F] [Finite F] {z : F}
    (hno : ∀ P : Subgroup F, ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {z}) → z ∉ P) :
    NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_no_perfect_subnormal z hz K hzK hK hw hns hno

theorem NoNonsolvableClassicalAt.of_solvable_hom {F : Type*} [Group F] [Finite F] {z : F}
    {S : Type*} [Group S] [Group.IsSolvable S] (f : Subgroup.centralizer ({z} : Set F) →* S)
    (hf : ∀ h : z ∈ Subgroup.centralizer ({z} : Set F), f ⟨z, h⟩ ≠ 1) :
    NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_solvable_hom z hz K hzK hK hw hns f hf

theorem NoNonsolvableClassicalAt.of_index_two {F : Type*} [Group F] [Finite F] {z : F}
    (N : Subgroup F) (hNn : (N.subgroupOf (Subgroup.centralizer {z})).Normal)
    (hidx : (N.subgroupOf (Subgroup.centralizer {z})).index = 2) (hzN : z ∉ N) :
    NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_index_two z hz K hzK hK hw hns N hNn hidx hzN

theorem NoNonsolvableClassicalAt.of_unique_perfect_subnormal {F : Type*} [Group F] [Finite F]
    {z : F} (Q : Subgroup F)
    (hQ : ∀ P : Subgroup F, ⁅P, P⁆ = P → IsSubnormal P (Subgroup.centralizer {z}) → z ∈ P →
      P = Q)
    (hnw : ¬ classicalInvolutionWitness Q) : NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_unique_perfect_subnormal z hz K hzK hK hw hns Q hQ hnw

theorem NoNonsolvableClassicalAt.of_isQuasisimple_centralizer {F : Type*} [Group F] [Finite F]
    {z : F} (hC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer {z}))
    (hnw : ¬ classicalInvolutionWitness (Subgroup.centralizer {z})) : NoNonsolvableClassicalAt z :=
  fun hz K hzK hK hw hns => false_of_isQuasisimple_centralizer z hz K hzK hK hw hns hC hnw

end CFSG.ClassicalInvolution
