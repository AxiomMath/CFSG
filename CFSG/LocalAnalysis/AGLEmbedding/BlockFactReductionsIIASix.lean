module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Perm

open Equiv Equiv.Perm

theorem perm_fin_six_pow_three_eq_one {g : Perm (Fin 6)} {k : ℕ} (hg : g ^ 3 ^ k = 1) :
    g ^ 3 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  intro n hn
  have h1 : n ∣ 3 ^ k := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hg)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have h2 := two_le_of_mem_cycleType hn
  have h6 : 3 ^ j ≤ 6 := (le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans (by simp))
  rcases j with _ | _ | j
  · norm_num at h2
  · norm_num
  · have : 9 ≤ 3 ^ (j + 2) := by
      rw [pow_add]
      exact le_mul_of_one_le_left (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
    omega

theorem eq_three_of_mem_cycleType_of_pow_three {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} (hg : g ^ 3 = 1) {n : ℕ} (hn : n ∈ g.cycleType) : n = 3 := by
  have h1 : n ∣ 3 := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hg)
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
  · have := two_le_of_mem_cycleType hn
    omega
  · exact h

theorem not_centralizer_le_alternatingGroup_six {g : Perm (Fin 6)} (hg : g ^ 3 = 1) :
    ¬ Subgroup.centralizer {g} ≤ alternatingGroup (Fin 6) := by
  rw [centralizer_le_alternating_iff]
  rintro ⟨-, hsum, hcount⟩
  have hrep : g.cycleType = Multiset.replicate (Multiset.card g.cycleType) 3 :=
    Multiset.eq_replicate_card.mpr fun b hb => eq_three_of_mem_cycleType_of_pow_three hg hb
  have h1 := hcount 3
  rw [hrep, Multiset.count_replicate_self] at h1
  rw [hrep, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  omega

theorem exists_conj_eq_inv_alternatingGroup_six (g : alternatingGroup (Fin 6))
    (hg : g ^ 3 = 1) : ∃ h : alternatingGroup (Fin 6), h * g * h⁻¹ = g⁻¹ := by
  have hσ : (g : Perm (Fin 6)) ^ 3 = 1 := by simpa using congrArg Subtype.val hg
  obtain ⟨τ, hτ⟩ := isConj_iff.mp
    (isConj_iff_cycleType_eq.mpr (cycleType_inv (g : Perm (Fin 6))).symm)
  obtain ⟨c, hc, hcA⟩ :=
    IsConcreteLE.not_le_iff_exists.mp (not_centralizer_le_alternatingGroup_six hσ)
  have hcg : c * g = g * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  by_cases hτA : τ ∈ alternatingGroup (Fin 6)
  · exact ⟨⟨τ, hτA⟩, Subtype.ext (by simpa using hτ)⟩
  · have hτc : τ * c ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup] at hτA hcA ⊢
      rw [Perm.sign_mul, (Int.units_eq_one_or (sign τ)).resolve_left hτA,
        (Int.units_eq_one_or (sign c)).resolve_left hcA]
      rfl
    refine ⟨⟨τ * c, hτc⟩, Subtype.ext ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
    rw [← hτ]
    calc τ * c * ↑g * (c⁻¹ * τ⁻¹) = τ * (c * ↑g) * c⁻¹ * τ⁻¹ := by group
      _ = τ * ↑g * τ⁻¹ := by rw [hcg]; group

end Perm

open Equiv.Perm in
theorem kFactThreeASixExpThree_holds :
    ∀ (A : Type) [Group A], Nat.card (Subgroup.center A) = 3 →
      Nonempty (A ⧸ Subgroup.center A ≃* alternatingGroup (Fin 6)) →
      ∀ l : A, (∃ k : ℕ, l ^ 3 ^ k = 1) → l ^ 3 = 1 := by
  intro A _ hZ ⟨φ⟩ l ⟨k, hk⟩
  set Z := Subgroup.center A
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have : (⟨z, hz⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    rw [hZ] at this
    simpa using congrArg Subtype.val this
  set g := φ (QuotientGroup.mk' Z l)
  have hg : (g : Equiv.Perm (Fin 6)) ^ 3 ^ k = 1 := by
    have : g ^ 3 ^ k = 1 := by rw [← map_pow, ← map_pow, hk, map_one, map_one]
    simpa using congrArg Subtype.val this
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using perm_fin_six_pow_three_eq_one hg)
  have hl3Z : l ^ 3 ∈ Z := by
    have : QuotientGroup.mk' Z (l ^ 3) = 1 :=
      φ.injective (by rw [map_pow, map_pow, hg3, map_one])
    exact (QuotientGroup.eq_one_iff _).mp this
  obtain ⟨h, hh⟩ := exists_conj_eq_inv_alternatingGroup_six g hg3
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z (φ.symm h)
  set z := s * l * s⁻¹ * l with hzdef
  have hzZ : z ∈ Z := by
    have : QuotientGroup.mk' Z z = 1 := by
      apply φ.injective
      rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_mul, map_mul, map_mul, map_inv, hs,
        MulEquiv.apply_symm_apply, hh, map_one, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hsl : s * l * s⁻¹ = z * l⁻¹ := by
    rw [hzdef]
    group
  have h1 : (s * l * s⁻¹) ^ 3 = l ^ 3 := by
    rw [conj_pow, Subgroup.mem_center_iff.mp hl3Z s]
    group
  have hzc : Commute z l⁻¹ := (Subgroup.mem_center_iff.mp hzZ l⁻¹).symm
  rw [hsl, hzc.mul_pow 3, hZ3 z hzZ, one_mul, inv_pow] at h1
  have h6 : (l ^ 3) ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel _
  have h3k : (l ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]
  exact (pow_eq_one_iff_of_coprime (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3))).mp
    ⟨h6, h3k⟩

theorem kFactBlockThreeASix_of_exp : KFactBlockThreeASix := by
  have hA := kFactThreeASixExpThree_holds
  intro G _ _ M L hL hZ ⟨φ⟩
  have hq := hL.component.2.2
  have hperf : Group.IsPerfect (barM M L) := Group.isPerfect_def.mpr hq.1
  refine ⟨fun y hy ⟨k, hk⟩ => ?_, fun l hl ⟨k, hk⟩ => ?_, fun T hT hT3 => ?_⟩
  · refine mem_sup_centralizer_of_not_dvd_card_outer Nat.prime_three ?_ hy hk
    intro hdvd
    have h4 := card_outer_alternatingGroup_dvd_four 6 (by norm_num)
    rw [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence φ).toEquiv] at h4
    have := (hdvd.trans (card_outer_dvd_card_outer_centerQuotient (barM M L))).trans h4
    omega
  · have := hA (barM M L) hZ ⟨φ⟩ ⟨l, hl⟩ ⟨k, Subtype.ext (by simpa using hk)⟩
    simpa using congrArg Subtype.val this
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcard : Nat.card (barM M L) = 27 * 40 := by
      rw [(Subgroup.center (barM M L)).card_eq_card_quotient_mul_card_subgroup, hZ,
        Nat.card_congr φ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hT'card : Nat.card (T.subgroupOf (barM M L)) = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT).toEquiv
    have hT'3 : IsPGroup 3 (T.subgroupOf (barM M L)) := hT3.comap_subtype
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hT3
    have hdvd : 3 ^ j ∣ 27 * 40 := by
      rw [← hj, ← hT'card, ← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    have hj3 : j ≤ 3 := by
      by_contra hj3
      have : 3 ^ 4 ∣ 27 * 40 := (pow_dvd_pow 3 (by omega)).trans hdvd
      norm_num at this
    refine ⟨hj ▸ Nat.pow_le_pow_right (by norm_num) hj3, fun hab => ?_⟩
    rw [hj]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hj2
    have hidx : (T.subgroupOf (barM M L)).index = 40 := by
      have := (T.subgroupOf (barM M L)).card_mul_index
      rw [hT'card, hj, show j = 3 by omega, hcard] at this
      omega
    have hS : ¬ 3 ∣ (T.subgroupOf (barM M L)).index := by
      rw [hidx]
      norm_num
    obtain ⟨z, hz1⟩ : ∃ z : Subgroup.center (barM M L), z ≠ 1 := by
      have : Nontrivial (Subgroup.center (barM M L)) := by
        rw [← Finite.one_lt_card_iff_nontrivial, hZ]
        norm_num
      exact exists_ne 1
    have hz3 : (z : barM M L) ^ 3 = 1 := by
      have := pow_card_eq_one' (x := z)
      rw [hZ] at this
      exact congrArg Subtype.val this
    refine CFSG.LocalAnalysis.RankThreeTheoremC.not_isMulCommutative_sylow_of_isPerfect hperf
      (hT'3.toSylow hS) z.2 (fun h => hz1 (Subtype.ext h)) hz3 ?_
    rw [IsPGroup.toSylow_coe]
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    simpa using congrArg Subtype.val (hab.is_comm.comm ⟨a.1.1, a.2⟩ ⟨b.1.1, b.2⟩)

theorem kFactBlockThreeASix_holds : KFactBlockThreeASix :=
  kFactBlockThreeASix_of_exp

end CFSG.AGLEmbedding
