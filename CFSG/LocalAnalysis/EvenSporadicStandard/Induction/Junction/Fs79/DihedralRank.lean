module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.DihedralCentral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.CyclicIndex

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup DihedralGroup

variable {S : Type} [Group S] [Finite S]

theorem not_mem_commutator {n : ℕ} [NeZero n] {φ : S →* DihedralGroup n} {r s z : S}
    (hr : φ r = DihedralGroup.r 1) (hs : φ s = sr 0) (hn : 4 ∣ n) (hrn : r ^ n = 1)
    (hker : φ.ker ≤ center S) (hker2 : ∀ x ∈ φ.ker, x ^ 2 = 1) (hz : z ∈ φ.ker)
    (hz1 : z ≠ 1) : z ∉ commutator S :=
  not_mem_commutator_aux hr hs hn hrn hker hker2 (conj_mul_mem_ker hr hs) (by group) hz hz1

theorem card_le_four_of_card_dihedral_two {φ : S →* DihedralGroup (2 ^ 1)}
    (hφ : Function.Surjective φ) (hcard : Nat.card φ.ker ≤ 2) (hcomm : φ.ker ≤ commutator S)
    {E : Subgroup S} (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  have hS : Nat.card φ.ker * 4 = Nat.card S := by
    have := Subgroup.card_ker_mul_card_of_surjective hφ
    rwa [DihedralGroup.nat_card] at this
  by_contra hE4
  replace hE4 : 4 < Nat.card E := not_le.1 hE4
  have hdvd : Nat.card E ∣ Nat.card S := Subgroup.card_subgroup_dvd_card E
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hEle := Subgroup.card_le_card_group E
  rcases Nat.lt_or_ge (Nat.card φ.ker) 2 with h1 | h2
  · omega
  · have hk2 : Nat.card φ.ker = 2 := by omega
    have hS8 : Nat.card S = 8 := by omega
    obtain ⟨e, he⟩ : ∃ e, Nat.card E = e := ⟨_, rfl⟩
    rw [he, hS8] at hdvd
    rw [he] at hE4 hEle
    have he8 : e = 8 := by
      have : e ≤ 8 := hS8 ▸ he ▸ hEle
      interval_cases e <;> omega
    have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [he, he8, hS8])
    have := hE.1
    have hab : ∀ a b : S, a * b = b * a := fun a b => by
      have ha : a ∈ E := hEtop ▸ Subgroup.mem_top a
      have hb : b ∈ E := hEtop ▸ Subgroup.mem_top b
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) ⟨b, hb⟩)
    have hbot : commutator S ≤ ⊥ := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hab a b
    have := Subgroup.card_eq_one.2 (le_bot_iff.1 (hcomm.trans hbot))
    omega

theorem card_le_four_of_dihedral_central {m : ℕ} (hm : 1 ≤ m) {φ : S →* DihedralGroup (2 ^ m)}
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ center S) (hker2 : ∀ x ∈ φ.ker, x ^ 2 = 1)
    (hcard : Nat.card φ.ker ≤ 2) (hcomm : φ.ker ≤ commutator S) {E : Subgroup S}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  by_cases hm1 : m = 1
  · subst hm1
    exact card_le_four_of_card_dihedral_two hφ hcard hcomm hE
  have hm2 : 2 ≤ m := by omega
  have : NeZero (2 ^ m) := ⟨by positivity⟩
  obtain ⟨r, hr⟩ := hφ (DihedralGroup.r 1)
  obtain ⟨s, hs⟩ := hφ (DihedralGroup.sr 0)
  by_cases hk : φ.ker ≤ zpowers r
  · have hCle : ∀ c ∈ (rotations (2 ^ m)).comap φ, c ∈ zpowers r := by
      intro c hc
      obtain ⟨k, hk'⟩ := exists_pow_mul_mem_ker hr hc
      have := mul_mem (pow_mem (mem_zpowers r) k) (hk hk')
      simpa using this
    have hidx : (zpowers r).index ≤ 2 := by
      refine index_le_two_of_forall s fun x => ?_
      rcases mem_comap_rotations_or hs x with hx | hx
      · exact Or.inl (hCle _ hx)
      · exact Or.inr (hCle _ hx)
    exact card_le_four_of_cyclic_index_le_two hidx hE
  · exfalso
    obtain ⟨z, hzK, hzr⟩ := IsConcreteLE.not_le_iff_exists.1 hk
    have hz1 : z ≠ 1 := fun h => hzr (h ▸ one_mem _)
    have hz2 : z ^ 2 = 1 := hker2 z hzK
    have hord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hKz : zpowers z = φ.ker := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzK) ?_
      rw [Nat.card_zpowers, hord]
      exact hcard
    have hrn : r ^ 2 ^ m = 1 := by
      have hmem : r ^ 2 ^ m ∈ zpowers z := hKz ▸ pow_mem_ker hr
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hmem
      rw [← zpow_mod_orderOf z j, hord] at hj
      push_cast at hj
      rcases Int.emod_two_eq_zero_or_one j with h | h
      · rw [h, zpow_zero] at hj
        exact hj.symm
      · rw [h, zpow_one] at hj
        exact absurd (hj ▸ pow_mem (mem_zpowers r) _) hzr
    exact not_mem_commutator hr hs (pow_dvd_pow 2 hm2) hrn hker hker2 hzK hz1 (hcomm hzK)

end CFSG.EvenSporadicStandard.Induction.Junction
