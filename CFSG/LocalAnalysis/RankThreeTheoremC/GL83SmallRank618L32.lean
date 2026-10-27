module

import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.Family (GL32)
open scoped MatrixGroups

theorem card_psl_three_two : Nat.card PSL(3, ZMod 2) = 168 := by
  rw [Nat.card_congr L32Insp.pslEquiv.toEquiv]
  exact L32Insp.card_GL

theorem isSimpleGroup_psl_three_two : IsSimpleGroup PSL(3, ZMod 2) :=
  (CFSG.LinearGroups.linear_projective_simple (K := ZMod 2) (n := 3) (by norm_num)
    (Or.inl le_rfl)).2.1

private theorem l32_prime_dvd_168 {p : ℕ} (hp : p.Prime) (h : p ∣ 168) :
    p = 2 ∨ p = 3 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 3 * 3 * 7 := h
  rcases (Nat.Prime.dvd_mul hp).1 h' with h2 | h7
  · rcases (Nat.Prime.dvd_mul hp).1 h2 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h7))

private theorem l32_dvd_of_two_lt_card_primeFactors {n : ℕ} (hn : n ∣ 168)
    (h3 : 2 < n.primeFactors.card) : 42 ∣ n := by
  have hsub : n.primeFactors ⊆ {2, 3, 7} := by
    intro p hp
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.1 hp
    rcases l32_prime_dvd_168 hpp (hpn.trans hn) with rfl | rfl | rfl <;> simp
  have hcard : ({2, 3, 7} : Finset ℕ).card = 3 := by decide
  have heq : n.primeFactors = {2, 3, 7} :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have h2 : 2 ∣ n := (Nat.mem_primeFactors.1 (by rw [heq]; simp : 2 ∈ n.primeFactors)).2.1
  have h3' : 3 ∣ n := (Nat.mem_primeFactors.1 (by rw [heq]; simp : 3 ∈ n.primeFactors)).2.1
  have h7 : 7 ∣ n := (Nat.mem_primeFactors.1 (by rw [heq]; simp : 7 ∈ n.primeFactors)).2.1
  omega

private theorem l32_false_of_card_forty_two_or_eighty_four {R : Type*} [Group R] [Finite R]
    [IsSimpleGroup R] (h : Nat.card R = 42 ∨ Nat.card R = 84) : False := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 7 R) := inferInstance
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hmul : Nat.card P * (P : Subgroup R).index = Nat.card R := Subgroup.card_mul_index _
  have hidx : ¬ 7 ∣ (P : Subgroup R).index := P.not_dvd_index
  have hk3 : k < 3 := by
    by_contra hk3
    have h1 : 7 ^ 3 ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.1 hk3)
    have h2 : Nat.card P ≤ Nat.card R := Subgroup.card_le_card_group _
    rw [hk] at h2
    omega
  have hcases : Nat.card P = 7 ∧ ((P : Subgroup R).index = 6 ∨ (P : Subgroup R).index = 12) := by
    rw [hk] at hmul ⊢
    interval_cases k <;> omega
  obtain ⟨hP7, hi⟩ := hcases
  have hs : Nat.card (Sylow 7 R) = 1 := by
    have hmod := card_sylow_modEq_one 7 R
    have hdvd := P.card_dvd_index
    have hle : Nat.card (Sylow 7 R) ≤ (P : Subgroup R).index := Nat.le_of_dvd (by omega) hdvd
    have hle12 : Nat.card (Sylow 7 R) ≤ 12 := by omega
    unfold Nat.ModEq at hmod
    have hpos : 0 < Nat.card (Sylow 7 R) := Nat.card_pos
    generalize Nat.card (Sylow 7 R) = s at *
    interval_cases s <;> omega
  have : Subsingleton (Sylow 7 R) := Finite.card_le_one_iff_subsingleton.mp hs.le
  have : (P : Subgroup R).Normal := Sylow.normal_of_subsingleton P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup R) with hb | ht
  · rw [hb, Subgroup.card_bot] at hP7
    omega
  · rw [ht, Subgroup.index_top] at hi
    omega

private theorem l32_card_eq_of_simple_of_dvd {R : Type*} [Group R] [Finite R] [IsSimpleGroup R]
    (hR : ∃ a b : R, a * b ≠ b * a) (hd : Nat.card R ∣ 168) : Nat.card R = 168 := by
  have hns : ¬ Group.IsSolvable R := fun hsolv => by
    obtain ⟨a, b, hab⟩ := hR
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)
  have h3 : 2 < (Nat.card R).primeFactors.card := by
    by_contra h
    exact hns (CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      (not_lt.1 h))
  obtain ⟨m, hm⟩ := l32_dvd_of_two_lt_card_primeFactors hd h3
  have hm4 : m ∣ 4 := by
    rw [hm] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 42) (by simpa using hd)
  have hm' : m = 1 ∨ m = 2 ∨ m = 4 := by
    have := Nat.le_of_dvd (by norm_num) hm4
    interval_cases m <;> omega
  rcases hm' with rfl | rfl | rfl
  · exact (l32_false_of_card_forty_two_or_eighty_four (R := R) (by omega)).elim
  · exact (l32_false_of_card_forty_two_or_eighty_four (R := R) (by omega)).elim
  · omega

theorem eq_top_of_surjective_simple {E : Subgroup PSL(3, ZMod 2)} {R : Type} [Group R] [Finite R]
    [IsSimpleGroup R] (hR : ∃ a b : R, a * b ≠ b * a) (f : ↥E →* R)
    (hf : Function.Surjective f) : E = ⊤ ∧ Function.Injective f := by
  have hRE : Nat.card R ∣ Nat.card E := Subgroup.card_dvd_of_surjective hf
  have hEX : Nat.card E ∣ 168 := card_psl_three_two ▸ Subgroup.card_subgroup_dvd_card E
  have hR168 : Nat.card R = 168 := l32_card_eq_of_simple_of_dvd hR (hRE.trans hEX)
  have hE168 : Nat.card E = 168 := Nat.dvd_antisymm hEX (hR168 ▸ hRE)
  refine ⟨Subgroup.eq_top_of_card_eq E (hE168.trans card_psl_three_two.symm), ?_⟩
  exact (hf.bijective_of_nat_card_le (by rw [hE168, hR168])).1

theorem not_three_dvd_index_range_conj :
    ¬ 3 ∣ (MulAut.conj : PSL(3, ZMod 2) →* MulAut PSL(3, ZMod 2)).range.index := by
  let e : PSL(3, ZMod 2) ≃* GL32 := L32Insp.pslEquiv
  have hmap : (MulAut.conj : PSL(3, ZMod 2) →* MulAut PSL(3, ZMod 2)).range.map
      ((MulAut.congr e : MulAut PSL(3, ZMod 2) ≃* MulAut GL32) :
        MulAut PSL(3, ZMod 2) →* MulAut GL32) = L32Insp.Inn := by
    ext α
    constructor
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨e g, MulEquiv.ext fun h => ?_⟩
      simp [MulAut.congr_apply]
    · rintro ⟨g, rfl⟩
      refine ⟨MulAut.conj (e.symm g), ⟨e.symm g, rfl⟩, MulEquiv.ext fun h => ?_⟩
      simp [MulAut.congr_apply]
  rw [← Subgroup.index_map_equiv _ (MulAut.congr e :
    MulAut PSL(3, ZMod 2) ≃* MulAut GL32), hmap, L32Insp.index_Inn]
  norm_num

end CFSG.LocalAnalysis.RankThreeTheoremC
