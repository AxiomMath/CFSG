module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4ThreeIdx

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Equiv Equiv.Perm Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem sign_eq_neg_one_of_orderOf_eight {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω = 9) {σ : Perm Ω} (hσ : orderOf σ = 8) : Perm.sign σ = -1 := by
  have hl : σ.cycleType.lcm = 8 := by rw [Perm.lcm_cycleType, hσ]
  have hs : σ.cycleType.sum ≤ 9 := by
    rw [Perm.sum_cycleType]
    calc σ.support.card ≤ Fintype.card Ω := Finset.card_le_univ _
      _ = 9 := hΩ
  have h2 : ∀ n ∈ σ.cycleType, 2 ≤ n := fun n hn => Perm.two_le_of_mem_cycleType hn
  have h8 : 8 ∈ σ.cycleType := by
    by_contra hn
    have hdvd : σ.cycleType.lcm ∣ 4 := by
      rw [Multiset.lcm_dvd]
      intro b hb
      have hb8 : b ∣ 8 := hl ▸ Multiset.dvd_lcm hb
      have hb2 := h2 b hb
      have hb8' : b ≤ 8 := Nat.le_of_dvd (by norm_num) hb8
      have hbne : b ≠ 8 := fun h => hn (h ▸ hb)
      interval_cases b <;> omega
    rw [hl] at hdvd
    exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)
  obtain ⟨c', hc'⟩ := Multiset.exists_cons_of_mem h8
  have hc'0 : c' = 0 := by
    by_contra hne
    obtain ⟨n, hn⟩ := Multiset.exists_mem_of_ne_zero hne
    have hn2 : 2 ≤ n := h2 n (by rw [hc']; exact Multiset.mem_cons_of_mem hn)
    have hnle : n ≤ c'.sum := Multiset.le_sum_of_mem hn
    rw [hc', Multiset.sum_cons] at hs
    omega
  rw [Perm.sign_of_cycleType, hc', hc'0]
  simp only [Multiset.sum_cons, Multiset.sum_zero, Multiset.card_cons, Multiset.card_zero]
  exact Odd.neg_one_pow (by decide)

theorem no_small_index_of_card_6048 {Y : Type} [Group Y] [Finite Y] [IsSimpleGroup Y]
    (hcard : Nat.card Y = 6048) (h8 : ∃ y : Y, orderOf y = 8) (M : Subgroup Y) (hM : M ≠ ⊤) :
    11 < M.index := by
  classical
  by_contra hle
  push Not at hle
  have hm1 : M.index ≠ 1 := fun h => hM (Subgroup.index_eq_one.mp h)
  have hm0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  let Ω := Y ⧸ M
  have : Fintype Ω := Fintype.ofFinite Ω
  have hΩ' : Nat.card Ω = M.index := rfl
  have hΩcard : Fintype.card Ω = M.index := by rw [← hΩ', Nat.card_eq_fintype_card]
  have hnt : Nontrivial Ω := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  let φ : Y →* Perm Ω := MulAction.toPermHom Y Ω
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker φ) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
      obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y a b
      have hyk : y ∈ MonoidHom.ker φ := h ▸ mem_top y
      have h1 : φ y = 1 := hyk
      have h2 : y • a = a := by
        have := congrArg (fun f : Perm Ω => f a) h1
        simpa [φ] using this
      exact hab (h2.symm.trans hy)
  have hdvd : 6048 ∣ (M.index).factorial := by
    have h1 : Nat.card Y ∣ Nat.card (Perm Ω) := Subgroup.card_dvd_of_injective φ hinj
    rw [hcard, Nat.card_perm, hΩ'] at h1
    exact h1
  have hidx : M.index ∣ 6048 := hcard ▸ Subgroup.index_dvd_card M
  have h9 : M.index = 9 := by
    generalize M.index = m at hle hdvd hidx hm0 hm1
    interval_cases m
    all_goals first | exact absurd rfl hm1 | exact absurd rfl hm0 | rfl | (revert hdvd; decide) | (revert hidx; decide)
  obtain ⟨y, hy⟩ := h8
  have hσ : orderOf (φ y) = 8 := by rw [orderOf_injective φ hinj y]; exact hy
  have hsign : Perm.sign (φ y) = -1 :=
    sign_eq_neg_one_of_orderOf_eight (by rw [hΩcard, h9]) hσ
  let sg : Y →* ℤˣ := Perm.sign.comp φ
  have hsy : sg y = -1 := hsign
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker sg) with h | h
  · have hy2 : y ^ 2 ∈ MonoidHom.ker sg := by
      rw [MonoidHom.mem_ker, map_pow, hsy]
      decide
    rw [h, Subgroup.mem_bot] at hy2
    have := orderOf_dvd_of_pow_eq_one hy2
    rw [hy] at this
    omega
  · have : y ∈ MonoidHom.ker sg := h ▸ mem_top y
    rw [MonoidHom.mem_ker, hsy] at this
    exact absurd this (by decide)

section Concrete

open CFSG.LinearGroups.UnitaryThreeOverNine

variable {K : Type} [Field K]

theorem exists_orderOf_eight_statedSU_three (hK : Nat.card K = 9) :
    ∃ g : StatedSU 3 3 K, orderOf g = 8 := by
  obtain ⟨i, hi⟩ := exists_units_orderOf_eq_four hK
  obtain ⟨⟨s, t, w, hs, ht, hw⟩, hmain⟩ := wreath_sylow_model hK i hi
  obtain ⟨hst, -, -, -, hw2, -, hwst, -, -, -, -, hord2, -, -⟩ := hmain s t w hs ht hw
  have hww : w * w = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hw2])
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hwsw : w * s * w = t := by
    rw [hwinv] at hwst
    exact hwst
  have hg2 : (s * w) ^ 2 = s * t := by
    rw [sq]
    calc s * w * (s * w) = s * (w * s * w) := by group
      _ = s * t := by rw [hwsw]
  have hst4 : (s * t) ^ 4 = 1 := by
    have : (s * t) ^ 4 = ((s * t) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord2])
  have hst2 : (s * t) ^ 2 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord2
    omega
  have hg4 : (s * w) ^ 4 = (s * t) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hg2]
  have hg8 : (s * w) ^ 8 = 1 := by
    rw [show (8 : ℕ) = 4 * 2 by norm_num, pow_mul, hg4]
    have : ((s * t) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact hst4
    exact this
  refine ⟨s * w, ?_⟩
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := s * w) (by
    rw [show 2 ^ 2 = 4 by norm_num, hg4]
    exact hst2) (by
    rw [show 2 ^ (2 + 1) = 8 by norm_num]
    exact hg8)
  rw [this]
  norm_num

end Concrete

open CFSG.LinearGroups.UnitaryThreeOverNine in
theorem minIndexU33 : MinIndexU33 := by
  intro Y _ hY M hM
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (3 ^ 1) ^ 2 ∧ Nonempty (Y ≃* StatedProj (StatedSU 3 (3 ^ 1) K)) := by
    rcases hY with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hK9 : Nat.card K = 9 := by rw [hcard]; norm_num
  have e' : Y ≃* StatedProj (StatedSU 3 3 K) := e
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hs : IsSimpleGroup (StatedProj (StatedSU 3 3 K)) :=
    isSimpleGroup_statedProj_three_odd (K := K) (p := 3) (f := 1) hcard (by norm_num)
  have : IsSimpleGroup Y := e'.isSimpleGroup
  have : Finite Y := Finite.of_equiv _ e'.symm.toEquiv
  have hbot := statedScalars_subgroupOf_statedSU_eq_bot hK9
  let π : StatedSU 3 3 K →* StatedProj (StatedSU 3 3 K) := QuotientGroup.mk' _
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcardY : Nat.card Y = 6048 := by
    rw [Nat.card_congr e'.toEquiv, ← card_statedSU hK9]
    exact (Nat.card_congr (Equiv.ofBijective π ⟨hπinj, hπsurj⟩)).symm
  obtain ⟨g, hg⟩ := exists_orderOf_eight_statedSU_three hK9
  exact no_small_index_of_card_6048 hcardY
    ⟨e'.symm (π g), by rw [MulEquiv.orderOf_eq, orderOf_injective π hπinj g, hg]⟩ M hM

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
