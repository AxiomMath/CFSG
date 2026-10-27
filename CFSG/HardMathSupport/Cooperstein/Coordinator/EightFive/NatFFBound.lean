module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.NatFFMatching

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {E : Subgroup (Perm Ω)}

theorem stabilizer_eq_bot_of_isExp2 (hE : IsExp2 E) [IsPretransitive E Ω] (p : Ω) :
    stabilizer E p = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext q
  obtain ⟨h, rfl⟩ := exists_smul_eq E p q
  exact hE.smul_eq_of_mem_stabilizer ⟨h, rfl⟩ hg

theorem card_eq_of_isExp2_of_pretransitive (hE : IsExp2 E) [IsPretransitive E Ω] [Nonempty Ω] :
    Nat.card E = Nat.card Ω := by
  obtain ⟨p⟩ := ‹Nonempty Ω›
  have h := card_orbit_eq_index (G := E) p
  rw [stabilizer_eq_bot_of_isExp2 hE p, Subgroup.index_bot, orbit_eq_univ, Nat.card_coe_set_eq,
    Set.ncard_univ] at h
  exact h.symm

theorem natFF_numerics [Nonempty Ω] (hE : IsExp2 E) :
    ∃ m : Orb E → ℕ, (∀ ω, Nat.card (orbit E ω.out) = 2 ^ m ω) ∧
      Nat.card Ω = ∑ ω, 2 ^ m ω ∧
      Nat.card (FixTriv E) * (FixTriv E).index ^ Nat.card (Orb E) ≤ 2 ^ ∑ ω, m ω ∧
      Nat.card E = Nat.card (FixTriv E) * (FixTriv E).index ∧
      Nat.card (FixUp E) ≤ 2 ^ Nat.card (Orb E) * (FixTriv E).index ∧
      ((∃ p, ∀ g ∈ E, g p = p) → 2 * Nat.card (FixUp E) ≤ 2 ^ Nat.card (Orb E)) := by
  classical
  let i0 : Ω := Classical.arbitrary Ω
  choose m hm using fun ω : Orb E => hE.card_orbit ω.out
  have hsum : Nat.card Ω = ∑ ω, 2 ^ m ω := by
    rw [card_eq_sum_orbits E]
    exact Finset.sum_congr rfl fun ω _ => hm ω
  have hprod : ∏ ω : Orb E, Nat.card (orbit E ω.out) = 2 ^ ∑ ω, m ω := by
    rw [Finset.prod_congr rfl fun ω _ => hm ω, Finset.prod_pow_eq_pow_sum]
  have hY := card_mul_index_pow_le hE (FixTriv E) fun p => stabilizer_le_FixTriv p
  rw [hprod] at hY
  have hfp : Nat.card (FixP E) ≤ 2 ^ Nat.card (Orb E) := card_FixP_le E
  have hU := card_FixUp_eq (E := E) (i0 := i0)
  have hker := card_ker_twistFix_le (E := E) (i0 := i0)
  refine ⟨m, hm, hsum, hY, (Subgroup.card_mul_index _).symm, ?_, ?_⟩
  · rw [hU]
    exact Nat.mul_le_mul (hker.trans (card_FixEven_le.trans hfp)) (card_range_twistFix_le hE)
  · rintro ⟨p, hp⟩
    rw [hU, range_twistFix_trivial hp, mul_one]
    have := card_FixEven_mul_two_le hp
    omega

theorem card_eq_sum_gx {m : Orb E → ℕ} (hsum : Nat.card Ω = ∑ ω, 2 ^ m ω) :
    Nat.card Ω = ∑ ω, gx (m ω) + ∑ ω, m ω + Nat.card (Orb E) := by
  rw [hsum]
  have h1 : ∀ ω, 2 ^ m ω = gx (m ω) + m ω + 1 := fun ω => by
    have := gx_add (m ω)
    omega
  simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

theorem exists_eq_of_card_orb_eq_one {m : Orb E → ℕ} (hr : Nat.card (Orb E) = 1) :
    ∃ ω0 : Orb E, ∑ ω, 2 ^ m ω = 2 ^ m ω0 ∧ ∑ ω, m ω = m ω0 := by
  obtain ⟨ω0, hω0⟩ := Finset.card_eq_one.1
    (show (Finset.univ : Finset (Orb E)).card = 1 by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hr])
  exact ⟨ω0, by rw [hω0, Finset.sum_singleton], by rw [hω0, Finset.sum_singleton]⟩

theorem one_le_of_no_fixed {m : Orb E → ℕ} (hm : ∀ ω, Nat.card (orbit E ω.out) = 2 ^ m ω)
    (hf : ¬ ∃ p, ∀ g ∈ E, g p = p) (ω : Orb E) : 1 ≤ m ω := by
  by_contra hlt
  have h1 : Nat.card (orbit E ω.out) = 1 := by
    rw [hm, show m ω = 0 by omega, pow_zero]
  exact hf ⟨ω.out, fixed_of_card_orbit_eq_one h1⟩

theorem two_mul_add_two_le_two_pow {M : ℕ} (hM : 3 ≤ M) : 2 * M + 2 ≤ 2 ^ M := by
  rcases Nat.eq_or_lt_of_le hM with h | h
  · subst h
    norm_num
  · exact (two_pow_gt_four h).le

theorem two_mul_card_mul_card_FixUp_le (hE : IsExp2 E) (hn : 5 ≤ Nat.card Ω)
    (hΔ : ¬ IsMatchingGroup E) : 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ Nat.card Ω := by
  classical
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  obtain ⟨m, hm, hsum, hY, hEY, hU, hfix⟩ := natFF_numerics hE
  have hid := card_eq_sum_gx hsum
  set r := Nat.card (Orb E) with hr_def
  set y := Nat.card (FixTriv E) with hy_def
  set T := (FixTriv E).index with hT_def
  set M := ∑ ω, m ω with hM_def
  have hr : 0 < r := card_Orb_pos
  have hT : 0 < T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hy : 0 < y := Nat.card_pos
  by_cases hf : ∃ p, ∀ g ∈ E, g p = p
  ·
    have h1 := hfix hf
    have hE' : Nat.card E ≤ 2 ^ M := by
      rw [hEY]
      exact le_trans (Nat.mul_le_mul_left _ (Nat.le_self_pow hr.ne' _)) hY
    calc 2 * (Nat.card E * Nat.card (FixUp E)) = Nat.card E * (2 * Nat.card (FixUp E)) := by ring
      _ ≤ 2 ^ M * 2 ^ r := Nat.mul_le_mul hE' h1
      _ = 2 ^ (M + r) := (pow_add _ _ _).symm
      _ ≤ 2 ^ Nat.card Ω := Nat.pow_le_pow_right (by norm_num) (by omega)
  · have hpos := one_le_of_no_fixed hm hf
    have hX : 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * (y * T ^ 2) := by
      rw [hEY]
      calc 2 * (y * T * Nat.card (FixUp E)) ≤ 2 * (y * T * (2 ^ r * T)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU)
        _ = 2 ^ (r + 1) * (y * T ^ 2) := by ring
    rcases Nat.lt_or_ge r 2 with hr1 | hr2
    ·
      obtain ⟨ω0, hs, hM0⟩ := exists_eq_of_card_orb_eq_one (m := m) (show r = 1 by omega)
      rw [show r = 1 by omega, pow_one] at hY
      rw [← hM_def] at hM0
      have hn0 : Nat.card Ω = 2 ^ M := by rw [hsum, hs, hM0]
      have hM3 : 3 ≤ M := by
        by_contra h
        have : 2 ^ M ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have hTle : T ≤ 2 ^ M := le_trans (Nat.le_mul_of_pos_left _ hy) hY
      calc 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * (y * T ^ 2) := hX
        _ = 4 * ((y * T) * T) := by rw [show r = 1 by omega]; ring
        _ ≤ 4 * (2 ^ M * 2 ^ M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hY hTle)
        _ = 2 ^ (2 * M + 2) := by ring
        _ ≤ 2 ^ Nat.card Ω := by
          rw [hn0]
          exact Nat.pow_le_pow_right (by norm_num) (two_mul_add_two_le_two_pow hM3)
    · have hYT : y * T ^ 2 ≤ 2 ^ M :=
        le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT hr2)) hY
      by_cases hG : 1 ≤ ∑ ω, gx (m ω)
      ·
        calc 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * 2 ^ M :=
              hX.trans (Nat.mul_le_mul_left _ hYT)
          _ = 2 ^ (r + 1 + M) := (pow_add _ _ _).symm
          _ ≤ 2 ^ Nat.card Ω := Nat.pow_le_pow_right (by norm_num) (by omega)
      ·
        have hG0 : ∑ ω, gx (m ω) = 0 := by omega
        have hm1 : ∀ ω, m ω = 1 := fun ω => le_antisymm (arith_fixed m hG0 ω) (hpos ω)
        have hMr : M = r := by
          rw [hM_def, hr_def, Finset.sum_congr rfl fun ω _ => hm1 ω, Finset.sum_const,
            Finset.card_univ, smul_eq_mul, mul_one, Nat.card_eq_fintype_card]
        have hn2 : Nat.card Ω = r + r := by omega
        rw [hMr] at hY hYT
        by_cases hT1 : T = 1
        ·
          have hEy : Nat.card E = y := by rw [hEY, hT1, mul_one]
          obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hE.isPGroup
          have hkr : k < r := by
            by_contra hkr
            apply hΔ
            refine isMatchingGroup_of_card (fun i => ?_) ?_
            · rw [card_orbit_eq_two_pow hm, hm1, pow_one]
            · rw [hk]
              exact Nat.pow_le_pow_right (by norm_num) (by omega)
          calc 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * (y * T ^ 2) := hX
            _ = 2 ^ (r + 1) * 2 ^ k := by rw [hT1, one_pow, mul_one, ← hEy, hk]
            _ = 2 ^ (r + 1 + k) := (pow_add _ _ _).symm
            _ ≤ 2 ^ Nat.card Ω := Nat.pow_le_pow_right (by norm_num) (by omega)
        ·
          have hT2 : 2 ≤ T := by omega
          have hr3 : 3 ≤ r := by omega
          have h3 : 2 * (y * T ^ 2) ≤ 2 ^ r :=
            calc 2 * (y * T ^ 2) ≤ T * (y * T ^ 2) := Nat.mul_le_mul_right _ hT2
              _ = y * T ^ 3 := by ring
              _ ≤ y * T ^ r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT hr3)
              _ ≤ 2 ^ r := hY
          calc 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * (y * T ^ 2) := hX
            _ = 2 ^ r * (2 * (y * T ^ 2)) := by ring
            _ ≤ 2 ^ r * 2 ^ r := Nat.mul_le_mul_left _ h3
            _ = 2 ^ Nat.card Ω := by rw [← pow_add, hn2]

theorem orbit_offender_shape (hE : IsExp2 E) (hn : 5 ≤ Nat.card Ω)
    (horb : ∀ i : Ω, 4 ≤ Nat.card (orbit E i))
    (hoff : 2 ^ Nat.card Ω ≤ 2 * (Nat.card E * Nat.card (FixUp E))) :
    Nat.card Ω = 8 ∧ Nat.card E = 8 ∧ IsPretransitive E Ω := by
  classical
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  obtain ⟨m, hm, hsum, hY, hEY, hU, -⟩ := natFF_numerics hE
  have hid := card_eq_sum_gx hsum
  set r := Nat.card (Orb E) with hr_def
  set y := Nat.card (FixTriv E) with hy_def
  set T := (FixTriv E).index with hT_def
  set M := ∑ ω, m ω with hM_def
  have hr : 0 < r := card_Orb_pos
  have hT : 0 < T := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hy : 0 < y := Nat.card_pos
  have hm2 : ∀ ω, 2 ≤ m ω := by
    intro ω
    by_contra h
    have h4 := horb ω.out
    rw [hm] at h4
    have : 2 ^ m ω ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hX : 2 * (Nat.card E * Nat.card (FixUp E)) ≤ 2 ^ (r + 1) * (y * T ^ 2) := by
    rw [hEY]
    calc 2 * (y * T * Nat.card (FixUp E)) ≤ 2 * (y * T * (2 ^ r * T)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU)
      _ = 2 ^ (r + 1) * (y * T ^ 2) := by ring
  rcases Nat.lt_or_ge r 2 with hr1 | hr2
  · have hr1' : r = 1 := by omega
    obtain ⟨ω0, hs, hM0⟩ := exists_eq_of_card_orb_eq_one (m := m) hr1'
    rw [hr1', pow_one] at hY
    rw [← hM_def] at hM0
    have hn0 : Nat.card Ω = 2 ^ M := by rw [hsum, hs, hM0]
    have hTle : T ≤ y * T := Nat.le_mul_of_pos_left _ hy
    have hEle : Nat.card E ≤ 2 ^ M := by rw [hEY]; exact hY
    have hsq : 2 ^ Nat.card Ω ≤ 4 * (Nat.card E * Nat.card E) := by
      calc 2 ^ Nat.card Ω ≤ 2 ^ (r + 1) * (y * T ^ 2) := hoff.trans hX
        _ = 4 * ((y * T) * T) := by rw [hr1']; ring
        _ ≤ 4 * ((y * T) * (y * T)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hTle)
        _ = 4 * (Nat.card E * Nat.card E) := by rw [hEY]
    have hM3 : M = 3 := by
      have hM2 : 2 ≤ M := by rw [hM0]; exact hm2 ω0
      have hle : 2 ^ (2 ^ M) ≤ 2 ^ (2 * M + 2) := by
        calc 2 ^ (2 ^ M) = 2 ^ Nat.card Ω := by rw [hn0]
          _ ≤ 4 * (Nat.card E * Nat.card E) := hsq
          _ ≤ 4 * (2 ^ M * 2 ^ M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hEle hEle)
          _ = 2 ^ (2 * M + 2) := by ring
      have hle' := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
      have hM4 : M < 4 := by
        by_contra h
        have := two_pow_gt_four (show 4 ≤ M by omega)
        omega
      have h5 : 5 ≤ 2 ^ M := hn0 ▸ hn
      interval_cases M
      · norm_num at h5
      · rfl
    have hn8 : Nat.card Ω = 8 := by rw [hn0, hM3]; norm_num
    refine ⟨hn8, ?_, ?_⟩
    · have hE8 : Nat.card E ≤ 8 := by rw [hM3] at hEle; simpa using hEle
      rw [hn8, show (2 : ℕ) ^ 8 = 256 by norm_num] at hsq
      by_contra hne
      have hE7 : Nat.card E ≤ 7 := by omega
      have : Nat.card E * Nat.card E ≤ 7 * 7 := Nat.mul_le_mul hE7 hE7
      omega
    · exact (pretransitive_iff_subsingleton_quotient E Ω).2 (Nat.card_eq_one_iff_unique.1 hr1').1
  ·
    exfalso
    have hYT : y * T ^ 2 ≤ 2 ^ M :=
      le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hT hr2)) hY
    have hG : r ≤ ∑ ω, gx (m ω) := by
      calc r = ∑ _ω : Orb E, 1 := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hr_def,
                Nat.card_eq_fintype_card]
        _ ≤ ∑ ω, gx (m ω) := Finset.sum_le_sum fun ω _ => gx_ge_one (hm2 ω)
    have hle : 2 ^ Nat.card Ω ≤ 2 ^ (r + 1 + M) := by
      calc 2 ^ Nat.card Ω ≤ 2 ^ (r + 1) * (y * T ^ 2) := hoff.trans hX
        _ ≤ 2 ^ (r + 1) * 2 ^ M := Nat.mul_le_mul_left _ hYT
        _ = 2 ^ (r + 1 + M) := (pow_add _ _ _).symm
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
    omega

theorem eight_mul_card_FixUp_zpowers_le (hn : 8 ≤ Nat.card Ω) {b : Perm Ω} (hb : b * b = 1)
    (hfix : ∀ i, b i ≠ i) : 8 * Nat.card (FixUp (Subgroup.zpowers b)) ≤ 2 ^ Nat.card Ω := by
  classical
  have : Nonempty Ω := (Nat.card_pos_iff.1 (by omega)).1
  have hE : IsExp2 (Subgroup.zpowers b) := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hb, one_zpow]
  have hcardE : Nat.card (Subgroup.zpowers b) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hb)
  have h2 : ∀ i : Ω, Nat.card (orbit (Subgroup.zpowers b) i) = 2 := by
    intro i
    apply le_antisymm
    · rw [card_orbit_eq_index]
      exact (Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)).trans hcardE
    · rw [Nat.card_coe_set_eq, ← Set.ncard_pair (hfix i).symm]
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro j hj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
      rcases hj with rfl | rfl
      · exact mem_orbit_self _
      · exact ⟨⟨b, Subgroup.mem_zpowers b⟩, rfl⟩
  obtain ⟨m, -, -, -, hEY, hU, -⟩ := natFF_numerics hE
  have hn2 := card_eq_two_mul_card_orb h2
  have hT : (FixTriv (Subgroup.zpowers b)).index ≤ 2 := by
    calc (FixTriv (Subgroup.zpowers b)).index ≤ Nat.card (Subgroup.zpowers b) := by
          rw [hEY]; exact Nat.le_mul_of_pos_left _ Nat.card_pos
      _ ≤ 2 := hcardE
  calc 8 * Nat.card (FixUp (Subgroup.zpowers b))
      ≤ 8 * (2 ^ Nat.card (Orb (Subgroup.zpowers b)) * 2) :=
        Nat.mul_le_mul_left _ (hU.trans (Nat.mul_le_mul_left _ hT))
    _ = 2 ^ (Nat.card (Orb (Subgroup.zpowers b)) + 4) := by ring
    _ ≤ 2 ^ Nat.card Ω := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
