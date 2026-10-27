module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeTwo
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.DigitConds
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.SmallCheck

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section NodeBound


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]
  {s : N6}

theorem odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ⟨2 ^ m - 1, by rw [pow_succ]; have := Nat.one_le_two_pow (n := m); omega⟩

theorem hv0_of_notMem {J : Finset N6} (T : NodeTab s) (hs : s ∉ J) :
    ∀ j, reflect Tag.E6 j T.v0F ≠ T.v0F → j ∉ J := by
  intro j hj
  by_cases hjs : j = s
  · exact hjs ▸ hs
  · exact absurd (T.fam_hv0 j hjs) hj

theorem node_dim_big [Module.Finite k V] (T : NodeTab s) {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k ↥(e6Data_valid.minGroup K) V}
    (hρ : IsSimpleRep ρ) {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J)
    {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) (h2 : 2 ≤ J'.card)
    (hgood : ∑ i ∈ J', 2 ^ i < 2 ^ n - 1 →
      3 ≤ Nat.gcd (∑ i ∈ J', 2 ^ i) (2 ^ n - 1) ∨ (J'.card ≤ 3 ∧ 6 ≤ n))
    (hvec : ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y, e ≠ 0 ∧
      e ∈ wt ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s)) :
    T.A * T.B ≤ Module.finrank k V := by
  classical
  obtain ⟨b, hb⟩ : J'.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨e, he, he0, hew⟩ := hvec b hb
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hbn : b < n := hJ' b hb
  have hn2 : 2 ≤ n := by
    by_contra hcon
    have hsub : J' ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hJ' i hi)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hMod : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have haM' : a ≤ 2 ^ n - 1 := sum_two_pow_le J' hJ'
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (pair_le_sum h2 hb)
  by_cases haM : a = 2 ^ n - 1
  · rw [haM] at hew
    exact node_dim_R2 (s := s) T.wW T.uW hρ ht hs hK hn2 b T.fam_hU T.fam_hU2 T.v0F
      (hv0_of_notMem T hs) T.fam_hdist T.fam_hβinj T.fam_hβ he he0 hew
  · have haM2 : a < 2 ^ n - 1 := by omega
    have hA0 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (a : ℤ)) := by
      intro h
      have := Int.le_of_dvd (by exact_mod_cast ha0) h
      have h' : 2 ^ n - 1 ≤ a := by exact_mod_cast this
      omega
    refine node_dim_of_sep (s := s) T.wW T.uW hK a b T.fam_hU he0 hew ?_
    intro p q hcong
    have hcong' : ∀ i, (((2 ^ n - 1 : ℕ) : ℤ)) ∣ ((a : ℤ) * famX s T.wW T.uW p.1 p.2 i -
        2 ^ b * famB s T.wW p.1 i) - ((a : ℤ) * famX s T.wW T.uW q.1 q.2 i -
        2 ^ b * famB s T.wW q.1 i) := by
      intro i
      simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using hcong i
    have hinjP : ∀ p q : Fin T.A × Fin T.B, famX s T.wW T.uW p.1 p.2 = famX s T.wW T.uW q.1 q.2 →
        famB s T.wW p.1 = famB s T.wW q.1 → p = q := by
      intro p q h1 h2
      obtain ⟨e1, e2⟩ := T.fam_hinj p.1 q.1 p.2 q.2 h1 h2
      exact Prod.ext e1 e2
    by_cases h3 : 3 ≤ Nat.gcd a (2 ^ n - 1)
    · exact class_sep_gcd (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
        (fun p => famB s T.wW p.1) (2 ^ n - 1) a b hMod h3
        (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP hA0 p q
        hcong'
    · have hcard3 : J'.card ≤ 3 := by
        rcases hgood haM2 with h | h
        · exact absurd h h3
        · exact h.1
      have hgcd1 : Nat.gcd a (2 ^ n - 1) = 1 := by
        have hodd : Odd (Nat.gcd a (2 ^ n - 1)) := Odd.of_dvd_nat hMod (Nat.gcd_dvd_right _ _)
        have hpos : 0 < Nat.gcd a (2 ^ n - 1) := Nat.gcd_pos_of_pos_left _ ha0
        rcases hodd with ⟨m, hm⟩
        omega
      have hn6 : 6 ≤ n := by
        rcases hgood haM2 with h | h
        · exact absurd h h3
        · exact h.2
      have hbig : 32 < 2 ^ n - 1 := by
        have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn6
        omega
      have hD3 := digit_D3 (J' := J') (n := n) (by omega)
      obtain ⟨c0, c1, c2, c3, c4, c5, c6⟩ := digit_conds hn2 hJ' hb h2 haM2 hD3
      exact class_sep_unit (fun p : Fin T.A × Fin T.B => famX s T.wW T.uW p.1 p.2)
        (fun p => famB s T.wW p.1) (2 ^ n - 1) a b hMod hbig hgcd1
        (fun p i => T.fam_bdX p.1 p.2 i) (fun p i => T.fam_bdβ p.1 i)
        (fun p q h => T.fam_hβ p.1 q.1 h) (fun p q h => T.fam_hX p.1 q.1 p.2 q.2 h) hinjP
        c0 c1 c2 c3 c4 c5 c6 p q hcong'

theorem node_dim_small [Module.Finite k V] (S : NodeTab s)
    (hsm : ClassSepSmall s S.wTab S.uTab S.A S.B) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J)
    {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) (h2 : 2 ≤ J'.card) (h5 : n ≤ 5)
    (hlt : ∑ i ∈ J', 2 ^ i < 2 ^ n - 1)
    (hvec : ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y, e ≠ 0 ∧
      e ∈ wt ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s)) :
    S.A * S.B ≤ Module.finrank k V := by
  classical
  obtain ⟨b, hb⟩ : J'.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨e, he, he0, hew⟩ := hvec b hb
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  have hbn : b < n := hJ' b hb
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.zero_le _) (pair_le_sum h2 hb)
  have hn3 : 3 ≤ n := by
    by_contra hcon
    have hn2 : n ≤ 2 := by omega
    have hsub : J' ⊆ Finset.range n := fun i hi => Finset.mem_range.2 (hJ' i hi)
    have hcard := Finset.card_le_card hsub
    simp at hcard
    have : n = 2 := by omega
    subst this
    obtain ⟨c, hc, hcb⟩ : ∃ c ∈ J', c ≠ b := by
      by_contra hcon'
      push Not at hcon'
      have : J'.card ≤ 1 := Finset.card_le_one.2 fun x hx y hy =>
        (hcon' x hx).trans (hcon' y hy).symm
      omega
    have hsub2 : ({b, c} : Finset ℕ) ⊆ J' := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h4 := Finset.sum_le_sum_of_subset (f := fun i => 2 ^ i) hsub2
    rw [Finset.sum_pair (Ne.symm hcb)] at h4
    have hb2 : b < 2 := hJ' b hb
    have hc2 : c < 2 := hJ' c hc
    have : 2 ^ b + 2 ^ c = 3 := by
      interval_cases b <;> interval_cases c <;> simp_all
    omega
  refine node_dim_of_sep (s := s) S.wW S.uW hK a b S.fam_hU he0 hew ?_
  intro p q hcong
  exact hsm n a b hn3 h5 ha0 hlt hbn (testBit_sum_of_mem hb) (sum_ne_two_pow h2 b) p q hcong

theorem node_copies [Module.Finite k V] (T : NodeTab s)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J) :
    T.B * Module.finrank k (orbitSpan (ρ.comp (rankOne6 K s)) y) ≤ Module.finrank k V := by
  let u' : Fin T.B → WeylGroup Tag.E6 := fun j => (coxeterSystem Tag.E6).wordProd (T.uW j)
  have hu : ∀ j, u' j • (Pi.single s 1 : N6 → ℤ) = Pi.single s 1 := by
    intro j; rw [wordProd_smul_foldr, T.fam_hU2 j]
  have hli : LinearIndependent k (fun j => ρ (canonMin K (u' j)) y) := by
    refine linearIndependent_translates_support hρ ht (hv0_of_notMem T hs) u' ?_
    intro j j' hjj h
    apply T.fam_hdist j j' hjj
    have := h
    simp only [u', wordProd_smul_foldr] at this
    exact this
  exact copies_finrank_orbit hρ ht u' hu hli

theorem six_pow_ge {t : ℕ} (h : 7 ≤ t) : 78 * t + 2 ≤ 6 * 2 ^ t := by
  induction t, h using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; omega

theorem node_dim_two [Module.Finite k V] (T : NodeTab s)
    (hprim : ∀ i : Fin T.A, ∀ d : ℕ, (∀ c, (d : ℤ) ∣ famB s T.wW i c) → d = 1)
    {n g : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (hg : 1 ≤ g) (hgn : g ∣ n) (h4 : 4 * g ≤ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hs : s ∉ J)
    {J' : Finset ℕ} (hJ' : ∀ i ∈ J', i < n) (hne : J'.Nonempty)
    (hper : (2 ^ n - 1) ∣ (2 ^ g - 1) * ∑ i ∈ J', 2 ^ i)
    (hvec : ∀ b ∈ J', ∃ e ∈ orbitSpan (ρ.comp (rankOne6 K s)) y, e ≠ 0 ∧
      e ∈ wt ρ (((∑ i ∈ J', 2 ^ i : ℕ) : ℤ) • omegaF s - (2 : ℤ) ^ b • alphaF s)) :
    2 * (T.A * T.B) ≤ Module.finrank k V := by
  classical
  set a : ℕ := ∑ i ∈ J', 2 ^ i with ha
  obtain ⟨b, hb⟩ := hne
  have hn3 : 3 ≤ n := by omega
  have hMo : Odd (2 ^ n - 1) := odd_two_pow_sub_one hn
  have haM' : a ≤ 2 ^ n - 1 := sum_two_pow_le J' hJ'
  have ha0 : 0 < a := lt_of_lt_of_le (Nat.two_pow_pos _)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  by_cases haM : a = 2 ^ n - 1
  ·
    have hJrange : J' = Finset.range n := by
      apply Finset.equivBitIndices.symm.injective
      have h1 := sum_range_two_pow n
      show ∑ i ∈ J', 2 ^ i = ∑ i ∈ Finset.range n, 2 ^ i
      omega
    have h0 : 0 ∈ J' := by rw [hJrange]; exact Finset.mem_range.2 (by omega)
    have h1 : 1 ∈ J' := by rw [hJrange]; exact Finset.mem_range.2 (by omega)
    obtain ⟨e, he, he0, hew⟩ := hvec 0 h0
    obtain ⟨e', he', he0', hew'⟩ := hvec 1 h1
    rw [haM] at hew hew'
    exact two_dim_eq T hprim hn3 hK hρ ht hs (b := 0) (b' := 1) rfl he he' he0 he0' hew hew'
  · have haM2 : a < 2 ^ n - 1 := by omega
    have hA0 : ¬ (((2 ^ n - 1 : ℕ) : ℤ) ∣ (a : ℤ)) := by
      intro h
      have := Int.le_of_dvd (by exact_mod_cast ha0) h
      have h' : 2 ^ n - 1 ≤ a := by exact_mod_cast this
      omega
    have hb' : (b + g) % n ∈ J' := shift_mem hn hJ' hper hb
    obtain ⟨e, he, he0, hew⟩ := hvec b hb
    obtain ⟨e', he', he0', hew'⟩ := hvec _ hb'
    have hgcd3 : 3 ≤ Nat.gcd a (2 ^ n - 1) := by
      have h := gcd_ge_pow hn hg hgn hper ha0
      have h8 : 2 ^ 3 ≤ 2 ^ (n - g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hbig : 2 ^ (g + 1) + 2 < Nat.gcd a (2 ^ n - 1) := by
      have h := gcd_ge_pow hn hg hgn hper ha0
      have h3 : 2 ^ (3 * g) ≤ 2 ^ (n - g) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : 2 ^ (g + 1) + 2 < 2 ^ (3 * g) := by
        have hP : 2 ≤ 2 ^ g := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
        have e1 : 2 ^ (g + 1) = 2 * 2 ^ g := by rw [pow_succ]; ring
        have e2 : 2 ^ (3 * g) = 2 ^ g * 2 ^ g * 2 ^ g := by rw [pow_mul']; ring
        rw [e1, e2]
        nlinarith
      omega
    have hbm : (((2 ^ n - 1 : ℕ) : ℤ)) ∣ 2 ^ ((b + g) % n) - 2 ^ (b + g) := by
      have := (Nat.modEq_iff_dvd).1 (two_pow_mod_n n (b + g)).symm
      push_cast at this
      exact this
    exact two_dim_lt T hprim hn hK hg hMo hA0 hgcd3 hbig hbm he0 he0' hew hew'

theorem node_bound [Module.Finite k V] (T S : NodeTab s)
    (hsm : ClassSepSmall s S.wTab S.uTab S.A S.B)
    (hprim : ∀ i : Fin T.A, ∀ d : ℕ, (∀ c, (d : ℤ) ∣ famB s T.wW i c) → d = 1)
    (h79 : 79 ≤ S.A * S.B) (hAB : 392 ≤ T.A * T.B) (hAB2 : 470 ≤ 2 * (T.A * T.B))
    (hB : 6 ≤ T.B) {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hJ : ∀ s', s' ≠ s → s' ∈ J) (hs : s ∉ J)
    {g : ℕ} (hg : 1 ≤ g) (hgn : g ∣ n)
    (hper : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) ^ (2 ^ g) = χ (e6Data_valid.hm K s z)) :
    (n / g = 1 → (∃ b, b < n ∧ ∀ z : Kˣ,
        χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (2 ^ b)) ∨
        79 ≤ Module.finrank k V) ∧
      (2 ≤ n / g → 78 * (n / g) + 2 ≤ Module.finrank k V) := by
  classical
  obtain ⟨J', hJ', hε, hJ0, hdim, hvec⟩ := string_wt_vec hK hρ ht hJ
  have hne := string_nonempty hn hK ht hs hε hJ0
  have hper' := periodic_dvd hK hε hper
  have hcardt := card_ge_of_periodic hg hgn hJ' hne hper'
  have ht1 : 1 ≤ n / g := Nat.div_pos (Nat.le_of_dvd (by omega) hgn) (by omega)
  have ha0 : 0 < ∑ i ∈ J', 2 ^ i := by
    obtain ⟨b, hb⟩ := id hne
    exact lt_of_lt_of_le (Nat.two_pow_pos _)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have hcop := node_copies T hρ ht hs
  rw [hdim] at hcop
  have hcop4 : 4 ≤ J'.card → 79 ≤ Module.finrank k V := by
    intro h4
    have h2 : 2 ^ 4 ≤ 2 ^ J'.card := Nat.pow_le_pow_right (by norm_num) h4
    have h3 : T.B * 2 ^ 4 ≤ T.B * 2 ^ J'.card := Nat.mul_le_mul_left _ h2
    omega
  refine ⟨fun h1 => ?_, fun h2 => ?_⟩
  · by_cases hc1 : J'.card = 1
    · left
      obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hc1
      refine ⟨b, hJ' b (by rw [hb]; exact Finset.mem_singleton_self b), fun z => ?_⟩
      rw [hε z, hb]
      simp
    · right
      have hc2 : 2 ≤ J'.card := by
        have := hne.card_pos
        omega
      by_cases h4 : 4 ≤ J'.card
      · exact hcop4 h4
      · have hc3 : J'.card ≤ 3 := by omega
        by_cases hlt : ∑ i ∈ J', 2 ^ i < 2 ^ n - 1
        · by_cases h3 : 3 ≤ Nat.gcd (∑ i ∈ J', 2 ^ i) (2 ^ n - 1)
          · have := node_dim_big T hn hK hρ ht hs hJ' hc2 (fun _ => Or.inl h3) hvec
            omega
          · by_cases hn6 : 6 ≤ n
            · have := node_dim_big T hn hK hρ ht hs hJ' hc2
                (fun _ => Or.inr ⟨hc3, hn6⟩) hvec
              omega
            · have := node_dim_small S hsm hn hK hρ ht hs hJ' hc2 (by omega) hlt hvec
              omega
        · have := node_dim_big T hn hK hρ ht hs hJ' hc2 (fun h => absurd h hlt) hvec
          omega
  · by_cases ht7 : 7 ≤ n / g
    · have h1 : 6 * 2 ^ (n / g) ≤ T.B * 2 ^ J'.card := by
        have h2' : 2 ^ (n / g) ≤ 2 ^ J'.card := Nat.pow_le_pow_right (by norm_num) hcardt
        exact Nat.mul_le_mul hB h2'
      have := six_pow_ge ht7
      omega
    · by_cases ht6 : n / g = 6
      · have h4 : 4 * g ≤ n := by
          obtain ⟨t, rfl⟩ := hgn
          have ht' : t = 6 := by
            rw [Nat.mul_div_cancel_left t (by omega)] at ht6; exact ht6
          subst ht'
          omega
        have := node_dim_two T hprim hn hK hg hgn h4 hρ ht hs hJ' hne hper' hvec
        omega
      · have hcj : 2 ≤ J'.card := by omega
        have := node_dim_big T hn hK hρ ht hs hJ' hcj
          (fun _ => Or.inl (gcd_ge_three hg hgn h2 hper' ha0)) hvec
        omega

end NodeBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
