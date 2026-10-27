module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalElems
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalThreeB
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocalCover
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenCensus
public import CFSG.Monster.Existence.MilestoneInputs
public import CFSG.Monster.Existence.BabyTableIVOf

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

open CFSG.Blueprint CFSG.Monster.GMS Subgroup CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23

section Witness

theorem mul_self_of_babyInv {k : Fin 4} {r : NativeSporadic.B} (hr : BabyInv k r) : r * r = 1 := by
  have h := pow_orderOf_eq_one r
  rw [hr.1] at h
  rw [← sq]
  exact h

theorem line_facts {G : Type*} [Group G] {x f r : G} (j : ℕ) (hxf : x * f = f * x)
    (hx : x ^ 7 = 1) (hf : f ^ 7 = 1) (hxr : x * r = r * x) (hfr : f * r = r * f) :
    (x * f ^ j) ^ 7 = 1 ∧ r * (x * f ^ j) = x * f ^ j * r := by
  have hcomm : Commute x (f ^ j) := Commute.pow_right hxf j
  have hfjr : f ^ j * r = r * f ^ j := (Commute.pow_left hfr j).eq
  refine ⟨?_, ?_⟩
  · rw [hcomm.mul_pow, hx, ← pow_mul, mul_comm, pow_mul, hf, one_pow, one_mul]
  · calc r * (x * f ^ j) = r * x * f ^ j := (mul_assoc _ _ _).symm
      _ = x * r * f ^ j := by rw [hxr]
      _ = x * (r * f ^ j) := mul_assoc _ _ _
      _ = x * (f ^ j * r) := by rw [hfjr]
      _ = x * f ^ j * r := (mul_assoc _ _ _).symm

theorem exists_pow_of_mem_zpowers_of_order {x e : NativeSporadic.B} {n : ℕ} (hn : 0 < n)
    (hx : orderOf x = n) (he : e ∈ zpowers x) : ∃ i < n, e = x ^ i := by
  obtain ⟨k, rfl⟩ := (mem_zpowers_iff (G := NativeSporadic.B)).1 he
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have e1 := Int.emod_nonneg k hn'.ne'
  have e2 := Int.emod_lt_of_pos k hn'
  refine ⟨(k % n).toNat, by omega, ?_⟩
  rw [← zpow_mod_orderOf, hx, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k hn'.ne')]

theorem exists_pow_of_mem_zpowers {x e : NativeSporadic.B} (hx : orderOf x = 7)
    (he : e ∈ zpowers x) : ∃ i < 7, e = x ^ i :=
  exists_pow_of_mem_zpowers_of_order (by norm_num) hx he

theorem line_pow {G : Type*} [Group G] {p : ℕ} {x f : G} (j : ℕ) (hxf : x * f = f * x)
    (hx : x ^ p = 1) (hf : f ^ p = 1) : (x * f ^ j) ^ p = 1 := by
  have hcomm : Commute x (f ^ j) := Commute.pow_right hxf j
  rw [hcomm.mul_pow, hx, ← pow_mul, mul_comm, pow_mul, hf, one_pow, one_mul]

theorem orbitWitness_cyclic (hT4 : BabyTableIV) {α x r s : NativeSporadic.B} {k : Fin 4}
    (hr : BabyInv 0 r) (hs : BabyInv 0 s) (hk : BabyOrbit k r s)
    (hv : ∀ N : ℕ, N * babyOrbitSize k = babyCentOrder 0 → N.factorization 7 = 1)
    (hx : orderOf x = 7) (hxr : x * r = r * x) (hxs : x * s = s * x)
    (hsep : rk (r * x) ≠ rk (α * x)) : OrbitWitness α x k := by
  refine ⟨r, s, hr, hs, hk, zpowers x, ?_, ?_, ?_⟩
  · rw [zpowers_le]
    exact ⟨(mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hxr,
      (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hxs⟩
  · rw [Nat.card_zpowers, hx, hv _ (card_inf_mul_babyOrbitSize hT4 hr hs hk), pow_one]
  · intro e he he1
    left
    obtain ⟨i, hi, rfl⟩ := exists_pow_of_mem_zpowers hx he
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact he1 (pow_zero x)
    have h7 : ¬ 7 ∣ i := fun h => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) h) (by omega)
    rw [rk_mul_pow_eq (p := 7) (by norm_num) (by norm_num) (mul_self_of_babyInv hr)
      (hx ▸ pow_orderOf_eq_one x) hxr.symm h7]
    exact hsep

theorem orbitWitness_pair (hT4 : BabyTableIV) {α x f r s : NativeSporadic.B} {k : Fin 4}
    (hr : BabyInv 0 r) (hs : BabyInv 0 s) (hk : BabyOrbit k r s)
    (hv : ∀ N : ℕ, N * babyOrbitSize k = babyCentOrder 0 → N.factorization 7 = 2)
    (hx : x ^ 7 = 1) (hx1 : x ≠ 1) (hf : f ^ 7 = 1) (hxf : x * f = f * x)
    (hfx : ∀ i < 7, f ≠ x ^ i)
    (hxr : x * r = r * x) (hxs : x * s = s * x) (hfr : f * r = r * f) (hfs : f * s = s * f)
    (hsepf : rk (r * f) ≠ rk (α * x) ∨ rk (s * f) ≠ rk (α * x))
    (hsepj : ∀ j < 7, rk (r * (x * f ^ j)) ≠ rk (α * x) ∨ rk (s * (x * f ^ j)) ≠ rk (α * x)) :
    OrbitWitness α x k := by
  have hp : Nat.Prime 7 := by norm_num
  have hfx' : f ∉ zpowers x := by
    intro hmem
    have hxo : orderOf x = 7 := orderOf_eq_prime hx hx1
    obtain ⟨i, hi, hfi⟩ := exists_pow_of_mem_zpowers hxo hmem
    exact hfx i hi hfi
  obtain ⟨hmem, hcard⟩ := @closure_pair NativeSporadic.B Units.instGroup 7 hp x f hxf hx hf hx1 hfx'
  have hr2 := mul_self_of_babyInv hr
  have hs2 := mul_self_of_babyInv hs
  refine ⟨r, s, hr, hs, hk, closure ({x, f} : Set NativeSporadic.B), ?_, ?_, ?_⟩
  · rw [closure_le]
    rintro g (rfl | rfl)
    · exact ⟨(mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hxr,
        (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hxs⟩
    · exact ⟨(mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hfr,
        (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 hfs⟩
  · rw [hcard, hv _ (card_inf_mul_babyOrbitSize hT4 hr hs hk)]
  · intro e he he1
    obtain ⟨a, b, ha, hb, rfl⟩ := hmem e he
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      simp only [not_or, ne_eq, not_not] at h
      rw [h.1, h.2, pow_zero, pow_zero, one_mul] at he1
      exact he1 rfl
    obtain ⟨m, hm0, hm7, hline⟩ := @exists_line NativeSporadic.B Units.instGroup 7 hp x f hxf hx hf
      a b ha hb hab
    have hm : ¬ 7 ∣ m := fun h => absurd (Nat.le_of_dvd hm0 h) (by omega)
    rcases hline with h | ⟨j, hj, h⟩
    · rw [h, rk_mul_pow_eq hp (by norm_num) hr2 hf hfr.symm hm,
        rk_mul_pow_eq hp (by norm_num) hs2 hf hfs.symm hm]
      exact hsepf
    · obtain ⟨he7, her⟩ := @line_facts NativeSporadic.B Units.instGroup x f r j hxf hx hf hxr hfr
      obtain ⟨-, hes⟩ := @line_facts NativeSporadic.B Units.instGroup x f s j hxf hx hf hxs hfs
      rw [h, rk_mul_pow_eq hp (by norm_num) hr2 he7 her hm,
        rk_mul_pow_eq hp (by norm_num) hs2 he7 hes hm]
      exact hsepj j hj

theorem factorization_eq_of_dvd {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ^ k ∣ n)
    (h2 : ¬ p ^ (k + 1) ∣ n) : n.factorization p = k := by
  have e1 := (hp.pow_dvd_iff_le_factorization hn).1 h1
  have e2 := mt (hp.pow_dvd_iff_le_factorization hn).2 h2
  omega

theorem ne_one_of_rk {g : NativeSporadic.B} {r : ℕ} (hr : 0 < r) (h : rk g = r) : g ≠ 1 := by
  rintro rfl
  have : rk (1 : NativeSporadic.B) = 0 := by simp [rk]
  omega

theorem orderOf_mul_eq_two {a b : NativeSporadic.B} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {r : ℕ} (hr : 0 < r) (h : rk (a * b) = r) : orderOf (a * b) = 2 := by
  have h2 : (a * b) ^ 2 = 1 := by
    rw [sq]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h2 (ne_one_of_rk hr h)

theorem factorization_stab_seven (k : Fin 4) (N : ℕ) (hN : N * babyOrbitSize k = babyCentOrder 0) :
    N.factorization 7 = if k = 1 then 2 else 1 := by
  have hp : Nat.Prime 7 := by norm_num
  fin_cases k
  · obtain rfl : N = 2 ^ 38 * 3 ^ 6 * 5 * 7 * 11 := by
      simp only [babyOrbitSize, babyCentOrder] at hN
      norm_num at hN
      omega
    exact factorization_eq_of_dvd hp (by norm_num) (by norm_num) (by norm_num)
  · obtain rfl : N = 2 ^ 26 * 3 ^ 6 * 5 ^ 2 * 7 ^ 2 * 13 * 17 := by
      simp only [babyOrbitSize, babyCentOrder] at hN
      norm_num at hN
      omega
    exact factorization_eq_of_dvd hp (by norm_num) (by norm_num) (by norm_num)
  · obtain rfl : N = 2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 := by
      simp only [babyOrbitSize, babyCentOrder] at hN
      norm_num at hN
      omega
    exact factorization_eq_of_dvd hp (by norm_num) (by norm_num) (by norm_num)
  · obtain rfl : N = 2 ^ 30 * 3 ^ 6 * 5 * 7 := by
      simp only [babyOrbitSize, babyCentOrder] at hN
      norm_num at hN
      omega
    exact factorization_eq_of_dvd hp (by norm_num) (by norm_num) (by norm_num)

end Witness

section Main


theorem babyInv_three_of_rank_2158 {X : NativeSporadic.B} (hX : orderOf X = 2)
    (hr : Matrix.rank (X.val.val - 1) = 2158) : BabyInv 3 X := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, -, b1, b0, b5, b3⟩ :=
    CFSG.Monster.B.CTIB.native_four_involution_classes
  obtain ⟨i, ⟨hi, hc⟩, -⟩ := hB X hX
  have hrk := CFSG.Monster.Existence.rank_sub_one_of_isConj hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · rw [hr, b1] at hrk
    exact absurd hrk (by norm_num)
  · rw [hr, b0] at hrk
    exact absurd hrk (by norm_num)
  · exact CFSG.Monster.Existence.babyInv_three_babyRep_five.of_isConj hc.symm
  · rw [hr, b3] at hrk
    exact absurd hrk (by norm_num)

theorem centralizer_xSeven_le :
    centralizer ({xSeven} : Set NativeSporadic.B) ≤
      centralizer ({alphaB} : Set NativeSporadic.B) := by
  have hT3 := CFSG.Monster.Existence.babyTableIII
  have hT4 := CFSG.Monster.Existence.babyTableIV
  have P := bSevenElem_parts
  have L := localParts_of_certificate
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hord2 : ∀ {g : NativeSporadic.B} {r : ℕ}, g * g = 1 → 0 < r → rk g = r → orderOf g = 2 :=
    fun h1 hr h => orderOf_eq_prime (by rw [sq]; exact h1) (ne_one_of_rk hr h)
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hx : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  have hτ₁ : BabyInv 0 tauOne :=
    babyInv_zero_of_rank_1860 (hord2 P.tauOne_sq (by norm_num) P.tauOne_rank) P.tauOne_rank
  have hτ₂ : BabyInv 0 tauTwo :=
    babyInv_zero_of_rank_1860 (hord2 P.tauTwo_sq (by norm_num) P.tauTwo_rank) P.tauTwo_rank
  have hs₃ : BabyInv 0 sThree :=
    babyInv_zero_of_rank_1860 (hord2 L.s3_sq (by norm_num) L.s3_rk) L.s3_rk
  have hs₄ : BabyInv 0 sFour :=
    babyInv_zero_of_rank_1860 (hord2 L.s4_sq (by norm_num) L.s4_rk) L.s4_rk
  have ho0 : BabyOrbit 0 tauOne tauTwo :=
    CFSG.Monster.Existence.babyInv_one_of_rank_2048
      (orderOf_mul_eq_two P.tauOne_sq P.tauTwo_sq P.tauOne_tauTwo (by norm_num) P.tau_rank)
      P.tau_rank
  have ho1 : BabyOrbit 1 alphaB tauOne :=
    babyInv_three_of_rank_2158 (orderOf_mul_eq_two (by rw [← sq]; exact P.alpha_sq) P.tauOne_sq
      P.tauOne_alpha.symm (by norm_num) L.rk_at) L.rk_at
  have ho2 : BabyOrbit 2 tauOne sThree := orderOf_eq_prime L.w3_cube L.w3_ne
  have ho3 : BabyOrbit 3 tauOne sFour := by
    have hsq : (tauOne * sFour) ^ 2 = tauOne * sFour * (tauOne * sFour) := sq _
    refine ⟨orderOf_eq_prime_pow (p := 2) (n := 1) (by rw [pow_one, hsq]; exact L.w4_sq_ne)
      (by norm_num; exact L.w4_pow), ?_⟩
    rw [hsq]
    refine CFSG.Monster.Existence.babyInv_one_of_rank_2048 (hord2 ?_ (by norm_num) L.w4_rk) L.w4_rk
    rw [← hsq, ← pow_add]
    exact L.w4_pow
  have hv : ∀ k : Fin 4, ∀ N : ℕ, N * babyOrbitSize k = babyCentOrder 0 →
      N.factorization 7 = if k = 1 then 2 else 1 := factorization_stab_seven
  have hsep : rk (tauOne * xSeven) ≠ rk (alphaB * xSeven) := by rw [L.rk_tx, L.rk_ax]; norm_num
  refine centralizer_le_of_witnesses hT3 hT4 hα hx P.alpha_x (fun k => ?_)
  fin_cases k
  · exact orbitWitness_cyclic hT4 hτ₁ hτ₂ ho0 (fun N hN => hv 0 N hN) hx P.tauOne_x.symm
      P.tauTwo_x.symm hsep
  · refine orbitWitness_pair hT4 hα hτ₁ ho1 (fun N hN => hv 1 N hN) P.x_pow P.x_ne L.f_pow
      L.f_x.symm L.f_ne_pow P.alpha_x.symm P.tauOne_x.symm L.f_a L.f_t
      (Or.inl (by rw [L.rk_line.1, L.rk_ax]; norm_num)) (fun j hj => ?_)
    obtain ⟨-, l1, l2, l3, l4, l5, l6⟩ := L.rk_line
    interval_cases j
    · right; rw [pow_zero, mul_one]; exact hsep
    · right; rw [pow_one, l1, L.rk_ax]; norm_num
    · right; rw [l2, L.rk_ax]; norm_num
    · left; rw [l3, L.rk_ax]; norm_num
    · right; rw [l4, L.rk_ax]; norm_num
    · left; rw [l5, L.rk_ax]; norm_num
    · left; rw [l6, L.rk_ax]; norm_num
  · exact orbitWitness_cyclic hT4 hτ₁ hs₃ ho2 (fun N hN => hv 2 N hN) hx P.tauOne_x.symm
      L.s3_x.symm hsep
  · exact orbitWitness_cyclic hT4 hτ₁ hs₄ ho3 (fun N hN => hv 3 N hN) hx P.tauOne_x.symm
      L.s4_x.symm hsep

theorem uQ_facts :
    Nat.card (Subgroup.closure ({uOne, uTwo} : Set NativeSporadic.B)) = 3 ^ 2 ∧
      Subgroup.closure ({uOne, uTwo} : Set NativeSporadic.B) ≤
        centralizer ({xSeven} : Set NativeSporadic.B) ∧
      ∀ q ∈ Subgroup.closure ({uOne, uTwo} : Set NativeSporadic.B), q ≠ 1 → rk q = 2862 := by
  have L := localParts_of_certificate
  have hp : Nat.Prime 3 := Nat.prime_three
  have h3 : Fact (Nat.Prime 3) := ⟨hp⟩
  have hu1o : orderOf uOne = 3 := orderOf_eq_prime L.u1_pow L.u1_ne
  have hfx : uTwo ∉ zpowers uOne := by
    intro hmem
    obtain ⟨i, hi, hfi⟩ := exists_pow_of_mem_zpowers_of_order (by norm_num) hu1o hmem
    exact L.u2_ne_pow i hi hfi
  obtain ⟨hmem, hcard⟩ := @closure_pair NativeSporadic.B Units.instGroup 3 hp uOne uTwo L.u1_u2
    L.u1_pow L.u2_pow L.u1_ne hfx
  refine ⟨hcard, ?_, ?_⟩
  · rw [closure_le]
    rintro g (rfl | rfl)
    · exact (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 L.u1_x
    · exact (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 L.u2_x
  · intro q hq hq1
    obtain ⟨a, b, ha, hb, rfl⟩ := hmem q hq
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h
      simp only [not_or, ne_eq, not_not] at h
      rw [h.1, h.2, pow_zero, pow_zero, one_mul] at hq1
      exact hq1 rfl
    obtain ⟨m, hm0, hm3, hline⟩ := @exists_line NativeSporadic.B Units.instGroup 3 hp uOne uTwo
      L.u1_u2 L.u1_pow L.u2_pow a b ha hb hab
    have hm : ¬ 3 ∣ m := fun h => absurd (Nat.le_of_dvd hm0 h) (by omega)
    have h11 : (1 : NativeSporadic.B) * 1 = 1 := one_mul 1
    have hrk : ∀ e : NativeSporadic.B, e ^ 3 = 1 → rk (e ^ m) = rk e := fun e he => by
      have := rk_mul_pow_eq hp (by norm_num) h11 he (by rw [one_mul, mul_one]) hm
      rwa [one_mul, one_mul] at this
    obtain ⟨-, r2, r12, r122⟩ := L.rk_q
    rcases hline with h | ⟨j, hj, h⟩
    · rw [h, hrk uTwo L.u2_pow, r2]
    · rw [h, hrk _ (@line_pow NativeSporadic.B Units.instGroup 3 uOne uTwo j L.u1_u2 L.u1_pow
        L.u2_pow)]
      interval_cases j
      · rw [pow_zero, mul_one]; exact L.rk_q.1
      · rw [pow_one]; exact r12
      · exact r122

theorem card_centralizer_seven_three (x : NativeSporadic.B) (hx : orderOf x = 7) :
    (Nat.card (centralizer ({x} : Set NativeSporadic.B))).factorization 3 = 2 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have P := bSevenElem_parts
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hα : BabyInv 0 alphaB :=
    babyInv_zero_of_rank_1860 (orderOf_eq_prime P.alpha_sq P.alpha_ne) P.alpha_rank
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  rw [CFSG.Monster.Existence.natCard_centralizer_eq_of_isConj (bSeven_isConj hx hxS)]
  obtain ⟨hQ, hQle, -⟩ := uQ_facts
  have h9 : 3 ^ 2 ∣ Nat.card (centralizer ({xSeven} : Set NativeSporadic.B)) :=
    hQ ▸ Subgroup.card_dvd_of_le hQle
  have h27 := not_dvd_27_card_centralizer CFSG.Monster.Existence.babyTableIII hα hxS
    centralizer_xSeven_le
  exact factorization_eq_of_dvd Nat.prime_three Nat.card_pos.ne' h9 (by norm_num; exact h27)

theorem bThreeB_seven_free :
    ¬ 7 ∣ Nat.card (centralizer ({phiB (t3 1)} : Set NativeSporadic.B)) := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have P := bSevenElem_parts
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  obtain ⟨hrk1, hord1⟩ := rk_phiB_t3_one
  intro hdvd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer ({phiB (t3 1)} : Set NativeSporadic.B))) 7 hdvd
  have hz' : orderOf (z : NativeSporadic.B) = 7 := by rw [Subgroup.orderOf_coe]; exact hz
  have hzr : (z : NativeSporadic.B) * phiB (t3 1) = phiB (t3 1) * z :=
    (mem_centralizer_singleton_iff (G := NativeSporadic.B)).1 z.2
  obtain ⟨c, hc⟩ := isConj_iff.1 (bSeven_isConj hz' hxS)
  set u := c * phiB (t3 1) * c⁻¹ with hu
  have huC : u ∈ centralizer ({xSeven} : Set NativeSporadic.B) := by
    refine (mem_centralizer_singleton_iff (G := NativeSporadic.B)).2 ?_
    rw [← hc, hu]
    calc c * phiB (t3 1) * c⁻¹ * (c * z * c⁻¹) = c * (phiB (t3 1) * z) * c⁻¹ := by group
      _ = c * (z * phiB (t3 1)) * c⁻¹ := by rw [hzr]
      _ = c * z * c⁻¹ * (c * phiB (t3 1) * c⁻¹) := by group
  have hu3 : u ^ 3 = 1 := by
    have h := pow_orderOf_eq_one (phiB (t3 1))
    rw [hord1] at h
    rw [hu, conj_pow, h]
    group
  obtain ⟨hQ, hQle, hQrk⟩ := uQ_facts
  have hQcard : Nat.card (Subgroup.closure ({uOne, uTwo} : Set NativeSporadic.B)) =
      3 ^ (Nat.card (centralizer ({xSeven} : Set NativeSporadic.B))).factorization 3 := by
    rw [hQ, card_centralizer_seven_three xSeven hxS]
  obtain ⟨d, -, hdQ⟩ := @exists_conj_mem_of_card NativeSporadic.B Units.instGroup _ 3 _ _ _ hQle
    hQcard u huC hu3
  have hne : d * u * d⁻¹ ≠ 1 := by
    intro h1
    have hu1 : u = 1 := by
      have := congrArg (fun w => d⁻¹ * w * d) h1
      simpa [mul_assoc] using this
    have : phiB (t3 1) = 1 := by
      have := congrArg (fun w => c⁻¹ * w * c) hu1
      simpa [hu, mul_assoc] using this
    rw [this, orderOf_one] at hord1
    exact absurd hord1 (by norm_num)
  have h1 := hQrk _ hdQ hne
  rw [hu, show d * (c * phiB (t3 1) * c⁻¹) * d⁻¹ = (d * c) * phiB (t3 1) * (d * c)⁻¹ by group,
    rk_conj, hrk1] at h1
  exact absurd h1 (by norm_num)

end Main

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
