module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Base

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.Sporadic.Fi24 CFSG.HardMathSupport.Dickson.I271.Fi7
open scoped commutatorElement


theorem C7_commute_X7 : Commute C7 X7 := fi7_cube.2.2.2.1

theorem C7_commute_Y7 : Commute C7 Y7 := fi7_cube.2.2.2.2.1

theorem C7_pow_mul_X7 (a : ℕ) : C7 ^ a * X7 = X7 * C7 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc C7 ^ (a + 1) * X7 = C7 * (C7 ^ a * X7) := by rw [pow_succ']; group
      _ = C7 * (X7 * C7 ^ a) := by rw [ih]
      _ = (C7 * X7) * C7 ^ a := by group
      _ = (X7 * C7) * C7 ^ a := by rw [C7_commute_X7]
      _ = X7 * C7 ^ (a + 1) := by rw [pow_succ]; group

theorem C7_pow_mul_Y7 (a : ℕ) : C7 ^ a * Y7 = Y7 * C7 ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    calc C7 ^ (a + 1) * Y7 = C7 * (C7 ^ a * Y7) := by rw [pow_succ']; group
      _ = C7 * (Y7 * C7 ^ a) := by rw [ih]
      _ = (C7 * Y7) * C7 ^ a := by group
      _ = (Y7 * C7) * C7 ^ a := by rw [C7_commute_Y7]
      _ = Y7 * C7 ^ (a + 1) := by rw [pow_succ]; group

theorem C7_pow_mul_X7_pow (a b : ℕ) : C7 ^ a * X7 ^ b = X7 ^ b * C7 ^ a := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc C7 ^ a * X7 ^ (b + 1) = (C7 ^ a * X7 ^ b) * X7 := by rw [pow_succ]; group
      _ = (X7 ^ b * C7 ^ a) * X7 := by rw [ih]
      _ = X7 ^ b * (C7 ^ a * X7) := by group
      _ = X7 ^ b * (X7 * C7 ^ a) := by rw [C7_pow_mul_X7]
      _ = X7 ^ (b + 1) * C7 ^ a := by rw [pow_succ']; group

theorem C7_pow_mul_Y7_pow (a b : ℕ) : C7 ^ a * Y7 ^ b = Y7 ^ b * C7 ^ a := by
  induction b with
  | zero => simp
  | succ b ih =>
    calc C7 ^ a * Y7 ^ (b + 1) = (C7 ^ a * Y7 ^ b) * Y7 := by rw [pow_succ]; group
      _ = (Y7 ^ b * C7 ^ a) * Y7 := by rw [ih]
      _ = Y7 ^ b * (C7 ^ a * Y7) := by group
      _ = Y7 ^ b * (Y7 * C7 ^ a) := by rw [C7_pow_mul_Y7]
      _ = Y7 ^ (b + 1) * C7 ^ a := by rw [pow_succ']; group

theorem C7_pow_mul_X7_Y7_pow (a i j : ℕ) :
    C7 ^ a * (X7 ^ i * Y7 ^ j) = (X7 ^ i * Y7 ^ j) * C7 ^ a := by
  calc C7 ^ a * (X7 ^ i * Y7 ^ j) = (C7 ^ a * X7 ^ i) * Y7 ^ j := by group
    _ = (X7 ^ i * C7 ^ a) * Y7 ^ j := by rw [C7_pow_mul_X7_pow]
    _ = X7 ^ i * (C7 ^ a * Y7 ^ j) := by group
    _ = X7 ^ i * (Y7 ^ j * C7 ^ a) := by rw [C7_pow_mul_Y7_pow]
    _ = (X7 ^ i * Y7 ^ j) * C7 ^ a := by group

theorem Y7_mul_X7_pow (i : ℕ) :
    Y7 * X7 ^ i = X7 ^ i * Y7 * C7 ^ (6 * i) := by
  have h7 : ⁅X7, Y7⁆ ^ 7 = 1 := by rw [fi7_comm_xy, C7_pow_seven]
  have h := CFSG.SectionRank.LocalWitness.y_mul_x_pow (x := X7) (y := Y7) (r := 7)
    (by norm_num) fi7_commute_x fi7_commute_y h7 i
  simpa [fi7_comm_xy] using h

theorem Y7_pow_mul_X7_pow (i j : ℕ) :
    Y7 ^ j * X7 ^ i = X7 ^ i * Y7 ^ j * C7 ^ (6 * i * j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcy : C7 ^ (6 * i) * Y7 ^ j = Y7 ^ j * C7 ^ (6 * i) :=
      C7_pow_mul_Y7_pow (6 * i) j
    calc Y7 ^ (j + 1) * X7 ^ i = Y7 * (Y7 ^ j * X7 ^ i) := by rw [pow_succ']; group
      _ = Y7 * (X7 ^ i * Y7 ^ j * C7 ^ (6 * i * j)) := by rw [ih]
      _ = (Y7 * X7 ^ i) * Y7 ^ j * C7 ^ (6 * i * j) := by group
      _ = (X7 ^ i * Y7 * C7 ^ (6 * i)) * Y7 ^ j * C7 ^ (6 * i * j) := by rw [Y7_mul_X7_pow]
      _ = X7 ^ i * Y7 * (C7 ^ (6 * i) * Y7 ^ j) * C7 ^ (6 * i * j) := by group
      _ = X7 ^ i * Y7 * (Y7 ^ j * C7 ^ (6 * i)) * C7 ^ (6 * i * j) := by rw [hcy]
      _ = X7 ^ i * (Y7 * Y7 ^ j) * (C7 ^ (6 * i) * C7 ^ (6 * i * j)) := by group
      _ = X7 ^ i * Y7 ^ (j + 1) * C7 ^ (6 * i * (j + 1)) := by
        rw [← pow_succ', ← pow_add, show 6 * i + 6 * i * j = 6 * i * (j + 1) by ring]

theorem pow_mul_pow_X7_Y7 (i j n : ℕ) :
    ∃ K : ℕ, (X7 ^ i * Y7 ^ j) ^ n = X7 ^ (i * n) * Y7 ^ (j * n) * C7 ^ K := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨K, hK⟩ := ih
    refine ⟨K + 6 * i * j * n, ?_⟩
    have hcomm : C7 ^ K * (X7 ^ i * Y7 ^ j) = (X7 ^ i * Y7 ^ j) * C7 ^ K :=
      C7_pow_mul_X7_Y7_pow K i j
    have hcy : C7 ^ (6 * i * (j * n)) * Y7 ^ j = Y7 ^ j * C7 ^ (6 * i * (j * n)) :=
      C7_pow_mul_Y7_pow (6 * i * (j * n)) j
    calc (X7 ^ i * Y7 ^ j) ^ (n + 1) =
          (X7 ^ i * Y7 ^ j) ^ n * (X7 ^ i * Y7 ^ j) := by rw [pow_succ]
      _ = (X7 ^ (i * n) * Y7 ^ (j * n) * C7 ^ K) * (X7 ^ i * Y7 ^ j) := by rw [hK]
      _ = X7 ^ (i * n) * Y7 ^ (j * n) * (C7 ^ K * (X7 ^ i * Y7 ^ j)) := by group
      _ = X7 ^ (i * n) * Y7 ^ (j * n) * ((X7 ^ i * Y7 ^ j) * C7 ^ K) := by rw [hcomm]
      _ = X7 ^ (i * n) * (Y7 ^ (j * n) * X7 ^ i) * Y7 ^ j * C7 ^ K := by group
      _ = X7 ^ (i * n) * (X7 ^ i * Y7 ^ (j * n) * C7 ^ (6 * i * (j * n))) *
            Y7 ^ j * C7 ^ K := by rw [Y7_pow_mul_X7_pow]
      _ = X7 ^ (i * n) * X7 ^ i * Y7 ^ (j * n) *
            (C7 ^ (6 * i * (j * n)) * Y7 ^ j) * C7 ^ K := by group
      _ = X7 ^ (i * n) * X7 ^ i * Y7 ^ (j * n) *
            (Y7 ^ j * C7 ^ (6 * i * (j * n))) * C7 ^ K := by rw [hcy]
      _ = X7 ^ (i * n) * X7 ^ i * (Y7 ^ (j * n) * Y7 ^ j) *
            (C7 ^ (6 * i * (j * n)) * C7 ^ K) := by group
      _ = X7 ^ (i * (n + 1)) * Y7 ^ (j * (n + 1)) * C7 ^ (K + 6 * i * j * n) := by
        rw [← pow_add, ← pow_add, ← pow_add,
          show i * n + i = i * (n + 1) by ring,
          show j * n + j = j * (n + 1) by ring,
          show 6 * i * (j * n) + K = K + 6 * i * j * n by ring]

theorem pow_mul_pow_mul_pow_X7_Y7 (i j k n : ℕ) :
    ∃ K : ℕ, (X7 ^ i * Y7 ^ j * C7 ^ k) ^ n =
      X7 ^ (i * n) * Y7 ^ (j * n) * C7 ^ K := by
  obtain ⟨K, hK⟩ := pow_mul_pow_X7_Y7 i j n
  refine ⟨K + k * n, ?_⟩
  have hsplit : ∀ m : ℕ, (X7 ^ i * Y7 ^ j * C7 ^ k) ^ m =
      (X7 ^ i * Y7 ^ j) ^ m * (C7 ^ k) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hCA : C7 ^ (k * m) * (X7 ^ i * Y7 ^ j) =
          (X7 ^ i * Y7 ^ j) * C7 ^ (k * m) := C7_pow_mul_X7_Y7_pow (k * m) i j
      calc (X7 ^ i * Y7 ^ j * C7 ^ k) ^ (m + 1) =
            (X7 ^ i * Y7 ^ j * C7 ^ k) ^ m * (X7 ^ i * Y7 ^ j * C7 ^ k) := by
              rw [pow_succ]
        _ = ((X7 ^ i * Y7 ^ j) ^ m * (C7 ^ k) ^ m) *
              (X7 ^ i * Y7 ^ j * C7 ^ k) := by rw [ih]
        _ = (X7 ^ i * Y7 ^ j) ^ m * (((C7 ^ k) ^ m * (X7 ^ i * Y7 ^ j)) * C7 ^ k) := by
              group
        _ = (X7 ^ i * Y7 ^ j) ^ m * ((C7 ^ (k * m) * (X7 ^ i * Y7 ^ j)) * C7 ^ k) := by
              rw [pow_mul]
        _ = (X7 ^ i * Y7 ^ j) ^ m * (((X7 ^ i * Y7 ^ j) * C7 ^ (k * m)) * C7 ^ k) := by
              rw [hCA]
        _ = (X7 ^ i * Y7 ^ j) ^ (m + 1) * (C7 ^ k) ^ (m + 1) := by
              rw [pow_succ, pow_succ, pow_mul]
              group
  calc (X7 ^ i * Y7 ^ j * C7 ^ k) ^ n
      = ((X7 ^ i * Y7 ^ j) * C7 ^ k) ^ n := by rfl
    _ = (X7 ^ i * Y7 ^ j) ^ n * (C7 ^ k) ^ n := hsplit n
    _ = (X7 ^ (i * n) * Y7 ^ (j * n) * C7 ^ K) * C7 ^ (k * n) := by rw [hK, ← pow_mul]
    _ = X7 ^ (i * n) * Y7 ^ (j * n) * (C7 ^ K * C7 ^ (k * n)) := by group
    _ = X7 ^ (i * n) * Y7 ^ (j * n) * C7 ^ (K + k * n) := by rw [← pow_add]

theorem plane_cases {E : Subgroup J} (hEQ : E ≤ Q7) (hEc : Nat.card E = 7 ^ 2) :
    C7 ∈ E ∧ (Y7 ∈ E ∨ ∃ lam < 7, X7 * Y7 ^ lam ∈ E) := by
  have hfact : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hx7, hy7, -, -, -, -⟩ := fi7_cube
  have hcE : C7 ∈ E := by
    set E' : Subgroup Q7 := E.subgroupOf Q7 with hE'def
    have hcardE' : Nat.card E' = 7 ^ 2 := by
      rw [hE'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv, hEc]
    have hidx : E'.index = 7 := by
      have h1 := Subgroup.card_mul_index E'
      rw [hcardE', card_Q7] at h1
      omega
    have hmin : (Nat.card Q7).minFac = 7 := by
      rw [card_Q7]
      exact Nat.Prime.pow_minFac (by norm_num) (by norm_num)
    haveI hE'normal : E'.Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
    have hE'ne : E' ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card E' = 1 := by rw [hbot]; simp
      rw [hcardE'] at h1
      norm_num at h1
    haveI hQp : IsPGroup 7 Q7 := IsPGroup.of_card (n := 3) (by rw [card_Q7])
    haveI : Group.IsNilpotent Q7 := hQp.isNilpotent
    have hcenter : E' ⊓ Subgroup.center Q7 ≠ ⊥ :=
      Group.IsNilpotent.inf_center_ne_bot_of_normal hE'ne
    have hlt : ⊥ < E' ⊓ Subgroup.center Q7 := bot_lt_iff_ne_bot.mpr hcenter
    obtain ⟨x, hxN, hxbot⟩ := SetLike.exists_of_lt hlt
    have hx1 : x ≠ 1 := fun h1 => hxbot (by rw [h1]; exact Subgroup.one_mem _)
    have hxE : (x : J) ∈ E := Subgroup.mem_subgroupOf.mp hxN.1
    have hxZ : (x : J) ∈ Subgroup.zpowers C7 := by
      refine Q7_center x x.2 ?_
      intro q hq
      have h := Subgroup.mem_center_iff.mp hxN.2 ⟨q, hq⟩
      simpa using (congrArg Subtype.val h).symm
    have hxpow : (x : J) ^ 7 = 1 := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxZ
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, C7_pow_seven,
        one_zpow]
    have hx1J : (x : J) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxord : orderOf (x : J) = 7 := orderOf_eq_prime hxpow hx1J
    have hzpow : Subgroup.zpowers (x : J) = Subgroup.zpowers C7 := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxZ) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hxord, orderOf_C7]
    have hxgen : C7 ∈ Subgroup.zpowers (x : J) := hzpow ▸ Subgroup.mem_zpowers C7
    exact (Subgroup.zpowers_le.mpr hxE) hxgen
  refine ⟨hcE, ?_⟩
  obtain ⟨e, heE, heZ⟩ :=
    CFSG.HardMathSupport.Dickson.I271.exists_not_mem_zpowers_of_card (X := J) (p := 7)
      (w := C7) orderOf_C7 (E := E) hEc
  obtain ⟨i, j, k, hi, hj, hk, heq⟩ :=
    CFSG.SectionRank.LocalWitness.mem_closure_normalForm (x := X7) (y := Y7) (r := 7)
      (by norm_num) hx7 hy7 fi7_commute_x fi7_commute_y (hEQ heE)
  rw [fi7_comm_xy] at heq
  by_cases hi0 : i = 0
  ·
    left
    have heq' : e = Y7 ^ j * C7 ^ k := by simpa [hi0] using heq
    have hjc : Y7 ^ j * C7 ^ k ∈ E := by simpa [heq'] using heE
    have hckE : C7 ^ k ∈ E := E.pow_mem hcE k
    have hYjE : Y7 ^ j ∈ E := by
      have h : Y7 ^ j = (Y7 ^ j * C7 ^ k) * (C7 ^ k)⁻¹ := by group
      rw [h]
      exact E.mul_mem hjc (E.inv_mem hckE)
    have hj0 : j ≠ 0 := by
      intro hj0
      apply heZ
      rw [heq, hi0, hj0]
      simpa using Subgroup.pow_mem (Subgroup.mem_zpowers C7) k
    have hcop : Nat.Coprime j 7 := by
      have hjn : ¬ 7 ∣ j := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hj]
        omega
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hjn)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num : 1 < 7)
    have hY : Y7 = (Y7 ^ j) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (j * m) hy7, hm, pow_one]
    rw [hY]
    exact E.pow_mem hYjE m
  ·
    right
    have himod : ¬ 7 ∣ i := by
      rw [Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hi]
      omega
    have hcopi : Nat.Coprime i 7 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr himod)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcopi (by norm_num : 1 < 7)
    refine ⟨(j * m) % 7, Nat.mod_lt _ (by norm_num), ?_⟩
    obtain ⟨K, hK⟩ := pow_mul_pow_mul_pow_X7_Y7 i j k m
    have hK' : e ^ m = X7 ^ (i * m) * Y7 ^ (j * m) * C7 ^ K := by
      rw [heq]
      exact hK
    have hXm : X7 ^ (i * m) = X7 := by
      rw [pow_eq_pow_mod (i * m) hx7, hm, pow_one]
    have hYm : Y7 ^ (j * m) = Y7 ^ ((j * m) % 7) := pow_eq_pow_mod (j * m) hy7
    have hEm : X7 * Y7 ^ ((j * m) % 7) * C7 ^ K ∈ E := by
      rw [← hXm, ← hYm, ← hK']
      exact E.pow_mem heE m
    have hcKE : C7 ^ K ∈ E := E.pow_mem hcE K
    have h : X7 * Y7 ^ ((j * m) % 7) =
        (X7 * Y7 ^ ((j * m) % 7) * C7 ^ K) * (C7 ^ K)⁻¹ := by group
    rw [h]
    exact E.mul_mem hEm (E.inv_mem hcKE)

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K
