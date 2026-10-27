module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I112Ctx
public import CFSG.LocalAnalysis.GLTheoremA.PartI.ExcBridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.HardMathSupport.Solomon.Coordinator.SporOrders
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.ScopeBInputs
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TCAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator.I1420
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.LocalAnalysis.GLTheoremA.S10

section Arithmetic

private theorem two_pow_mod_nine_eq (b : ℕ) : 2 ^ b % 9 = 2 ^ (b % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod b 6, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

private theorem even_of_two_pow_mod_nine {b : ℕ} (h : 2 ^ b % 9 = 4 ∨ 2 ^ b % 9 = 7) :
    b % 2 = 0 := by
  rw [two_pow_mod_nine_eq] at h
  obtain ⟨r, hr⟩ : ∃ r, b % 6 = r := ⟨_, rfl⟩
  rw [hr] at h
  have hr6 : r < 6 := by omega
  have hb : b % 2 = r % 2 := by omega
  rw [hb]
  interval_cases r <;> simp_all

private theorem two_pow_mod_nine_of_six_dvd {b : ℕ} (h : b % 6 = 0) : 2 ^ b % 9 = 1 := by
  rw [two_pow_mod_nine_eq, h]
  norm_num

private theorem orderTwistedA_two_part {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) :
    ∃ A, Odd A ∧ orderTwistedA r (2 ^ m) = 2 ^ (m * (r * (r + 1) / 2)) * A := by
  have h2m : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨A, hA⟩ := CatDistinct.gcd_dvd_twP hr h2m
  have hg : 0 < Nat.gcd (r + 1) (2 ^ m + 1) := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos r)
  refine ⟨A, ?_, ?_⟩
  · have h := CatDistinct.odd_twP (r := r) hm
    rw [hA] at h
    exact (Nat.odd_mul.1 h).2
  · apply Nat.eq_of_mul_eq_mul_right hg
    rw [CatDistinct.orderTwistedA_mul_gcd hr hm, hA]
    ring

private theorem orderA_two_two_part {b : ℕ} (hb : 1 ≤ b) :
    ∃ A, Odd A ∧ orderA 2 (2 ^ b) = 2 ^ (b * 3) * A := by
  have hmul := CatDistinct.orderA_two_mul_gcd (2 ^ b)
  have h1 := Nat.sub_dvd_pow_sub_pow (2 ^ b) 1 3
  rw [one_pow] at h1
  have hdvd : Nat.gcd 3 (2 ^ b - 1) ∣ ((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 - 1) :=
    ((Nat.gcd_dvd_right 3 (2 ^ b - 1)).trans h1).trans (dvd_mul_left _ _)
  obtain ⟨A, hA⟩ := hdvd
  have hodd : Odd A := by
    have h := (CatDistinct.odd_pow_two_pow_sub_one (a := b) (j := 2) hb (by norm_num)).mul
      (CatDistinct.odd_pow_two_pow_sub_one (a := b) (j := 3) hb (by norm_num))
    rw [hA] at h
    exact (Nat.odd_mul.1 h).2
  refine ⟨A, hodd, ?_⟩
  apply Nat.eq_of_mul_eq_mul_right (Nat.gcd_pos_of_pos_left _ (by norm_num : 0 < 3))
  rw [hmul, hA, pow_mul]
  ring

private def e6P (q : ℕ) : ℕ :=
  (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)

private theorem orderTwistedE6_eq (q : ℕ) :
    orderTwistedE6 q = q ^ 36 * e6P q / Nat.gcd 3 (q + 1) := by
  simp only [orderTwistedE6, e6P, mul_assoc]

private theorem e6P_odd {m : ℕ} (hm : 1 ≤ m) : Odd (e6P (2 ^ m)) := by
  unfold e6P
  have h12 := CatDistinct.odd_pow_two_pow_sub_one (a := m) (j := 12) hm (by norm_num)
  have h9 := CatDistinct.odd_pow_two_pow_add_one (a := m) (j := 9) hm (by norm_num)
  have h8 := CatDistinct.odd_pow_two_pow_sub_one (a := m) (j := 8) hm (by norm_num)
  have h6 := CatDistinct.odd_pow_two_pow_sub_one (a := m) (j := 6) hm (by norm_num)
  have h5 := CatDistinct.odd_pow_two_pow_add_one (a := m) (j := 5) hm (by norm_num)
  have h2 := CatDistinct.odd_pow_two_pow_sub_one (a := m) (j := 2) hm (by norm_num)
  exact (((((h12.mul h9).mul h8).mul h6).mul h5).mul h2)

private theorem orderTwistedE6_two_part {m : ℕ} (hm : 1 ≤ m) :
    ∃ A, Odd A ∧ orderTwistedE6 (2 ^ m) = 2 ^ (m * 36) * A := by
  have hg : 0 < Nat.gcd 3 (2 ^ m + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h9 : Nat.gcd 3 (2 ^ m + 1) ∣ (2 ^ m) ^ 9 + 1 := by
    have h := Odd.nat_add_dvd_pow_add_pow (2 ^ m) 1 (by decide : Odd 9)
    rw [one_pow] at h
    exact (Nat.gcd_dvd_right 3 (2 ^ m + 1)).trans h
  have hgP : Nat.gcd 3 (2 ^ m + 1) ∣ e6P (2 ^ m) := by
    unfold e6P
    exact ((((Dvd.dvd.mul_left h9 _).mul_right _).mul_right _).mul_right _).mul_right _
  obtain ⟨A, hA⟩ := hgP
  have hodd : Odd A := by
    have h := e6P_odd hm
    rw [hA] at h
    exact (Nat.odd_mul.1 h).2
  refine ⟨A, hodd, ?_⟩
  rw [orderTwistedE6_eq, hA,
    show (2 ^ m) ^ 36 * (Nat.gcd 3 (2 ^ m + 1) * A) = Nat.gcd 3 (2 ^ m + 1) * ((2 ^ m) ^ 36 * A) by ring,
    Nat.mul_div_cancel_left _ hg, ← pow_mul]

private theorem e6P_le {q : ℕ} (hq : 1 ≤ q) : e6P q ≤ 4 * q ^ 42 := by
  unfold e6P
  have h9 : 1 ≤ q ^ 9 := Nat.one_le_pow _ _ hq
  have h5 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ hq
  have a12 : q ^ 12 - 1 ≤ q ^ 12 := Nat.sub_le _ _
  have a9 : q ^ 9 + 1 ≤ 2 * q ^ 9 := by omega
  have a8 : q ^ 8 - 1 ≤ q ^ 8 := Nat.sub_le _ _
  have a6 : q ^ 6 - 1 ≤ q ^ 6 := Nat.sub_le _ _
  have a5 : q ^ 5 + 1 ≤ 2 * q ^ 5 := by omega
  have a2 : q ^ 2 - 1 ≤ q ^ 2 := Nat.sub_le _ _
  calc (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) * (q ^ 5 + 1) * (q ^ 2 - 1)
      ≤ q ^ 12 * (2 * q ^ 9) * q ^ 8 * q ^ 6 * (2 * q ^ 5) * q ^ 2 := by gcongr
    _ = 4 * q ^ 42 := by ring

private theorem orderTwistedE6_le {q : ℕ} (hq : 1 ≤ q) :
    orderTwistedE6 q ≤ q ^ 36 * (4 * q ^ 42) := by
  rw [orderTwistedE6_eq]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (e6P_le hq))

private theorem twP5_le {x : ℕ} (hx : 1 ≤ x) :
    (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1) ≤ 4 * x ^ 20 := by
  have h3 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have h5 : 1 ≤ x ^ 5 := Nat.one_le_pow _ _ hx
  have a2 : x ^ 2 - 1 ≤ x ^ 2 := Nat.sub_le _ _
  have a3 : x ^ 3 + 1 ≤ 2 * x ^ 3 := by omega
  have a4 : x ^ 4 - 1 ≤ x ^ 4 := Nat.sub_le _ _
  have a5 : x ^ 5 + 1 ≤ 2 * x ^ 5 := by omega
  have a6 : x ^ 6 - 1 ≤ x ^ 6 := Nat.sub_le _ _
  calc (x ^ 2 - 1) * (x ^ 3 + 1) * (x ^ 4 - 1) * (x ^ 5 + 1) * (x ^ 6 - 1)
      ≤ x ^ 2 * (2 * x ^ 3) * x ^ 4 * (2 * x ^ 5) * x ^ 6 := by gcongr
    _ = 4 * x ^ 20 := by ring

private theorem twP2_ge {Q : ℕ} (hQ : 2 ≤ Q) : Q ^ 5 ≤ 2 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
  have hQ2 : 2 ≤ Q ^ 2 := by nlinarith
  have h1 : Q ^ 2 ≤ 2 * (Q ^ 2 - 1) := by omega
  calc Q ^ 5 = Q ^ 2 * Q ^ 3 := by ring
    _ ≤ 2 * (Q ^ 2 - 1) * Q ^ 3 := Nat.mul_le_mul_right _ h1
    _ ≤ 2 * ((Q ^ 2 - 1) * (Q ^ 3 + 1)) := by
        rw [mul_assoc]
        exact Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (le_refl _) (Nat.le_add_right _ _))

private theorem exp_eq_of_two_pow_mul {u v A B : ℕ} (hA : Odd A) (hB : Odd B)
    (h : 2 ^ u * A = 2 ^ v * B) : u = v :=
  (CatDistinct.two_pow_mul_odd_inj hA hB h).1

private theorem e6_ne_L2 {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : orderTwistedE6 (2 ^ n) = orderA 1 (2 ^ m)) : False := by
  obtain ⟨A, hA, hO⟩ := orderTwistedE6_two_part (m := n) hn
  have hB := CatDistinct.orderA_one_eq hm
  have hBodd : Odd ((2 ^ m) ^ 2 - 1) :=
    CatDistinct.odd_pow_two_pow_sub_one (a := m) (j := 2) hm (by norm_num)
  have hle := orderTwistedE6_le (q := 2 ^ n) Nat.one_le_two_pow
  rw [hO, hB] at h
  obtain ⟨hmn, hAB⟩ := CatDistinct.two_pow_mul_odd_inj hA hBodd h
  rw [hO, ← pow_mul, ← pow_mul] at hle
  have hA4 : A ≤ 4 * 2 ^ (n * 42) := Nat.le_of_mul_le_mul_left hle (by positivity)
  subst hmn
  have hsq : (2 ^ (n * 36)) ^ 2 = 2 ^ (n * 72) := by
    rw [← pow_mul]
    congr 1
    ring
  have hy : 1 ≤ 2 ^ (n * 42) := Nat.one_le_two_pow
  have hX : 8 * 2 ^ (n * 42) ≤ 2 ^ (n * 72) := by
    have h30 : 8 ≤ 2 ^ (n * 30) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n * 30) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have e : 2 ^ (n * 72) = 2 ^ (n * 42) * 2 ^ (n * 30) := by
      rw [← pow_add]
      congr 1
      ring
    rw [e]
    calc 8 * 2 ^ (n * 42) ≤ 2 ^ (n * 30) * 2 ^ (n * 42) := Nat.mul_le_mul_right _ h30
      _ = 2 ^ (n * 42) * 2 ^ (n * 30) := mul_comm _ _
  rw [hAB, hsq] at hA4
  omega

private theorem e6_ne_60 {n : ℕ} (hn : 1 ≤ n) (h : orderTwistedE6 (2 ^ n) = 60) : False := by
  obtain ⟨A, hA, hO⟩ := orderTwistedE6_two_part (m := n) hn
  rw [hO] at h
  have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 15) (h.trans (by norm_num : (60 : ℕ) = 2 ^ 2 * 15))
  omega

private theorem u3_ne_u6 {n b : ℕ} (hn : 3 ≤ n) (hbn : b = 5 * n)
    (h : orderTwistedA 2 (2 ^ b) = orderTwistedA 5 (2 ^ n)) : False := by
  have hb1 : 1 ≤ b := by omega
  have hm2 := CatDistinct.orderTwistedA_mul_gcd (r := 2) (m := b) (by norm_num) hb1
  have hm5 := CatDistinct.orderTwistedA_mul_gcd (r := 5) (m := n) (by norm_num) (by omega)
  rw [h, CatDistinct.twP_two] at hm2
  rw [CatDistinct.twP_five] at hm5
  norm_num at hm2 hm5
  have hb3 : 2 ^ (b * 3) = 2 ^ (n * 15) := by
    congr 1
    omega
  rw [hb3] at hm2
  have hx1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hx : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have key : 2 ^ (n * 15) * ((((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) * Nat.gcd 6 (2 ^ n + 1))
      = 2 ^ (n * 15) * ((((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 6 - 1)) * Nat.gcd 3 (2 ^ b + 1)) := by
    calc 2 ^ (n * 15) * ((((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)) * Nat.gcd 6 (2 ^ n + 1))
        = (orderTwistedA 5 (2 ^ n) * Nat.gcd 3 (2 ^ b + 1)) * Nat.gcd 6 (2 ^ n + 1) := by
          rw [hm2]; ring
      _ = (orderTwistedA 5 (2 ^ n) * Nat.gcd 6 (2 ^ n + 1)) * Nat.gcd 3 (2 ^ b + 1) := by ring
      _ = _ := by rw [hm5]; ring
  have key' := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ (n * 15)) key
  have hg6 : 0 < Nat.gcd 6 (2 ^ n + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd 3 (2 ^ b + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hP : ((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) ≤
      3 * ((((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 6 - 1))) := by
    calc ((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1)
        ≤ ((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 3 + 1) * Nat.gcd 6 (2 ^ n + 1) :=
          Nat.le_mul_of_pos_right _ hg6
      _ = (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 6 - 1)) * Nat.gcd 3 (2 ^ b + 1) := by
          exact key'
      _ ≤ (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 6 - 1)) * 3 := Nat.mul_le_mul_left _ hg3
      _ = 3 * ((((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 4 - 1) *
          ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 6 - 1))) := by ring
  have hbound2 : 2 ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have hP3 := twP2_ge hbound2
  have hP6 := twP5_le hx1
  have hz : 32768 ≤ (2 ^ n) ^ 5 := by
    calc 32768 = 8 ^ 5 := by norm_num
      _ ≤ (2 ^ n) ^ 5 := Nat.pow_le_pow_left hx 5
  have hQx : 2 ^ b = (2 ^ n) ^ 5 := by rw [hbn, mul_comm, pow_mul]
  have e : (2 ^ b) ^ 5 = (2 ^ n) ^ 20 * (2 ^ n) ^ 5 := by
    rw [hQx]
    ring
  have hy : 1 ≤ (2 ^ n) ^ 20 := Nat.one_le_pow _ _ hx1
  have h1 : (2 ^ n) ^ 20 * 32768 ≤ (2 ^ n) ^ 20 * (2 ^ n) ^ 5 := Nat.mul_le_mul_left _ hz
  nlinarith [hP3, hP, hP6, e, h1, hy]

end Arithmetic

private theorem valid_A_one_two_pow (n : ℕ) (hn : Odd n) (hn1 : 1 < n) (hpos : 0 < n) :
    (TauCeti.LieTypeIndex.A 1 ⟨2, n, Nat.prime_two, hpos⟩).Valid := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
    TauCeti.LieTypeIndex.isDuplicateRepresentative_iff, TauCeti.PrimePower.card_def]
  have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  omega

private theorem isUrn_of_isU6n {n : ℕ} {i : TauCeti.CFSGIndex} (h : S10.isU6n n i) :
    S10.isUrn n i := by
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at h
  | alternating k hk => simp [S10.isU6n, onLie] at h
  | sporadic s => simp [S10.isU6n, onLie] at h
  | lie j =>
    obtain ⟨d, hv⟩ := j
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S10.isU6n, S10.isUrn, onLie] at h ⊢
      exact h
    | _ => simp [S10.isU6n, onLie] at h

private theorem data_isTE6n {S : Type} [Group S] [Finite S] (hc : CatDistinct.Ctx) {m : ℕ}
    (h : catalogIs S (S10.isTE6n m)) :
    1 ≤ m ∧ Nat.card S = orderTwistedE6 (2 ^ m) ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (S ≃* d.Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isTE6n, onLie] at hi
  | alternating k hk => simp [S10.isTE6n, onLie] at hi
  | sporadic s => simp [S10.isTE6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedE6 q =>
      simp only [S10.isTE6n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      refine ⟨by have := q.exponent_pos; omega, ?_, ⟨⟨.twistedE6 q, hv⟩, by simp [hp], ⟨e⟩⟩⟩
      rw [hc.bridge ⟨.twistedE6 q, hv⟩ S ⟨e⟩]
      show orderTwistedE6 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [S10.isTE6n, onLie] at hi

private theorem data_isU6n' {S : Type} [Group S] [Finite S] (hc : CatDistinct.Ctx) {m : ℕ}
    (h : catalogIs S (S10.isU6n m)) :
    1 ≤ m ∧ Nat.card S = orderTwistedA 5 (2 ^ m) ∧
      ∃ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 ∧ Nonempty (S ≃* d.Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [S10.isU6n, onLie] at hi
  | alternating k hk => simp [S10.isU6n, onLie] at hi
  | sporadic s => simp [S10.isU6n, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | _ | r <;> simp [S10.isU6n, onLie] at hi
      obtain ⟨hp, hn⟩ := hi
      refine ⟨by have := q.exponent_pos; omega, ?_, ⟨⟨.twistedA 5 q, hv⟩, by simp [hp], ⟨e⟩⟩⟩
      rw [hc.bridge ⟨.twistedA 5 q, hv⟩ S ⟨e⟩]
      show orderTwistedA 5 q.card = _
      rw [TauCeti.PrimePower.card_def, hp, hn]
    | _ => simp [S10.isU6n, onLie] at hi

private theorem exc_contra_U6 (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn3 : 3 ≤ n) (hodd : Odd n) (d6 : TauCeti.ValidLieTypeIndex) (hd6 : d6.1.characteristic = 2)
    (f6 : S ≃* d6.Group) (hcard : Nat.card S = orderTwistedA 5 (2 ^ n))
    (hE : catalogIs S excIndex) : False := by
  obtain ⟨A, hA, hO⟩ := orderTwistedA_two_part (r := 5) (m := n) (by norm_num) (by omega)
  norm_num at hO
  obtain ⟨i, hi, ⟨f⟩⟩ := hE
  cases i with
  | cyclic p hp => simp [excIndex] at hi
  | alternating k hk =>
    simp only [excIndex] at hi
    rw [CatDistinct.card_alternating_of_iso hk f] at hcard
    rw [hO] at hcard
    rcases hi with rfl | rfl
    · have e : 2 ^ (n * 15) * A = 2 ^ 3 * 45 := by
        rw [← hcard] <;> norm_num [Nat.factorial]
      have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 45) e
      omega
    · have e : 2 ^ (n * 15) * A = 2 ^ 3 * 315 := by
        rw [← hcard] <;> norm_num [Nat.factorial]
      have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 315) e
      omega
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    have hM : Nat.card S = 443520 := by
      rw [Nat.card_congr f.toEquiv]
      exact hc.m22
    have e : 2 ^ (n * 15) * A = 2 ^ 7 * 3465 := by
      rw [← hO, ← hcard, hM] <;> norm_num
    have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 3465) e
    omega
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hqc : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        have hcard' : Nat.card S = orderA 2 q'.card := hc.bridge ⟨.A 2 q', hv⟩ S ⟨f⟩
        obtain ⟨A', hA', hO'⟩ := orderA_two_two_part (b := q'.exponent) q'.exponent_pos
        rw [← hqc] at hO'
        have e : 2 ^ (n * 15) * A = 2 ^ (q'.exponent * 3) * A' := by
          rw [← hO, ← hcard, hcard', hO']
        have hu := exp_eq_of_two_pow_mul hA hA' e
        have hmod : 2 ^ q'.exponent % 9 = 4 ∨ 2 ^ q'.exponent % 9 = 7 := by
          rw [hq'] at hi
          exact hi
        have hev := even_of_two_pow_mod_nine hmod
        have hn2 : n % 2 = 1 := Nat.odd_iff.1 hodd
        omega
      · have hadm' : StatedLieAdmissible .PSL 3 q'.p q'.exponent :=
          ⟨q'.prime_p, q'.exponent_pos, by norm_num, by simp, by simp⟩
        refine CatDistinct.xc hc (t' := .PSL) (n' := 3) (by simp) hadm' hq' ?_ d6 hd6 f6
        refine CatDistinct.hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.A 2 q', hv⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor, TauCeti.PrimePower.card_def]
    | twistedA r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hqc : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        have hcard' : Nat.card S = orderTwistedA 2 q'.card :=
          hc.bridge ⟨.twistedA 2 q', hv⟩ S ⟨f⟩
        obtain ⟨A', hA', hO'⟩ :=
          orderTwistedA_two_part (r := 2) (m := q'.exponent) (by norm_num) q'.exponent_pos
        rw [← hqc] at hO'
        have e : 2 ^ (n * 15) * A = 2 ^ (q'.exponent * (2 * (2 + 1) / 2)) * A' := by
          rw [← hO, ← hcard, hcard', hO']
        have hu := exp_eq_of_two_pow_mul hA hA' e
        have hbn : q'.exponent = 5 * n := by omega
        have hO2 : orderTwistedA 2 (2 ^ q'.exponent) = orderTwistedA 5 (2 ^ n) := by
          rw [← hqc, ← hcard']
          exact hcard
        exact u3_ne_u6 hn3 hbn hO2
      · have h3 : 3 ≤ q'.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
        have hadm' : StatedLieAdmissible .PSU 3 q'.p q'.exponent := by
          refine ⟨q'.prime_p, q'.exponent_pos, le_rfl, ?_⟩
          intro hh
          have : q'.p ^ q'.exponent = 2 := (Prod.mk.inj hh).2
          have h3' : 3 ≤ q'.p ^ q'.exponent := by rwa [TauCeti.PrimePower.card_def] at h3
          omega
        refine CatDistinct.xc hc (t' := .PSU) (n' := 3) (by simp) hadm' hq' ?_ d6 hd6 f6
        refine CatDistinct.hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.twistedA 2 q', hv⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | _ => simp [excIndex] at hi

private theorem exc_contra_TE6 (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hn : 1 ≤ n) (d6 : TauCeti.ValidLieTypeIndex) (hd6 : d6.1.characteristic = 2)
    (f6 : S ≃* d6.Group) (hcard : Nat.card S = orderTwistedE6 (2 ^ n))
    (hE : catalogIs S excIndex) : False := by
  obtain ⟨A, hA, hO⟩ := orderTwistedE6_two_part (m := n) hn
  obtain ⟨i, hi, ⟨f⟩⟩ := hE
  cases i with
  | cyclic p hp => simp [excIndex] at hi
  | alternating k hk =>
    simp only [excIndex] at hi
    rw [CatDistinct.card_alternating_of_iso hk f] at hcard
    rw [hO] at hcard
    rcases hi with rfl | rfl
    · have e : 2 ^ (n * 36) * A = 2 ^ 3 * 45 := by
        rw [← hcard] <;> norm_num [Nat.factorial]
      have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 45) e
      omega
    · have e : 2 ^ (n * 36) * A = 2 ^ 3 * 315 := by
        rw [← hcard] <;> norm_num [Nat.factorial]
      have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 315) e
      omega
  | sporadic s =>
    simp only [excIndex] at hi
    subst hi
    have hM : Nat.card S = 443520 := by
      rw [Nat.card_congr f.toEquiv]
      exact hc.m22
    have e : 2 ^ (n * 36) * A = 2 ^ 7 * 3465 := by
      rw [← hO, ← hcard, hM] <;> norm_num
    have hu := exp_eq_of_two_pow_mul hA (by decide : Odd 3465) e
    omega
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | A r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hqc : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        have hcard' : Nat.card S = orderA 2 q'.card := hc.bridge ⟨.A 2 q', hv⟩ S ⟨f⟩
        obtain ⟨A', hA', hO'⟩ := orderA_two_two_part (b := q'.exponent) q'.exponent_pos
        rw [← hqc] at hO'
        have e : 2 ^ (n * 36) * A = 2 ^ (q'.exponent * 3) * A' := by
          rw [← hO, ← hcard, hcard', hO']
        have hu := exp_eq_of_two_pow_mul hA hA' e
        have h6 : q'.exponent % 6 = 0 := by omega
        have h1 := two_pow_mod_nine_of_six_dvd h6
        have hi' : 2 ^ q'.exponent % 9 = 4 ∨ 2 ^ q'.exponent % 9 = 7 := by
          rw [hq'] at hi
          exact hi
        rw [h1] at hi'
        norm_num at hi'
      · have hadm' : StatedLieAdmissible .PSL 3 q'.p q'.exponent :=
          ⟨q'.prime_p, q'.exponent_pos, by norm_num, by simp, by simp⟩
        refine CatDistinct.xc hc (t' := .PSL) (n' := 3) (by simp) hadm' hq' ?_ d6 hd6 f6
        refine CatDistinct.hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.A 2 q', hv⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderA, lieOrderNumerator, lieOrderDivisor, TauCeti.PrimePower.card_def]
    | twistedA r q' =>
      rcases r with _ | _ | _ | r <;> simp [excIndex] at hi
      by_cases hq' : q'.p = 2
      · have hqc : q'.card = 2 ^ q'.exponent := by rw [TauCeti.PrimePower.card_def, hq']
        have hcard' : Nat.card S = orderTwistedA 2 q'.card :=
          hc.bridge ⟨.twistedA 2 q', hv⟩ S ⟨f⟩
        obtain ⟨A', hA', hO'⟩ :=
          orderTwistedA_two_part (r := 2) (m := q'.exponent) (by norm_num) q'.exponent_pos
        rw [← hqc] at hO'
        have e : 2 ^ (n * 36) * A = 2 ^ (q'.exponent * (2 * (2 + 1) / 2)) * A' := by
          rw [← hO, ← hcard, hcard', hO']
        have hu := exp_eq_of_two_pow_mul hA hA' e
        have h6 : q'.exponent % 6 = 0 := by omega
        have h1 := two_pow_mod_nine_of_six_dvd h6
        have hi' : 2 ^ q'.exponent % 9 = 2 ∨ 2 ^ q'.exponent % 9 = 5 := by
          rw [hq'] at hi
          exact hi
        rw [h1] at hi'
        norm_num at hi'
      · have h3 : 3 ≤ q'.card :=
          ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
            ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).2 rfl
        have hadm' : StatedLieAdmissible .PSU 3 q'.p q'.exponent := by
          refine ⟨q'.prime_p, q'.exponent_pos, le_rfl, ?_⟩
          intro hh
          have : q'.p ^ q'.exponent = 2 := (Prod.mk.inj hh).2
          have h3' : 3 ≤ q'.p ^ q'.exponent := by rwa [TauCeti.PrimePower.card_def] at h3
          omega
        refine CatDistinct.xc hc (t' := .PSU) (n' := 3) (by simp) hadm' hq' ?_ d6 hd6 f6
        refine CatDistinct.hM'_of_card hadm' ?_
        rw [hc.bridge ⟨.twistedA 2 q', hv⟩ S ⟨f⟩]
        simp [lieOrderFormula, orderTwistedA, lieOrderNumerator, lieOrderDivisor,
          TauCeti.PrimePower.card_def]
    | _ => simp [excIndex] at hi

private theorem exc_contra (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] {n : ℕ}
    (hodd : Odd n) (hn1 : 1 < n) (hS : catalogIs S (S10.isU6n n) ∨ catalogIs S (S10.isTE6n n))
    (hE : catalogIs S excIndex) : False := by
  have hn3 : 3 ≤ n := by
    obtain ⟨c, hc'⟩ := hodd
    omega
  rcases hS with hU | hT
  · obtain ⟨-, hcard, d6, hd6, ⟨f6⟩⟩ := data_isU6n' hc hU
    exact exc_contra_U6 hc hn3 hodd d6 hd6 f6 hcard hE
  · obtain ⟨hn, hcard, d6, hd6, ⟨f6⟩⟩ := data_isTE6n hc hT
    exact exc_contra_TE6 hc hn d6 hd6 f6 hcard hE

private theorem l2_contra (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] {n m : ℕ}
    (hodd : Odd n) (hn1 : 1 < n) (hS : catalogIs S (S10.isU6n n) ∨ catalogIs S (S10.isTE6n n))
    (hL : catalogIs S (S10.isL2n m)) : False := by
  rcases hS with hU | hT
  · obtain ⟨i, hi, ⟨f⟩⟩ := hU
    exact CatDistinct.field_urn_l2 hc S n m hodd hn1 ⟨i, isUrn_of_isU6n hi, ⟨f⟩⟩ hL
  · obtain ⟨hn, hcard, -⟩ := data_isTE6n hc hT
    rcases CatDistinct.data_isL2n hc hL with h60 | ⟨hm, hcL, -⟩
    · exact e6_ne_60 hn (hcard.symm.trans h60)
    · exact e6_ne_L2 hn hm (hcard.symm.trans hcL)

private theorem catalog_of_isLTwoOddPow {X : Type} [Group X] (h : IsLTwoOddPow X) :
    ∃ m : ℕ, Odd m ∧ 1 < m ∧ catalogIs (X ⧸ Subgroup.center X) (S10.isL2n m) := by
  obtain ⟨m, hm, hm1, ⟨e⟩⟩ := isL2TwoPowOdd_of_isLTwoOddPow h
  have hcen : Subgroup.center X = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsL2TwoPowOdd.center_eq_bot
      (isL2TwoPowOdd_of_isLTwoOddPow h)
  have hpos : 0 < m := by omega
  have hv : (TauCeti.LieTypeIndex.A 1 ⟨2, m, Nat.prime_two, hpos⟩).Valid :=
    valid_A_one_two_pow m hm hm1 hpos
  refine ⟨m, hm, hm1, TauCeti.CFSGIndex.lie ⟨.A 1 ⟨2, m, Nat.prime_two, hpos⟩, hv⟩, ?_, ⟨?_⟩⟩
  · exact ⟨rfl, rfl⟩
  · exact (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot.trans
        (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1
          ⟨2, m, Nat.prime_two, hpos⟩ hv).symm))

section Certified


theorem catDistinctCtx_of
    : CatDistinct.Ctx :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds,
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput,
    fun _ _ d hd e => CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e,
    (CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
      TauCeti.SporadicName.M22).trans (by decide)⟩

theorem i112NormAt_holds
    (G : Type) [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (hKP : CFSG.Open.IsKProper G) : I112NormAt G := by
  intro X K B n _hXK hK hB hBX hr0 hodd hn1 hU
  by_contra hnL
  have hr : GLATwoLocalRank 3 ↥X ≤ CFSG.Open.pRank 3 B :=
    CFSG.AGLEmbedding.le_pRank_of_pow_le_card Nat.prime_three le_rfl hB hr0
  obtain ⟨-, -, -, htype⟩ :=
    i112c_types CFSG.HardMathSupport.Timmesfeld.Coordinator.tables112_holds
      CFSG.HardMathSupport.Timmesfeld.Tables.Census.tableL2_unconditional
      CFSG.HardMathSupport.Solomon.Coordinator.tables112Types_holds
      hsimple hKP Nat.prime_three (by norm_num) hB hBX hr hK hnL
  have hc : CatDistinct.Ctx := catDistinctCtx_of
  rcases htype with h1 | h6
  · obtain ⟨m, -, -, hL2⟩ := catalog_of_isLTwoOddPow h1
    exact l2_contra hc hodd hn1 hU hL2
  · obtain ⟨-, hcat⟩ :=
      isExcShape_of_types (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK) h6
    exact exc_contra hc hodd hn1 hU hcat

end Certified

end CFSG.LocalAnalysis.GLTheoremA
