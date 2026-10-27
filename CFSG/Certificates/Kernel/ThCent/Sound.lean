module

public import Certificates.Data.Kernel.ThCent.Defs
public import CFSG.Certificates.Kernel.Th.Spec.Rank24
public import CFSG.Certificates.Kernel.Th.Spec.DceCore
public import CFSG.Certificates.Kernel.Th.Gen.Wrap

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Th.Spec.Dce CFSG.KC.Loop

theorem toMat_xor' (A B : ℕ) : toMat (A ^^^ B) = toMat A + toMat B := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  exact cast_xor _ _

theorem toVec_xor' (x y : ℕ) : toVec (x ^^^ y) = toVec x + toVec y := by
  funext j
  simp only [toVec, Pi.add_apply, Nat.testBit_xor]
  exact cast_xor _ _

theorem toVec_zero' : toVec 0 = 0 := by
  funext j
  simp [toVec]

theorem pw24_lt (A : ℕ) : ∀ e, pw24 A e < 2 ^ 576
  | 0 => ident24_lt
  | _ + 1 => mul24_lt _ _

theorem toMat_pw24 (A : ℕ) : ∀ e, toMat (pw24 A e) = toMat A ^ e
  | 0 => by rw [pow_zero]; exact toMat_ident24
  | e + 1 => by
    change toMat (mul24 (pw24 A e) A) = _
    rw [toMat_mul24, toMat_pw24 A e, pow_succ]

theorem vpw_lt {v : ℕ} (hv : v < 2 ^ 24) (X : ℕ) : ∀ e, vpw v X e < 2 ^ 24
  | 0 => hv
  | _ + 1 => vecmul_lt _ _

theorem toVec_vpw {v : ℕ} (hv : v < 2 ^ 24) (X : ℕ) : ∀ e,
    toVec (vpw v X e) = Matrix.vecMul (toVec v) (toMat X ^ e)
  | 0 => by rw [pow_zero, Matrix.vecMul_one]; rfl
  | e + 1 => by
    change toVec (vecmul (vpw v X e) X) = _
    rw [toVec_vecmul (vpw_lt hv X e), toVec_vpw hv X e, Matrix.vecMul_vecMul, pow_succ]

theorem ordRank_spec {o r X : ℕ} (h : ordRank o r X = true) :
    toMat X ^ o = 1 ∧ (toMat X + 1).rank = r := by
  have h2 := Gen.andB_right h
  have hp := Nat.eq_of_beq_eq_true (Gen.andB_left h2)
  have hr := Nat.eq_of_beq_eq_true (Gen.andB_right h2)
  refine ⟨?_, ?_⟩
  · rw [← toMat_pw24, hp, toMat_ident24]
  · rw [← hr, Spec.Rank24.rank24_eq]
    change _ = Matrix.rank (toMat (X ^^^ ident24))
    rw [toMat_xor', toMat_ident24]

theorem ordRank_of {o r X : ℕ} (h1 : toMat X ^ o = 1) (h2 : (toMat X + 1).rank = r) :
    ordRank o r X = true := by
  have hv : vpw 1 X o = 1 := by
    refine eq_of_toVec_eq (vpw_lt (by norm_num) X o) (by norm_num) ?_
    rw [toVec_vpw (by norm_num), h1, Matrix.vecMul_one]
  have hp : pw24 X o = ident24 :=
    eq_of_toMat_eq (pw24_lt X o) ident24_lt (by rw [toMat_pw24, h1, toMat_ident24])
  have hr : OutS.rank24 (Nat.xor X ident24) = r := by
    rw [Spec.Rank24.rank24_eq]
    change Matrix.rank (toMat (X ^^^ ident24)) = r
    rw [toMat_xor', toMat_ident24, h2]
  unfold ordRank
  rw [hv, hp, hr, Nat.beq_refl, Nat.beq_refl, Nat.beq_refl]
  rfl

theorem ordRank_conj {o r σ τ : ℕ} {P Q : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hστ : toMat τ = Q * toMat σ * P) (h : ordRank o r σ = true) :
    ordRank o r τ = true := by
  obtain ⟨h1, h2⟩ := ordRank_spec h
  refine ordRank_of ?_ ?_
  · have key : ∀ e, (Q * toMat σ * P) ^ e = Q * toMat σ ^ e * P := by
      intro e
      induction e with
      | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hQP]
      | succ e ih =>
        rw [pow_succ, ih, pow_succ]
        calc Q * toMat σ ^ e * P * (Q * toMat σ * P) = Q * toMat σ ^ e * (P * Q) * toMat σ * P := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hPQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [hστ, key, h1, Matrix.mul_one, hQP]
  · have e : Q * toMat σ * P + 1 = Q * (toMat σ + 1) * P := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP]
    rw [hστ, e, ← h2]
    have hQ : IsUnit Q.det := by
      have := congrArg Matrix.det hQP
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one _ this
    have hP : IsUnit P.det := by
      have := congrArg Matrix.det hPQ
      rw [Matrix.det_mul, Matrix.det_one] at this
      exact IsUnit.of_mul_eq_one _ this
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hQ]

theorem natRec_add_eq_sum (F : ℕ → ℕ) : ∀ k,
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k =
      ∑ l ∈ Finset.range k, F l
  | 0 => by simp
  | k + 1 => by
    change F k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (F l) ih2) k = _
    rw [natRec_add_eq_sum F k, Finset.sum_range_succ, Nat.add_comm]

theorem sumBelow_eq_sum64 (m : ℕ) (f : ℕ → ℕ) : ∀ hi, sumBelow m hi f =
    ∑ i ∈ Finset.range (64 * hi), Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m)
  | 0 => by simp [sumBelow]
  | hi + 1 => by
    have e : sumBelow m (hi + 1) f = Nat.add (Nat.rec (motive := fun _ => ℕ) 0
        (fun l ih2 => Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
          (Nat.add (Nat.shiftLeft hi 6) l)) ih2) 64) (sumBelow m hi f) := rfl
    have e2 : ∀ l, Nat.add (Nat.shiftLeft hi 6) l = 64 * hi + l := fun l => by
      change hi <<< 6 + l = _
      rw [Nat.shiftLeft_eq, Nat.mul_comm]
    rw [e, natRec_add_eq_sum, sumBelow_eq_sum64 m f hi, Nat.mul_succ, Finset.sum_range_add]
    simp only [e2]
    exact Nat.add_comm _ _

theorem sumBelow_eq_sum {m hi : ℕ} (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i := by
  rw [sumBelow_eq_sum64]
  obtain ⟨d, hd⟩ : ∃ d, 64 * hi = m + d := ⟨64 * hi - m, by omega⟩
  rw [hd, Finset.sum_range_add]
  have h2 : ∑ l ∈ Finset.range d,
      Bool.rec (motive := fun _ => ℕ) 0 (f (m + l)) (Nat.blt (m + l) m) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    have hb : Nat.blt (m + l) m = false := by
      cases e : Nat.blt (m + l) m
      · rfl
      · rw [Nat.blt_eq] at e
        omega
    rw [hb]
  rw [h2, Nat.add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hb : Nat.blt i m = true := Nat.blt_eq.mpr (Finset.mem_range.1 hi)
  rw [hb]

theorem countGen (r : ℕ → Bool) {n hi : ℕ} (hn : n ≤ 64 * hi) :
    sumBelow n hi (fun i => nIf(r i, nat_lit 1, nat_lit 0)) =
      ((Finset.range n).filter fun i => r i = true).card := by
  rw [sumBelow_eq_sum _ hn, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases r i <;> rfl

theorem countOR_eq (EB : ℕ → ℕ) {o r lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    countOR EB o r lo n hi = ((Finset.range n).filter fun i => orAt EB o r lo i = true).card :=
  countGen (orAt EB o r lo) hn

theorem countComm_eq (HB TB : ℕ → ℕ) {G lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    countComm HB TB G lo n hi =
      ((Finset.range n).filter fun i => commAt HB TB G lo i = true).card :=
  countGen (commAt HB TB G lo) hn

theorem countSel_eq (R : ℕ → ℕ) {lo n hi : ℕ} (hn : n ≤ 64 * hi) :
    countSel R lo n hi = ((Finset.range n).filter fun i => selAt R lo i = true).card :=
  countGen (selAt R lo) hn

theorem allRec_iff (f : ℕ → Bool) : ∀ m : ℕ,
    Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m = true ↔
      ∀ i < m, f i = true
  | 0 => by simp
  | m + 1 => by
    change Bool.rec (motive := fun _ => Bool) false
      (Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m) (f m) = true ↔ _
    cases e : f m
    · constructor
      · intro h
        exact (Bool.false_ne_true h).elim
      · intro h
        exact absurd (h m (by omega)) (by rw [e]; exact Bool.false_ne_true)
    · change Nat.rec (motive := fun _ => Bool) true (fun i acc => bAnd(f i, acc)) m = true ↔ _
      rw [allRec_iff f m]
      constructor
      · intro h i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h i hi
        · exact e
      · intro h i hi
        exact h i (by omega)

theorem allBelow_spec {m hi : ℕ} {f : ℕ → Bool} (h : allBelow m hi f = true) (hm : m ≤ 64 * hi) :
    ∀ i < m, f i = true := by
  intro i him
  have h1 := (allRec_iff (fun h => Nat.rec (motive := fun _ => Bool) true (fun l ih2 =>
      bAnd((fun i => bIf(Nat.blt i m, f i, true)) (Nat.add (Nat.shiftLeft h 6) l), ih2)) 64) hi).1
    h (i / 64) (by omega)
  have h2 := (allRec_iff (fun l => (fun i => bIf(Nat.blt i m, f i, true))
      (Nat.add (Nat.shiftLeft (i / 64) 6) l)) 64).1 h1 (i % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.shiftLeft (i / 64) 6) (i % 64) = i := by
    change (i / 64) <<< 6 + i % 64 = i
    rw [Nat.shiftLeft_eq]
    omega
  have hb : Nat.blt i m = true := by
    rw [Nat.blt_eq]
    exact him
  dsimp only at h2
  rw [e, hb] at h2
  exact h2

theorem xor_bit {a b : ℕ} (ha : a < 2) (hb : b < 2) :
    ((a ^^^ b : ℕ) : ZMod 2) = a + b ∧ a ^^^ b < 2 := by
  interval_cases a <;> interval_cases b <;> decide

theorem bit_eq (z k : ℕ) : Nat.land (Nat.shiftRight z k) 1 = (z.testBit k).toNat := by
  change (z >>> k) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.toNat_testBit]

theorem par24_step (z : ℕ) : ∀ n,
    ((Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun k acc => Nat.xor acc (Nat.land (Nat.shiftRight z k) (nat_lit 1))) n : ℕ) : ZMod 2) =
      ∑ k ∈ Finset.range n, ((z.testBit k).toNat : ZMod 2) ∧
    Nat.rec (motive := fun _ => ℕ) (nat_lit 0)
      (fun k acc => Nat.xor acc (Nat.land (Nat.shiftRight z k) (nat_lit 1))) n < 2
  | 0 => by simp
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := par24_step z n
    have hb : (z.testBit n).toNat < 2 := by cases z.testBit n <;> decide
    obtain ⟨e1, e2⟩ := xor_bit ih2 hb
    change ((Nat.xor _ (Nat.land (Nat.shiftRight z n) 1) : ℕ) : ZMod 2) = _ ∧ Nat.xor _ _ < 2
    rw [bit_eq]
    refine ⟨?_, e2⟩
    change ((_ ^^^ _ : ℕ) : ZMod 2) = _
    rw [e1, ih1, Finset.sum_range_succ]

theorem par24_cast (z : ℕ) :
    ((par24 z : ℕ) : ZMod 2) = ∑ k : Fin 24, ((z.testBit k).toNat : ZMod 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ((z.testBit k).toNat : ZMod 2)) 24]
  exact (par24_step z 24).1

theorem par24_lt (z : ℕ) : par24 z < 2 := (par24_step z 24).2

theorem bf_cast {x : ℕ} (hx : x < 2 ^ 24) (B y : ℕ) :
    ((bf B x y : ℕ) : ZMod 2) = Matrix.vecMul (toVec x) (toMat B) ⬝ᵥ toVec y := by
  unfold bf
  rw [par24_cast, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e := congrFun (toVec_vecmul hx B) k
  simp only [toVec] at e
  change ((((vecmul x B &&& y).testBit k).toNat : ℕ) : ZMod 2) = _
  rw [Nat.testBit_and, cast_and, e]
  rfl

theorem bf_lt (B x y : ℕ) : bf B x y < 2 := par24_lt _

theorem toVec_shiftLeft {i : ℕ} (hi : i < 24) :
    toVec (Nat.shiftLeft 1 i) = Pi.single (⟨i, hi⟩ : Fin 24) 1 := by
  funext j
  simp only [toVec, Pi.single_apply, Fin.ext_iff]
  change ((((1 <<< i).testBit j).toNat : ℕ) : ZMod 2) = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
  by_cases h : (j : ℕ) = i
  · simp [h]
  · simp [h, Ne.symm h]

theorem shiftLeft_lt' {i : ℕ} (hi : i < 24) : Nat.shiftLeft 1 i < 2 ^ 24 := by
  change 1 <<< i < 2 ^ 24
  rw [Nat.one_shiftLeft]
  exact Nat.pow_lt_pow_right (by norm_num) hi

theorem formOK_spec {B LT : ℕ} (h : formOK B LT = true) :
    ∀ g < 7, toMat (DceS.let24 LT (2 * g)) * toMat B * (toMat (DceS.let24 LT (2 * g))).transpose =
      toMat B := by
  intro g hg
  set L := DceS.let24 LT (2 * g)
  have h1 : formL B L = true := allBelow_spec h (by decide) g hg
  ext i j
  have hij : 24 * (i : ℕ) + j < 576 := by omega
  have h3 := Nat.eq_of_beq_eq_true (allBelow_spec h1 (by decide) (24 * i + j) hij)
  have hdi : Nat.div (24 * (i : ℕ) + j) 24 = i := by
    change (24 * (i : ℕ) + j) / 24 = i
    omega
  have hmj : Nat.mod (24 * (i : ℕ) + j) 24 = j := by
    change (24 * (i : ℕ) + j) % 24 = j
    omega
  unfold formStep at h3
  rw [hdi, hmj] at h3
  have e := congrArg (fun n : ℕ => (n : ZMod 2)) h3
  simp only at e
  rw [bf_cast (vecmul_lt _ _), bf_cast (shiftLeft_lt' i.2), toVec_vecmul (shiftLeft_lt' i.2),
    toVec_vecmul (shiftLeft_lt' j.2), toVec_shiftLeft i.2, toVec_shiftLeft j.2] at e
  simp only [Fin.eta] at e
  have hrow : ∀ (a : Fin 24) (X : Matrix (Fin 24) (Fin 24) (ZMod 2)),
      Matrix.vecMul (Pi.single a 1) X = fun k => X a k := by
    intro a X
    funext k
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have hdot : ∀ (v : Fin 24 → ZMod 2) (a : Fin 24), v ⬝ᵥ Pi.single a 1 = v a := by
    intro v a
    simp [dotProduct, Pi.single_apply]
  rw [hrow, hrow, hrow, hdot] at e
  rw [← e]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct, Finset.sum_mul]

theorem allRec14_of {f : ℕ → Bool} (h : Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (f i)) (nat_lit 14) = true) : ∀ i < 14, f i = true :=
  (allB_iff f 14).1 h

theorem classOK_spec {CB CJ : ℕ → ℕ} {LT n hi : ℕ} (h : classOK CB CJ LT n 0 n hi = true)
    (hn : n ≤ 64 * hi) :
    ∀ k < n, ∀ c < 14, CJ (14 * k + c) < n ∧ DceS.mat CB (CJ (14 * k + c)) =
      mul24 (mul24 (DceS.let24 LT (c ^^^ 1)) (DceS.mat CB k)) (DceS.let24 LT c) := by
  intro k hk c hc
  have h1 := allBelow_spec h hn k hk
  have h2 := allRec14_of h1 c hc
  have e : Nat.add 0 k = k := Nat.zero_add k
  unfold classStep at h2
  rw [e] at h2
  exact ⟨Nat.blt_eq.mp (Gen.andB_left h2), Nat.eq_of_beq_eq_true (Gen.andB_right h2)⟩

theorem letInvOK_spec {LT : ℕ} (h : letInvOK LT = true) :
    ∀ c < 14, mul24 (DceS.let24 LT c) (DceS.let24 LT (c ^^^ 1)) = ident24 := by
  intro c hc
  exact Nat.eq_of_beq_eq_true (allBelow_spec h (by decide) c hc)

theorem memN_iff (k : ℕ) : ∀ l : List ℕ, memN k l = true ↔ k ∈ l
  | [] => by simp [memN]
  | a :: l => by
    change Bool.rec (memN k l) true (Nat.beq a k) = true ↔ _
    rw [List.mem_cons]
    cases e : Nat.beq a k
    · have : a ≠ k := Nat.ne_of_beq_eq_false e
      change memN k l = true ↔ _
      rw [memN_iff k l]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact absurd h.symm this
        · exact h
    · have : a = k := Nat.eq_of_beq_eq_true e
      simp [this]

theorem eqBool_iff {c m : Bool} (h : eqBool m c = true) : c = true ↔ m = true := by
  revert h
  cases c <;> cases m <;> decide

theorem flStep_spec {CB : ℕ → ℕ} {T : ℕ} {FL : List ℕ} {k : ℕ} (h : flStep CB T FL k = true) :
    commB (DceS.mat CB k) T = true ↔ k ∈ FL := by
  rw [← memN_iff]
  exact eqBool_iff h

theorem commB_iff {S G : ℕ} : commB S G = true ↔ mul24 S G = mul24 G S :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by unfold commB; rw [h]; exact Nat.beq_refl _⟩

theorem flOK_spec {CB : ℕ → ℕ} {T : ℕ} {FL : List ℕ} {n hi : ℕ} (h : flOK CB T FL n hi = true)
    (hn : n ≤ 64 * hi) :
    ∀ k < n, (mul24 (DceS.mat CB k) T = mul24 T (DceS.mat CB k) ↔ k ∈ FL) := by
  intro k hk
  rw [← commB_iff]
  exact flStep_spec (allBelow_spec h hn k hk)

section Hint

variable {SV : ℕ → ℕ} {N : ℕ} (hinc : ∀ k, k + 1 < N → SV k < SV (k + 1))
include hinc

theorem sv_mono : ∀ {a b : ℕ}, a ≤ b → b < N → SV a ≤ SV b := by
  intro a b hab hb
  induction b with
  | zero =>
    have : a = 0 := by omega
    rw [this]
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (le_of_lt (hinc b hb))
    · have : a = b + 1 := by omega
      rw [this]

theorem hint_mem {w j : ℕ} (h : hintH SV N w j = true) :
    memH SV N w j = true ↔ ∃ k < N, SV k = w := by
  unfold hintH at h
  cases em : memH SV N w j
  · rw [em] at h
    change CFSG.KC.Th.orB false _ = true at h
    rw [Spec.Dce.orB_iff] at h
    rcases h with h | h
    · exact absurd h (by decide)
    obtain ⟨hjn, hlo, hhi⟩ : Nat.ble j N = true ∧ _ ∧ _ := by
      rw [Spec.Dce.andB_iff, Spec.Dce.andB_iff] at h
      exact ⟨h.1, h.2.1, h.2.2⟩
    have hjN : j ≤ N := Nat.le_of_ble_eq_true hjn
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro k hk hkw
    rcases Nat.lt_or_ge k j with hkj | hkj
    · rw [Spec.Dce.orB_iff] at hlo
      rcases hlo with h0 | hl
      · have : j = 0 := Nat.eq_of_beq_eq_true h0
        omega
      · have hl' : SV (j - 1) < w := Nat.blt_eq.mp hl
        have := sv_mono hinc (a := k) (b := j - 1) (by omega) (by omega)
        omega
    · rw [Spec.Dce.orB_iff] at hhi
      rcases hhi with h0 | hl
      · have : j = N := Nat.eq_of_beq_eq_true h0
        omega
      · have hl' : w < SV j := Nat.blt_eq.mp hl
        have := sv_mono hinc (a := j) (b := k) hkj hk
        omega
  · unfold memH at em
    rw [Spec.Dce.andB_iff] at em
    simp only [true_iff]
    exact ⟨j, Nat.blt_eq.mp em.1, Nat.eq_of_beq_eq_true em.2⟩

end Hint

theorem getN_eq (l : List ℕ) : ∀ p, p < l.length → getN l p = l.getD p 0 := by
  induction l with
  | nil => intro p hp; simp at hp
  | cons a l ih =>
    intro p hp
    cases p with
    | zero => rfl
    | succ p =>
      change getN l p = _
      rw [ih p (by simpa using hp)]
      rfl

@[expose] noncomputable def codeFM (FL : List (Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (u : Fin 24 → ZMod 2) : ℕ :=
  (FL.filter fun Y => decide (Matrix.vecMul u Y = u)).length

@[expose] noncomputable def compM (S : Set (Fin 24 → ZMod 2)) (B : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (Ps FL : List (Matrix (Fin 24) (Fin 24) (ZMod 2))) (u : Fin 24 → ZMod 2) (q : ℕ) : ℕ := by
  classical
  exact if q = 3 * Ps.length then codeFM FL u else
    if q % 3 = 0 then (if Matrix.vecMul u (Ps.getD (q / 3) 0) = 0 then 1 else 0) else
    if q % 3 = 1 then (Matrix.vecMul u B ⬝ᵥ Matrix.vecMul u (Ps.getD (q / 3) 0)).val else
    (if Matrix.vecMul u (Ps.getD (q / 3) 0) ∈ S then 1 else 0)

theorem beqF {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem getD_map_toMat : ∀ (l : List ℕ) (p : ℕ), (l.map toMat).getD p 0 = toMat (l.getD p 0)
  | [], p => by simp [toMat_zero]
  | a :: l, 0 => rfl
  | a :: l, p + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map_toMat l p

theorem getN_eq' (l : List ℕ) : ∀ p, getN l p = l.getD p 0 := by
  induction l with
  | nil => intro p; simp [getN]
  | cons a l ih =>
    intro p
    cases p with
    | zero => rfl
    | succ p =>
      change getN l p = _
      rw [ih p]
      rfl

theorem eqB_eq (y x : ℕ) : eqB y x = if y = x then 1 else 0 := by
  unfold eqB
  cases e : Nat.beq y x
  · rw [if_neg (Nat.ne_of_beq_eq_false e)]
  · rw [if_pos (Nat.eq_of_beq_eq_true e)]

theorem codeF_cons (Y : ℕ) (FL : List ℕ) (x : ℕ) :
    codeF (Y :: FL) x = Nat.add (codeF FL x) (eqB (vecmul x Y) x) := rfl

theorem eqB_vec {x y : ℕ} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24) :
    eqB y x = if toVec y = toVec x then 1 else 0 := by
  rw [eqB_eq]
  by_cases h : y = x
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun e => h (eq_of_toVec_eq hy hx e))]

theorem codeF_eq {x : ℕ} (hx : x < 2 ^ 24) : ∀ FL : List ℕ,
    codeF FL x = codeFM (FL.map toMat) (toVec x)
  | [] => rfl
  | Y :: FL => by
    rw [codeF_cons, codeF_eq hx FL, eqB_vec hx (vecmul_lt _ _), toVec_vecmul hx]
    unfold codeFM
    rw [List.map_cons, List.filter_cons]
    by_cases h : Matrix.vecMul (toVec x) (toMat Y) = toVec x
    · rw [if_pos h, if_pos (by simp [h]), List.length_cons]
    · rw [if_neg h, if_neg (by simp [h])]
      rfl

theorem comp_eq {SV : ℕ → ℕ} {N : ℕ} (hinc : ∀ k, k + 1 < N → SV k < SV (k + 1))
    (hSV : ∀ k < N, SV k < 2 ^ 24) {B : ℕ} {Ps FL : List ℕ} {x q h : ℕ} (hx : x < 2 ^ 24)
    (hq : q ≤ 3 * Ps.length) (hh : hintOK SV N Ps x q h = true) :
    comp SV N B Ps FL x q h = compM {u | ∃ k < N, toVec (SV k) = u} (toMat B) (Ps.map toMat)
      (FL.map toMat) (toVec x) q := by
  classical
  have hdef : comp SV N B Ps FL x q h = Bool.rec (compP SV N B x (vecmul x (getN Ps
      (Nat.div q (nat_lit 3)))) (Nat.mod q (nat_lit 3)) h) (codeF FL x)
      (Nat.beq q (Nat.mul (nat_lit 3) (List.length Ps))) := rfl
  rw [hdef]
  unfold compM
  simp only [List.length_map]
  by_cases hq3 : q = 3 * Ps.length
  · have : Nat.beq q (Nat.mul (nat_lit 3) (List.length Ps)) = true := by
      rw [hq3]
      exact Nat.beq_refl _
    rw [this, if_pos hq3]
    exact codeF_eq hx FL
  have hb : Nat.beq q (Nat.mul (nat_lit 3) (List.length Ps)) = false := beqF hq3
  rw [hb, if_neg hq3]
  have hget : (Ps.map toMat).getD (q / 3) 0 = toMat (Ps.getD (q / 3) 0) := getD_map_toMat Ps _
  have hgN : getN Ps (Nat.div q (nat_lit 3)) = Ps.getD (q / 3) 0 := getN_eq' Ps _
  rw [hget, hgN]
  have hw := toVec_vecmul hx (Ps.getD (q / 3) 0)
  have hwl := vecmul_lt x (Ps.getD (q / 3) 0)
  have hh' : Nat.mod q (nat_lit 3) = 2 →
      hintH SV N (vecmul x (Ps.getD (q / 3) 0)) h = true := by
    intro h2
    unfold hintOK at hh
    rw [Spec.Dce.orB_iff, Spec.Dce.orB_iff] at hh
    rcases hh with hh | hh | hh
    · exact absurd (Nat.eq_of_beq_eq_true hh) hq3
    · have : Nat.beq (Nat.mod q (nat_lit 3)) (nat_lit 2) = true := by rw [h2]; rfl
      rw [this] at hh
      exact absurd hh (by decide)
    · rwa [hgN] at hh
  rw [← hw]
  generalize vecmul x (Ps.getD (q / 3) 0) = w at hw hwl hh' ⊢
  rw [show Nat.mod q (nat_lit 3) = q % 3 from rfl] at hh' ⊢
  unfold compP
  by_cases h0 : q % 3 = 0
  · rw [h0, if_pos rfl]
    change eqB w 0 = _
    rw [eqB_vec (x := 0) (y := w) (by norm_num) hwl, toVec_zero']
  have hb0 : Nat.beq (q % 3) (nat_lit 0) = false := beqF h0
  rw [hb0, if_neg h0]
  by_cases h1 : q % 3 = 1
  · rw [h1, if_pos rfl]
    change bf B x w = _
    have hc := bf_cast hx B w
    rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt (bf_lt B x w)]
  have hb1 : Nat.beq (q % 3) (nat_lit 1) = false := beqF h1
  rw [hb1, if_neg h1]
  have h2 : q % 3 = 2 := by omega
  have hm := hint_mem hinc (hh' h2)
  have hmem : (∃ k < N, toVec (SV k) = toVec w) ↔ ∃ k < N, SV k = w := by
    constructor
    · rintro ⟨k, hk, e⟩
      exact ⟨k, hk, eq_of_toVec_eq (hSV k hk) hwl e⟩
    · rintro ⟨k, hk, e⟩
      exact ⟨k, hk, by rw [e]⟩
  change Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (memH SV N w h) = _
  simp only [Set.mem_setOf_eq]
  revert hm
  cases memH SV N w h
  · intro hm
    have : ¬∃ k < N, toVec (SV k) = toVec w := by
      rw [hmem, ← hm]
      decide
    rw [if_neg this]
  · intro hm
    have : ∃ k < N, toVec (SV k) = toVec w := by
      rw [hmem, ← hm]
    rw [if_pos this]

theorem diffOK_ne {SV R H1 : ℕ → ℕ} {N B : ℕ} {Ps FL : List ℕ} {i1 k : ℕ}
    (hinc : ∀ k, k + 1 < N → SV k < SV (k + 1)) (hSV : ∀ k < N, SV k < 2 ^ 24)
    (hk : k < N) (hi1 : i1 < N)
    (h : diffOK SV R H1 N B Ps FL i1 k = true)
    (hs : Nat.land (R k) 63 ≠ 63) :
    ∃ q, compM {u | ∃ k < N, toVec (SV k) = u} (toMat B) (Ps.map toMat) (FL.map toMat)
        (toVec (SV k)) q ≠
      compM {u | ∃ k < N, toVec (SV k) = u} (toMat B) (Ps.map toMat) (FL.map toMat)
        (toVec (SV i1)) q := by
  unfold diffOK at h
  dsimp only at h
  rw [Spec.Dce.orB_iff] at h
  rcases h with h | h
  · exact absurd (Nat.eq_of_beq_eq_true h) hs
  rw [Spec.Dce.andB_iff, Spec.Dce.andB_iff, Spec.Dce.andB_iff] at h
  obtain ⟨hle, h1, h2, h3⟩ := h
  have hq := Nat.le_of_ble_eq_true hle
  refine ⟨Nat.land (R k) 63, ?_⟩
  rw [← comp_eq hinc hSV (hSV k hk) hq h1, ← comp_eq hinc hSV (hSV i1 hi1) hq h2]
  rw [Spec.Dce.notB_iff] at h3
  exact Nat.ne_of_beq_eq_false h3

end CFSG.KC.ThCent

end
