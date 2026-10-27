module

public import Certificates.Data.Kernel.MinusRealize
public import CFSG.Certificates.Kernel.MinusSecondKindSound
public import CFSG.OddTranspositions.PartThree.Eleven.Five.Refl
import all CFSG.OddTranspositions.PartThree.Eleven.Minus.RealizeCheck
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

namespace CFSG.KC.MinusRealize

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusRealize
open CFSG.KD.MinusRealize CFSG.KD.MinusQuandle CFSG.KD.MinusSecondKind CFSG.KC.MinusQuandle
open CFSG.KC.MinusSecondKind CFSG.RankThree.Native Matrix

theorem anyF_spec {n : ℕ} {g : ℕ → Bool} (h : anyF n g = true) : ∃ k < n, g k = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    change Bool.rec (anyF n g) true (g n) = true at h
    cases hg : g n
    · rw [hg] at h
      obtain ⟨k, hk, h⟩ := ih h
      exact ⟨k, by omega, h⟩
    · exact ⟨n, by omega, hg⟩

theorem dg_eq (c k : ℕ) : dg c k = c / 5 ^ k % 5 := rfl

theorem mk4_eq (a b c d : ℕ) : mk4 a b c d = a + (5 * b + (25 * c + 125 * d)) := rfl

@[expose] def dec (c : ℕ) : Fin 4 → ZMod 5 :=
  ![(dg c 0 : ZMod 5), (dg c 1 : ZMod 5), (dg c 2 : ZMod 5), (dg c 3 : ZMod 5)]

theorem dg_mk4 {a b c d : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5) :
    dg (mk4 a b c d) 0 = a ∧ dg (mk4 a b c d) 1 = b ∧ dg (mk4 a b c d) 2 = c ∧
      dg (mk4 a b c d) 3 = d := by
  have p0 : (5 : ℕ) ^ 0 = 1 := rfl
  have p1 : (5 : ℕ) ^ 1 = 5 := rfl
  have p2 : (5 : ℕ) ^ 2 = 25 := rfl
  have p3 : (5 : ℕ) ^ 3 = 125 := rfl
  simp only [dg_eq, mk4_eq, p0, p1, p2, p3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem dec_mk4 {a b c d : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5) :
    dec (mk4 a b c d) = ![(a : ZMod 5), (b : ZMod 5), (c : ZMod 5), (d : ZMod 5)] := by
  obtain ⟨h0, h1, h2, h3⟩ := dg_mk4 ha hb hc hd
  unfold dec
  rw [h0, h1, h2, h3]

theorem cast_inj {a b : ℕ} (ha : a < 5) (hb : b < 5) (h : (a : ZMod 5) = (b : ZMod 5)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem mk4_inj {a b c d a' b' c' d' : ℕ} (ha : a < 5) (hb : b < 5) (hc : c < 5) (hd : d < 5)
    (ha' : a' < 5) (hb' : b' < 5) (hc' : c' < 5) (hd' : d' < 5)
    (h : dec (mk4 a b c d) = dec (mk4 a' b' c' d')) : mk4 a b c d = mk4 a' b' c' d' := by
  rw [dec_mk4 ha hb hc hd, dec_mk4 ha' hb' hc' hd'] at h
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons] at e0 e1 e2 e3
  rw [cast_inj ha ha' e0, cast_inj hb hb' e1, cast_inj hc hc' e2, cast_inj hd hd' e3]

theorem mod5_lt (n : ℕ) : n % 5 < 5 := Nat.mod_lt _ (by norm_num)

theorem sm_eq (s c : ℕ) : sm s c = mk4 (s * dg c 0 % 5) (s * dg c 1 % 5) (s * dg c 2 % 5)
    (s * dg c 3 % 5) := rfl

theorem dec_sm (s c : ℕ) : dec (sm s c) = (s : ZMod 5) • dec c := by
  rw [sm_eq, dec_mk4 (mod5_lt _) (mod5_lt _) (mod5_lt _) (mod5_lt _)]
  funext a
  fin_cases a <;> simp [dec, ZMod.natCast_mod, Nat.cast_mul]

theorem inv_eq_pow (q : ZMod 5) : q⁻¹ = q ^ 3 := by
  by_cases h : q = 0
  · rw [h]
    simp
  · have h4 : q ^ 3 * q = 1 := by
      revert h
      revert q
      decide
    exact (eq_inv_of_mul_eq_one_left h4).symm

theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

theorem cast_sub4 (x k y : ℕ) :
    (((x + 4 * (k * y)) % 5 : ℕ) : ZMod 5) = (x : ZMod 5) - (k : ZMod 5) * (y : ZMod 5) := by
  rw [ZMod.natCast_mod]
  push_cast
  linear_combination ((k : ZMod 5) * (y : ZMod 5)) * five_eq_zero

theorem isSquare_iff (q : ZMod 5) : IsSquare q ↔ q = 0 ∨ q = 1 ∨ q = 4 := by
  unfold IsSquare
  revert q
  decide

theorem qf_eq (c d : ℕ) : qf c d = (dg c 0 * dg d 0 + (dg c 1 * dg d 1 +
    (dg c 2 * dg d 2 + 3 * (dg c 3 * dg d 3)))) % 5 := rfl

theorem qf_lt (c d : ℕ) : qf c d < 5 := by
  rw [qf_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem qf_cast (c d : ℕ) : (qf c d : ZMod 5) = fiveForm 3 false (dec c) (dec d) := by
  rw [qf_eq, ZMod.natCast_mod]
  simp only [fiveForm, Fin.sum_univ_three, dec, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  simp
  linear_combination ((dg c 3 : ZMod 5) * (dg d 3 : ZMod 5)) * five_eq_zero

theorem subK_eq (k c d : ℕ) : subK k c d =
    mk4 ((dg d 0 + 4 * (k * dg c 0)) % 5) ((dg d 1 + 4 * (k * dg c 1)) % 5)
      ((dg d 2 + 4 * (k * dg c 2)) % 5) ((dg d 3 + 4 * (k * dg c 3)) % 5) := rfl

theorem dec_subK (k c d : ℕ) : dec (subK k c d) = dec d - (k : ZMod 5) • dec c := by
  rw [subK_eq, dec_mk4 (mod5_lt _) (mod5_lt _) (mod5_lt _) (mod5_lt _)]
  simp only [cast_sub4]
  funext a
  fin_cases a <;> simp [dec]

theorem rf_eq (c d : ℕ) : rf c d = subK ((2 * (qf c d * qf c c ^ 3)) % 5) c d := by
  unfold rf
  rw [force_eq]
  rfl

theorem dec_rf (c d : ℕ) : dec (rf c d) =
    dec d - (2 * fiveForm 3 false (dec d) (dec c) * (fiveForm 3 false (dec c) (dec c))⁻¹) •
      dec c := by
  rw [rf_eq, dec_subK]
  congr 2
  rw [ZMod.natCast_mod]
  push_cast
  rw [inv_eq_pow, fiveForm_comm 3 false (dec d) (dec c), ← qf_cast, ← qf_cast]
  ring

theorem decode_eq (v : Array ℕ) : decode v = ![(v[0]! : ZMod 5), (v[1]! : ZMod 5),
    (v[2]! : ZMod 5), (v[3]! : ZMod 5)] := by
  funext a
  fin_cases a <;> rfl

theorem pin_spec {π : Bool} {P : ℕ} (h : pinOK π P = true) {i : ℕ} (hi : i < 65) :
    cd P i = codeA (vA π i) ∧ (vA π i)[0]! < 5 ∧ (vA π i)[1]! < 5 ∧ (vA π i)[2]! < 5 ∧
      (vA π i)[3]! < 5 := by
  have h1 := allF_spec h hi
  simp only [pinRow, bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨h1, h2⟩ := h1
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.le_of_ble_eq_true (allF_spec h2 (k := 0) (by norm_num)),
    Nat.le_of_ble_eq_true (allF_spec h2 (k := 1) (by norm_num)),
    Nat.le_of_ble_eq_true (allF_spec h2 (k := 2) (by norm_num)),
    Nat.le_of_ble_eq_true (allF_spec h2 (k := 3) (by norm_num))⟩

theorem vecD_eq {π : Bool} {P : ℕ} (h : pinOK π P = true) (i : Fin 65) :
    vecD π i = dec (cd P i) := by
  obtain ⟨e, h0, h1, h2, h3⟩ := pin_spec h i.2
  rw [e, codeA, dec_mk4 h0 h1 h2 h3, vecD, decode_eq]
  rfl

theorem cd_canon {π : Bool} {P : ℕ} (h : pinOK π P = true) {i : ℕ} (hi : i < 65) :
    ∃ a b c d, a < 5 ∧ b < 5 ∧ c < 5 ∧ d < 5 ∧ cd P i = mk4 a b c d := by
  obtain ⟨e, h0, h1, h2, h3⟩ := pin_spec h hi
  exact ⟨_, _, _, _, h0, h1, h2, h3, e⟩

theorem code_inj {π : Bool} {P : ℕ} (h : pinOK π P = true) {i : ℕ} (hi : i < 65) {s c : ℕ}
    (he : dec (sm s c) = dec (cd P i)) : sm s c = cd P i := by
  obtain ⟨a, b, c', d, ha, hb, hc, hd, e⟩ := cd_canon h hi
  rw [e] at he ⊢
  rw [sm_eq] at he ⊢
  exact mk4_inj (mod5_lt _) (mod5_lt _) (mod5_lt _) (mod5_lt _) ha hb hc hd he

theorem of_sgn {π : Bool} {q : ℕ} (h : sgn π q = true) :
    (q : ZMod 5) ≠ 0 ∧ (IsSquare (q : ZMod 5) ↔ π = true) := by
  cases π
  · simp only [sgn, bOr_eq, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> rw [isSquare_iff] <;> decide
  · simp only [sgn, bOr_eq, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;> rw [isSquare_iff] <;> decide

theorem sgn_of {π : Bool} {q : ℕ} (hq : q < 5) (h0 : (q : ZMod 5) ≠ 0)
    (hs : IsSquare (q : ZMod 5) ↔ π = true) : sgn π q = true := by
  rw [isSquare_iff] at hs
  revert h0 hs
  interval_cases q <;> cases π <;> decide

theorem reflMat_eq (v : Fin 4 → ZMod 5) : reflMat v = fiveReflMatrix 3 false v := by
  ext a b
  simp only [reflMat, fiveReflMatrix, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  have hJ : Jv v b = fiveFormVec 3 false v b := by
    fin_cases b <;> simp [Jv, fiveFormVec, Fin.last]
  rw [hJ]
  ring

theorem MA_mat {π : Bool} (i : Fin 65) : f5Mat (MA π i) = fiveReflMatrix 3 false (vecD π i) := by
  rw [MA, f5Mat_reflArr, reflMat_eq]
  rfl

theorem validA_of {a : Array ℕ} (h : f5Mat a * f5Mat a = 1) : f5ValidA a = true := by
  have hd : (f5Mat a).det * (f5Mat a).det = 1 := by rw [← det_mul, h, det_one]
  unfold f5ValidA
  rw [bne_iff_ne]
  intro h0
  rw [f5Mat_det] at hd
  have hz : ((f5DetZ a : ℤ) : ZMod 5) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Int.dvd_of_emod_eq_zero h0)
  rw [hz, zero_mul] at hd
  exact zero_ne_one hd

theorem smul_ne_zero_cast {s : ℕ} (hs : s < 4) : ((Nat.succ s : ℕ) : ZMod 5) ≠ 0 := by
  interval_cases s <;> decide

section Checks

variable {π : Bool} {P : ℕ} {R : ℕ → ℕ}

theorem sign_spec (hP : pinOK π P = true) (hS : signOK π P = true) (i : Fin 65) :
    fiveForm 3 false (vecD π i) (vecD π i) ≠ 0 ∧
      (IsSquare (fiveForm 3 false (vecD π i) (vecD π i)) ↔ π = true) := by
  have h := allF_spec hS i.2
  simp only [force_eq] at h
  rw [vecD_eq hP, ← qf_cast]
  exact of_sgn h

theorem signProp_of (hP : pinOK π P = true) (hS : signOK π P = true) : signProp π :=
  sign_spec hP hS

theorem table_spec (hR : rowsOK R = true) (hP : pinOK π P = true) (hT : tableOK R P = true)
    (i j : Fin 65) :
    (∃ s < 4, dec (sm (Nat.succ s) (rf (cd P i) (cd P j))) = dec (cd P (ln (R i) j))) ∧
      ((i : ℕ) ≠ j → ∀ s < 4, sm (Nat.succ s) (cd P j) ≠ cd P i) := by
  have h1 := allF_spec hT i.2
  simp only [force_eq] at h1
  have h2 := allF_spec h1 j.2
  simp only [force_eq, bAnd_eq, bOr_eq, bNot_eq, Bool.and_eq_true, Bool.or_eq_true] at h2
  obtain ⟨hA, hB⟩ := h2
  refine ⟨?_, fun hij s hs => ?_⟩
  · obtain ⟨s, hs, e⟩ := anyF_spec hA
    exact ⟨s, hs, by rw [Nat.eq_of_beq_eq_true e]⟩
  · rcases hB with hB | hB
    · exact absurd (Nat.eq_of_beq_eq_true hB) hij
    · have := allF_spec hB hs
      simp only [Bool.not_eq_true'] at this
      exact fun e => by rw [e, Nat.beq_refl] at this; exact Bool.noConfusion this

theorem TA_val (hR : rowsOK R = true) (i j : Fin 65) : ((TA i j : Fin 65) : ℕ) = ln (R i) j := by
  obtain ⟨h1, h2⟩ := tq_spec hR i.2 j.2
  have e1 : (minusTable[i]!)[j]! = minusQuandleT i j := rfl
  rw [TA, Fin.val_ofNat, e1, h1, Nat.mod_eq_of_lt h2]
  exact (ln_eq R _ _).symm

theorem form_ne_zero_vec {v : Fin 4 → ZMod 5} (h : fiveForm 3 false v v ≠ 0) : v ≠ 0 := by
  rintro rfl
  apply h
  simp [fiveForm]

theorem matProp_of (hR : rowsOK R = true) (hP : pinOK π P = true) (hS : signOK π P = true)
    (hT : tableOK R P = true) :
    matProp ((List.ofFn fun i : Fin 65 => MA π i).toArray) := by
  have hinv : ∀ i : Fin 65, f5Mat (MA π i) * f5Mat (MA π i) = 1 := fun i => by
    rw [MA_mat, fiveReflMatrix_mul_self]
  refine ⟨fun i => ?_, fun i => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [getElem_toArray_ofFn_MA]
    exact validA_of (hinv i)
  · rw [getElem_toArray_ofFn_MA]
    apply f5EqA_of_mat_eq
    rw [f5Mat_mulA, hinv, f5Mat_idA]
  · rw [getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA]
    apply f5EqA_of_mat_eq
    rw [f5Mat_mulA, f5Mat_mulA, MA_mat, MA_mat, MA_mat]
    obtain ⟨hQ, hsq⟩ := sign_spec hP hS i
    have hg := fiveForm_mulVec_of_mem (π := π)
      (Subgroup.subset_closure (fiveReflOf_mem hQ hsq) : fiveReflOf 3 false (vecD π i) ∈
        fiveReflectionGroup 3 false π)
    have hc := congrArg Units.val (conj_fiveReflOf hg (vecD π j))
    have hc' : fiveReflMatrix 3 false (vecD π i) * fiveReflMatrix 3 false (vecD π j) *
        fiveReflMatrix 3 false (vecD π i) =
        fiveReflMatrix 3 false (fiveReflMatrix 3 false (vecD π i) *ᵥ vecD π j) := hc
    rw [hc']
    obtain ⟨⟨s, hs, e⟩, -⟩ := table_spec hR hP hT i j
    have hw : fiveReflMatrix 3 false (vecD π i) *ᵥ vecD π j = dec (rf (cd P i) (cd P j)) := by
      rw [dec_rf, ← vecD_eq hP, ← vecD_eq hP]
      exact fiveReflOf_mulVec 3 false (vecD π i) (vecD π j)
    have hT' : vecD π (TA i j) = ((Nat.succ s : ℕ) : ZMod 5) •
        (fiveReflMatrix 3 false (vecD π i) *ᵥ vecD π j) := by
      rw [hw, ← dec_sm, e, vecD_eq hP, TA_val hR]
    rw [hT']
    exact (congrArg Units.val (fiveReflOf_smul 3 false _ (smul_ne_zero_cast hs))).symm
  · rw [getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA]
    cases he : f5EqA (MA π i) (MA π j)
    · rfl
    exfalso
    have hm := f5Mat_eq_of_eqA he
    rw [MA_mat, MA_mat] at hm
    obtain ⟨hQi, -⟩ := sign_spec hP hS i
    obtain ⟨hQj, -⟩ := sign_spec hP hS j
    have hv := congrArg (fun M => M *ᵥ vecD π i) hm
    have e1 : fiveReflMatrix 3 false (vecD π i) *ᵥ vecD π i = vecD π i -
        (2 * fiveForm 3 false (vecD π i) (vecD π i) *
          (fiveForm 3 false (vecD π i) (vecD π i))⁻¹) • vecD π i :=
      fiveReflOf_mulVec 3 false (vecD π i) (vecD π i)
    have e2 : fiveReflMatrix 3 false (vecD π j) *ᵥ vecD π i = vecD π i -
        (2 * fiveForm 3 false (vecD π i) (vecD π j) *
          (fiveForm 3 false (vecD π j) (vecD π j))⁻¹) • vecD π j :=
      fiveReflOf_mulVec 3 false (vecD π j) (vecD π i)
    have h2 : (2 * fiveForm 3 false (vecD π i) (vecD π i) *
        (fiveForm 3 false (vecD π i) (vecD π i))⁻¹) = 2 := by
      rw [mul_assoc, mul_inv_cancel₀ hQi, mul_one]
    rw [e1, e2, h2] at hv
    have h2v := sub_right_inj.1 hv
    have h6 : (3 * 2 : ZMod 5) = 1 := by decide
    have hu : vecD π i = (3 * (2 * fiveForm 3 false (vecD π i) (vecD π j) *
        (fiveForm 3 false (vecD π j) (vecD π j))⁻¹)) • vecD π j := by
      calc vecD π i = (3 * 2 : ZMod 5) • vecD π i := by rw [h6, one_smul]
        _ = _ := by rw [mul_smul, h2v, ← mul_smul]
    generalize (3 * (2 * fiveForm 3 false (vecD π i) (vecD π j) *
        (fiveForm 3 false (vecD π j) (vecD π j))⁻¹)) = u at hu
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hu
      exact form_ne_zero_vec hQi hu
    have hval : ((u.val : ℕ) : ZMod 5) = u := ZMod.natCast_zmod_val _
    have hlt := ZMod.val_lt u
    have hpos : 0 < u.val := by
      rcases Nat.eq_zero_or_pos u.val with h | h
      · exact absurd ((ZMod.val_eq_zero _).1 h) hu0
      · exact h
    have hs1 : Nat.succ (u.val - 1) = u.val := by omega
    obtain ⟨-, hB⟩ := table_spec hR hP hT i j
    refine hB (fun e => hij (Fin.ext e)) (u.val - 1) (by omega) (code_inj hP i.2 ?_)
    rw [dec_sm, hs1, hval, ← vecD_eq hP, ← vecD_eq hP, ← hu]

theorem coverProp_of (hP : pinOK π P = true) (hC : coverOK π P = true) : coverProp π := by
  intro v hQ hs
  obtain ⟨x, hx⟩ : ∃ x, x = mk4 (v 0).val (v 1).val (v 2).val (v 3).val := ⟨_, rfl⟩
  have hv : dec x = v := by
    rw [hx, dec_mk4 (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _)]
    funext a
    fin_cases a <;> simp [ZMod.natCast_zmod_val]
  have hx625 : x < 625 := by
    have h0 := ZMod.val_lt (v 0)
    have h1 := ZMod.val_lt (v 1)
    have h2 := ZMod.val_lt (v 2)
    have h3 := ZMod.val_lt (v 3)
    rw [hx, mk4_eq]
    omega
  have h1 := allF_spec hC hx625
  simp only [force_eq, bOr_eq, bNot_eq, Bool.or_eq_true, Bool.not_eq_true'] at h1
  have hq : (qf x x : ZMod 5) = fiveForm 3 false v v := by rw [qf_cast, hv]
  have hsg : sgn π (qf x x) = true :=
    sgn_of (qf_lt x x) (by rw [hq]; exact hQ) (by rw [hq]; exact hs)
  rcases h1 with h1 | h1
  · rw [hsg] at h1
    exact Bool.noConfusion h1
  obtain ⟨i, hi, h2⟩ := anyF_spec h1
  obtain ⟨s, hs', h3⟩ := anyF_spec h2
  refine ⟨⟨i, hi⟩, ((Nat.succ s : ℕ) : ZMod 5), smul_ne_zero_cast hs', ?_⟩
  rw [← hv, ← Nat.eq_of_beq_eq_true h3, dec_sm, vecD_eq hP]

end Checks

theorem realizeCheck_of {R : ℕ → ℕ} {Pt Pf : ℕ} (hR : rowsOK R = true)
    (hPt : pinOK true Pt = true) (hSt : signOK true Pt = true) (hTt : tableOK R Pt = true)
    (hCt : coverOK true Pt = true) (hPf : pinOK false Pf = true) (hSf : signOK false Pf = true)
    (hTf : tableOK R Pf = true) (hCf : coverOK false Pf = true) : realizeCheck () = true := by
  unfold realizeCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨signProp_of hPt hSt, signProp_of hPf hSf⟩, matProp_of hR hPt hSt hTt⟩,
    matProp_of hR hPf hSf hTf⟩, coverProp_of hPt hCt⟩, coverProp_of hPf hCf⟩

end CFSG.KC.MinusRealize
