module

public import CFSG.Certificates.Kernel.McL.Model
public import CFSG.Certificates.Kernel.McL.Sub
public import CFSG.Certificates.Kernel.LceSTabSound
import CFSG.Certificates.Kernel.Co1DceLemmas
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Fintype.Perm
import CFSG.Certificates.Kernel.LceSP.Walk
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.McLM

open CFSG.KC CFSG.Certificates.LCE

private theorem dig_concat {B A v k i : ℕ} (hB : 0 < B) (hA : A < B ^ k) :
    (A + v * B ^ k) / B ^ i % B = if i < k then A / B ^ i % B else v / B ^ (i - k) % B := by
  split_ifs with hi
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hi
    have e : v * B ^ (i + t + 1) = B ^ i * (B * (v * B ^ t)) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hi)
    have e : (A + v * B ^ k) / B ^ (k + j) = v / B ^ j := by
      rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm v, Nat.add_mul_div_left _ _ (by positivity),
        Nat.div_eq_of_lt hA, Nat.zero_add]
    rw [e, Nat.add_sub_cancel_left]

private theorem pget_eq (p i : ℕ) : McL.pget p i = p / 64 ^ i % 64 := by
  change (p >>> (6 * i)) &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

private theorem pget_lt (p i : ℕ) : McL.pget p i < 64 := by
  rw [pget_eq]
  exact Nat.mod_lt _ (by norm_num)

private noncomputable def fold6 (f : ℕ → ℕ) (d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul 6 i))) d

private theorem fold6_succ {f : ℕ → ℕ} {d : ℕ} (hf : ∀ i < d, f i < 64) :
    fold6 f (d + 1) = fold6 f d + f d * 64 ^ d ∧ fold6 f d < 64 ^ d := by
  induction d with
  | zero =>
    refine ⟨?_, by simp [fold6]⟩
    change 0 ||| f 0 <<< (6 * 0) = 0 + f 0 * 64 ^ 0
    simp
  | succ d ih =>
    obtain ⟨e, hlt⟩ := ih fun i hi => hf i (by omega)
    have hlt' : fold6 f (d + 1) < 64 ^ (d + 1) := by
      rw [e]
      have := hf d (by omega)
      calc fold6 f d + f d * 64 ^ d < 64 ^ d + f d * 64 ^ d := by omega
        _ = (f d + 1) * 64 ^ d := by ring
        _ ≤ 64 * 64 ^ d := Nat.mul_le_mul_right _ (by omega)
        _ = 64 ^ (d + 1) := by ring
    refine ⟨?_, hlt'⟩
    have hlt2 : fold6 f (d + 1) < 2 ^ (6 * (d + 1)) := by
      rw [pow_mul]
      norm_num
      exact hlt'
    change fold6 f (d + 1) ||| f (d + 1) <<< (6 * (d + 1)) = _
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt2, Nat.shiftLeft_eq, pow_mul, Nat.add_comm]
    norm_num

private theorem fold6_spec (f : ℕ → ℕ) : ∀ d, (∀ i < d, f i < 64) →
    fold6 f d < 64 ^ d ∧ ∀ i, McL.pget (fold6 f d) i = if i < d then f i else 0
  | 0, _ => ⟨by simp [fold6], fun i => by
      rw [pget_eq]
      simp [fold6]⟩
  | d + 1, hf => by
    obtain ⟨hlt, hb⟩ := fold6_spec f d (fun i hi => hf i (by omega))
    obtain ⟨e, -⟩ := fold6_succ (f := f) (d := d) (fun i hi => hf i (by omega))
    have hfd := hf d (by omega)
    refine ⟨?_, fun i => ?_⟩
    · rw [e]
      calc fold6 f d + f d * 64 ^ d < 64 ^ d + f d * 64 ^ d := by omega
        _ = (f d + 1) * 64 ^ d := by ring
        _ ≤ 64 * 64 ^ d := Nat.mul_le_mul_right _ (by omega)
        _ = 64 ^ (d + 1) := by ring
    · have hbi := hb i
      rw [pget_eq] at hbi ⊢
      rw [e, dig_concat (by norm_num) hlt]
      split_ifs with h1 h2 h2
      · rw [hbi]
        simp only [h1, ↓reduceIte]
      · omega
      · have : i = d := by omega
        subst this
        simp [Nat.mod_eq_of_lt hfd]
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt (show d < i by omega)
        rw [show d + j + 1 - d = j + 1 by omega, Nat.div_eq_of_lt (lt_of_lt_of_le hfd
          (Nat.le_self_pow (by omega) 64)), Nat.zero_mod]

private theorem pmul_eq (d p q : ℕ) :
    McL.pmul d p q = fold6 (fun i => McL.pget q (McL.pget p i)) d := rfl

private theorem pid_eq (d : ℕ) : McL.pid d = fold6 (fun i => i) d := rfl

private theorem pget_pmul (d p q : ℕ) {i : ℕ} (hi : i < d) :
    McL.pget (McL.pmul d p q) i = McL.pget q (McL.pget p i) := by
  rw [pmul_eq, (fold6_spec _ d (fun _ _ => pget_lt _ _)).2]
  simp only [hi, ↓reduceIte]

private theorem pmul_lt (d p q : ℕ) : McL.pmul d p q < 64 ^ d := by
  rw [pmul_eq]
  exact (fold6_spec _ d (fun _ _ => pget_lt _ _)).1

private theorem pget_pid {d i : ℕ} (hd : d ≤ 64) (hi : i < d) : McL.pget (McL.pid d) i = i := by
  rw [pid_eq, (fold6_spec _ d (fun j hj => by omega)).2]
  simp only [hi, ↓reduceIte]

private theorem pid_lt {d : ℕ} (hd : d ≤ 64) : McL.pid d < 64 ^ d := by
  rw [pid_eq]
  exact (fold6_spec _ d (fun j hj => by omega)).1

private theorem fold6_congr {f g : ℕ → ℕ} : ∀ d, (∀ i < d, f i = g i) → fold6 f d = fold6 g d
  | 0, _ => rfl
  | d + 1, h => by
    change fold6 f d ||| f d <<< (6 * d) = fold6 g d ||| g d <<< (6 * d)
    rw [fold6_congr d (fun i hi => h i (by omega)), h d (by omega)]

private theorem fold6_self (p : ℕ) : ∀ d, fold6 (fun i => McL.pget p i) d = p % 64 ^ d
  | 0 => by
    rw [pow_zero, Nat.mod_one]
    rfl
  | d + 1 => by
    rw [(fold6_succ (fun i _ => pget_lt p i)).1, fold6_self p d, pget_eq, Nat.mod_pow_succ]
    ring

private theorem perm_ext {d p q : ℕ} (hp : p < 64 ^ d) (hq : q < 64 ^ d)
    (h : ∀ i < d, McL.pget p i = McL.pget q i) : p = q := by
  rw [← Nat.mod_eq_of_lt hp, ← Nat.mod_eq_of_lt hq, ← fold6_self, ← fold6_self]
  exact fold6_congr d h

private theorem canon_iff {d p : ℕ} : Nat.shiftRight p (Nat.mul 6 d) = 0 ↔ p < 64 ^ d := by
  rw [LceP.shr_eq, Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)]
  change p < 2 ^ (6 * d) ↔ _
  rw [pow_mul]
  norm_num

private theorem inRange_iff {d p : ℕ} : McL.inRange d p = true ↔ ∀ i < d, McL.pget p i < d := by
  unfold McL.inRange
  rw [LceP.allRec_iff (fun i => Nat.blt (McL.pget p i) d) d]
  simp only [Nat.blt_eq]

private def Val (d p : ℕ) : Prop :=
  p < 64 ^ d ∧ (∀ i < d, McL.pget p i < d) ∧
    ∀ i < d, ∀ j < d, McL.pget p i = McL.pget p j → i = j

private noncomputable def toF (d p : ℕ) (i : Fin d) : Fin d :=
  if h : McL.pget p i.val < d then ⟨_, h⟩ else i

private theorem toF_val {d p : ℕ} (hp : Val d p) (i : Fin d) : (toF d p i).val = McL.pget p i.val := by
  simp only [toF, hp.2.1 _ i.isLt, ↓reduceDIte]

private theorem toF_inj {d p : ℕ} (hp : Val d p) : Function.Injective (toF d p) := by
  intro a b h
  have h' := congrArg Fin.val h
  rw [toF_val hp, toF_val hp] at h'
  exact Fin.ext (hp.2.2 _ a.isLt _ b.isLt h')

open Classical in
private noncomputable def E (d p : ℕ) : Equiv.Perm (Fin d) :=
  if h : Val d p then Equiv.ofBijective (toF d p) (Finite.injective_iff_bijective.mp (toF_inj h))
  else 1

private theorem E_val {d p : ℕ} (hp : Val d p) (i : Fin d) : (E d p i).val = McL.pget p i.val := by
  unfold E
  simp only [hp, ↓reduceDIte, Equiv.ofBijective_apply]
  exact toF_val hp i

private theorem Val_pmul {d p q : ℕ} (hp : Val d p) (hq : Val d q) : Val d (McL.pmul d p q) := by
  refine ⟨pmul_lt _ _ _, fun i hi => ?_, fun i hi j hj h => ?_⟩
  · rw [pget_pmul d p q hi]
    exact hq.2.1 _ (hp.2.1 i hi)
  · rw [pget_pmul d p q hi, pget_pmul d p q hj] at h
    exact hp.2.2 _ hi _ hj (hq.2.2 _ (hp.2.1 i hi) _ (hp.2.1 j hj) h)

private theorem E_pmul {d p q : ℕ} (hp : Val d p) (hq : Val d q) :
    E d (McL.pmul d p q) = E d q * E d p := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [Equiv.Perm.mul_apply, E_val (Val_pmul hp hq), E_val hq, E_val hp, pget_pmul d p q i.isLt]

private theorem Val_pid {d : ℕ} (hd : d ≤ 64) : Val d (McL.pid d) := by
  refine ⟨pid_lt hd, fun i hi => ?_, fun i hi j hj h => ?_⟩
  · rw [pget_pid hd hi]
    exact hi
  · rwa [pget_pid hd hi, pget_pid hd hj] at h

private theorem E_pid {d : ℕ} (hd : d ≤ 64) : E d (McL.pid d) = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [E_val (Val_pid hd), pget_pid hd i.isLt]
  rfl

private noncomputable def enc (d : ℕ) (σ : Equiv.Perm (Fin d)) : ℕ :=
  fold6 (fun i => if h : i < d then (σ ⟨i, h⟩).val else 0) d

private theorem enc_spec {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) :
    enc d σ < 64 ^ d ∧ ∀ i : Fin d, McL.pget (enc d σ) i.val = (σ i).val := by
  have hf : ∀ i < d, (fun i => if h : i < d then (σ ⟨i, h⟩).val else 0) i < 64 := by
    intro i hi
    simp only [hi, ↓reduceDIte]
    have := (σ ⟨i, hi⟩).isLt
    omega
  obtain ⟨h1, h2⟩ := fold6_spec _ d hf
  refine ⟨h1, fun i => ?_⟩
  unfold enc
  rw [h2]
  simp only [i.isLt, ↓reduceIte, ↓reduceDIte]

private theorem Val_enc {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) : Val d (enc d σ) := by
  obtain ⟨h1, h2⟩ := enc_spec hd σ
  refine ⟨h1, fun i hi => ?_, fun i hi j hj h => ?_⟩
  · rw [h2 ⟨i, hi⟩]
    exact (σ _).isLt
  · rw [h2 ⟨i, hi⟩, h2 ⟨j, hj⟩] at h
    have := σ.injective (Fin.ext h)
    exact congrArg Fin.val this

private theorem E_enc {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) : E d (enc d σ) = σ := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [E_val (Val_enc hd σ), (enc_spec hd σ).2 i]

private theorem enc_E {d p : ℕ} (hd : d ≤ 64) (hp : Val d p) : enc d (E d p) = p := by
  refine perm_ext (enc_spec hd _).1 hp.1 fun i hi => ?_
  rw [(enc_spec hd _).2 ⟨i, hi⟩, E_val hp]

private theorem enc_inj {d : ℕ} (hd : d ≤ 64) {σ τ : Equiv.Perm (Fin d)} (h : enc d σ = enc d τ) :
    σ = τ := by
  rw [← E_enc hd σ, ← E_enc hd τ, h]

private theorem enc_mul {d : ℕ} (hd : d ≤ 64) (σ τ : Equiv.Perm (Fin d)) :
    McL.pmul d (enc d σ) (enc d τ) = enc d (τ * σ) := by
  have hv := Val_pmul (Val_enc hd σ) (Val_enc hd τ)
  rw [← enc_E hd hv, E_pmul (Val_enc hd σ) (Val_enc hd τ), E_enc hd, E_enc hd]

private theorem enc_one {d : ℕ} (hd : d ≤ 64) : enc d 1 = McL.pid d := by
  rw [← E_pid hd, enc_E hd (Val_pid hd)]

private theorem pget_or (a b j : ℕ) : McL.pget (a ||| b) j = McL.pget a j ||| McL.pget b j := by
  change ((a ||| b) >>> (6 * j)) &&& 63 = ((a >>> (6 * j)) &&& 63) ||| ((b >>> (6 * j)) &&& 63)
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight]
  cases a.testBit (6 * j + k) <;> cases b.testBit (6 * j + k) <;> simp

private theorem pget_shift {x k j : ℕ} (hx : x < 64) :
    McL.pget (x <<< (6 * k)) j = if j = k then x else 0 := by
  rw [pget_eq, Nat.shiftLeft_eq, pow_mul]
  norm_num
  split_ifs with h
  · subst h
    rw [Nat.mul_div_cancel _ (by positivity), Nat.mod_eq_of_lt hx]
  · rcases Nat.lt_or_gt_of_ne h with hlt | hgt
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
      have e : x * 64 ^ (j + t + 1) = 64 ^ j * (64 * (x * 64 ^ t)) := by ring
      rw [e, Nat.mul_div_cancel_left _ (by positivity), Nat.mul_mod_right]
    · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hgt
      have e : 64 ^ (k + t + 1) = 64 ^ k * 64 ^ (t + 1) := by ring
      rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (by positivity),
        Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.le_self_pow (by omega) 64)), Nat.zero_mod]

private noncomputable def pinvAcc (p : ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul 6 (McL.pget p i)))) m

private theorem pinvAcc_spec {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) :
    ∀ m ≤ d, pinvAcc (enc d σ) m < 64 ^ d ∧ ∀ j : Fin d,
      McL.pget (pinvAcc (enc d σ) m) j.val = if (σ⁻¹ j).val < m then (σ⁻¹ j).val else 0
  | 0, _ => by
    refine ⟨by positivity, fun j => ?_⟩
    rw [pget_eq]
    simp [pinvAcc]
  | m + 1, hm => by
    obtain ⟨h1, h2⟩ := pinvAcc_spec hd σ m (by omega)
    have hpm : McL.pget (enc d σ) m = (σ ⟨m, by omega⟩).val := (enc_spec hd σ).2 ⟨m, by omega⟩
    have e : pinvAcc (enc d σ) (m + 1) = pinvAcc (enc d σ) m ||| m <<< (6 * (σ ⟨m, by omega⟩).val) := by
      change Nat.lor (pinvAcc (enc d σ) m) (Nat.shiftLeft m (Nat.mul 6 (McL.pget (enc d σ) m))) = _
      rw [hpm]
      rfl
    have hm64 : m < 64 := by omega
    refine ⟨?_, fun j => ?_⟩
    · rw [e]
      have h64d : (64 : ℕ) ^ d = 2 ^ (6 * d) := by
        rw [pow_mul]
        norm_num
      have hs := (σ ⟨m, by omega⟩).isLt
      have hterm : m <<< (6 * (σ ⟨m, by omega⟩).val) < 64 ^ d := by
        rw [Nat.shiftLeft_eq, pow_mul]
        norm_num
        calc m * 64 ^ (σ ⟨m, by omega⟩).val < 64 * 64 ^ (σ ⟨m, by omega⟩).val :=
              Nat.mul_lt_mul_of_pos_right hm64 (by positivity)
          _ = 64 ^ ((σ ⟨m, by omega⟩).val + 1) := by ring
          _ ≤ 64 ^ d := Nat.pow_le_pow_right (by norm_num) hs
      rw [h64d] at h1 hterm ⊢
      exact Nat.or_lt_two_pow h1 hterm
    · rw [e, pget_or, h2 j, pget_shift hm64]
      by_cases hj : j.val = (σ ⟨m, by omega⟩).val
      · have hj' : σ⁻¹ j = ⟨m, by omega⟩ := by
          rw [Equiv.Perm.inv_eq_iff_eq]
          exact Fin.ext hj
        simp only [hj, hj', ↓reduceIte, lt_irrefl, Nat.zero_or, Nat.lt_succ_self]
      · have hne : (σ⁻¹ j).val ≠ m := by
          intro h
          apply hj
          have : σ⁻¹ j = ⟨m, by omega⟩ := Fin.ext h
          rw [Equiv.Perm.inv_eq_iff_eq] at this
          rw [this]
        simp only [hj, ↓reduceIte, Nat.or_zero]
        by_cases hlt : (σ⁻¹ j).val < m
        · simp only [hlt, ↓reduceIte, show (σ⁻¹ j).val < m + 1 by omega]
        · simp only [hlt, ↓reduceIte, show ¬ (σ⁻¹ j).val < m + 1 by omega]

private theorem pinv_enc {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) :
    McL.Sub.pinv d (enc d σ) = enc d σ⁻¹ := by
  obtain ⟨h1, h2⟩ := pinvAcc_spec hd σ d le_rfl
  have e : McL.Sub.pinv d (enc d σ) = pinvAcc (enc d σ) d := rfl
  rw [e]
  refine perm_ext h1 (enc_spec hd _).1 fun i hi => ?_
  rw [h2 ⟨i, hi⟩, (enc_spec hd _).2 ⟨i, hi⟩]
  simp only [(σ⁻¹ _).isLt, ↓reduceIte]

private theorem pairOK_enc {d : ℕ} (hd : d ≤ 64) (σ : Equiv.Perm (Fin d)) :
    McL.pairOK d (enc d σ) (enc d σ⁻¹) = true := by
  have v1 := Val_enc hd σ
  have v2 := Val_enc hd σ⁻¹
  unfold McL.pairOK
  simp only [LceP.andB_iff, Nat.beq_eq]
  refine ⟨canon_iff.2 v1.1, canon_iff.2 v2.1, inRange_iff.2 v1.2.1, inRange_iff.2 v2.2.1, ?_⟩
  rw [enc_mul hd, inv_mul_cancel, enc_one hd]

private theorem Val_of_pairOK {d p q : ℕ} (hd : d ≤ 64) (h : McL.pairOK d p q = true) :
    Val d p ∧ Val d q ∧ E d q = (E d p)⁻¹ := by
  unfold McL.pairOK at h
  simp only [LceP.andB_iff, Nat.beq_eq] at h
  obtain ⟨hp, hq, hpr, hqr, hm⟩ := h
  have hpr' := inRange_iff.1 hpr
  have hqr' := inRange_iff.1 hqr
  have hl : ∀ i < d, McL.pget q (McL.pget p i) = i := fun i hi => by
    have := congrArg (fun r => McL.pget r i) hm
    rwa [pget_pmul d p q hi, pget_pid hd hi] at this
  have vp : Val d p := ⟨canon_iff.1 hp, hpr', fun i hi j hj h => by rw [← hl i hi, ← hl j hj, h]⟩
  have hsurj : ∀ x < d, ∃ i < d, McL.pget p i = x := by
    intro x hx
    obtain ⟨i, hi⟩ := (Finite.injective_iff_surjective.mp (toF_inj vp)) ⟨x, hx⟩
    exact ⟨i.val, i.isLt, by rw [← toF_val vp, hi]⟩
  have vq : Val d q := by
    refine ⟨canon_iff.1 hq, hqr', fun x hx y hy h => ?_⟩
    obtain ⟨i, hi, rfl⟩ := hsurj x hx
    obtain ⟨j, hj, rfl⟩ := hsurj y hy
    rw [hl i hi, hl j hj] at h
    rw [h]
  refine ⟨vp, vq, ?_⟩
  have e := E_pmul vp vq
  rw [hm, E_pid hd] at e
  exact eq_inv_of_mul_eq_one_left e.symm

private theorem bval_succ {H : Type*} [Group H] (z : ℕ → H) (W n : ℕ) :
    bval z W (n + 1) = bval z W n * letV z (wLet W n) := by
  simp [bval, List.range_succ]

private theorem bval_map {A B : Type*} [Group A] [Group B] (f : A →* B) (z : ℕ → A) (W n : ℕ) :
    f (bval z W n) = bval (fun i => f (z i)) W n := by
  induction n with
  | zero => simp [bval]
  | succ n ih =>
    rw [bval_succ, bval_succ, map_mul, ih]
    congr 1
    unfold letV
    split_ifs <;> simp

private theorem bval_mem {A : Type*} [Group A] (z : ℕ → A) (S : Subgroup A) {g W : ℕ}
    (hz : ∀ i < g, z i ∈ S) : ∀ n, (∀ i < n, wLet W i < 2 * g) → bval z W n ∈ S
  | 0, _ => by simp [bval, S.one_mem]
  | n + 1, h => by
    rw [bval_succ]
    refine S.mul_mem (bval_mem z S hz n fun i hi => h i (by omega)) ?_
    have hc := h n (by omega)
    unfold letV
    split_ifs
    · exact S.one_mem
    · exact hz _ (by omega)
    · exact S.inv_mem (hz _ (by omega))

private noncomputable def Kc (d BP : ℕ) (M : Subgroup (Equiv.Perm (Fin d))) :
    ℕ → Subgroup (Equiv.Perm (Fin d))
  | 0 => M
  | l + 1 => if h : McL.Model.bpt BP l < d then
      Kc d BP M l ⊓ MulAction.stabilizer (Equiv.Perm (Fin d)) (⟨McL.Model.bpt BP l, h⟩ : Fin d)
    else Kc d BP M l

private theorem Kc_succ_le (d BP : ℕ) (M : Subgroup (Equiv.Perm (Fin d))) (l : ℕ) :
    Kc d BP M (l + 1) ≤ Kc d BP M l := by
  change (if h : McL.Model.bpt BP l < d then _ else _) ≤ _
  split_ifs
  · exact inf_le_left
  · exact le_rfl

private theorem Kc_anti (d BP : ℕ) (M : Subgroup (Equiv.Perm (Fin d))) {l l' : ℕ} (h : l ≤ l') :
    Kc d BP M l' ≤ Kc d BP M l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans (Kc_succ_le d BP M _) ih

section Model

variable {MG EP ED : ℕ → ℕ} {d g BP nE : ℕ}

private noncomputable def Dl (MG : ℕ → ℕ) (d c : ℕ) : Equiv.Perm (Fin d) := (E d (MG c))⁻¹

private theorem gens_spec (hd : d ≤ 64) (hgens : McL.Sub.gensOK MG d g = true) :
    ∀ c < 2 * g, Val d (MG c) ∧ (c % 2 = 1 → Dl MG d c = (Dl MG d (c - 1))⁻¹) := by
  have hp := (LceP.allRec_iff (fun i => McL.pairOK d (MG (2 * i)) (MG (2 * i + 1))) g).1 hgens
  intro c hc
  obtain ⟨v1, v2, hE⟩ := Val_of_pairOK hd (hp (c / 2) (by omega))
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · rw [show c = 2 * (c / 2) by omega]
    exact ⟨v1, fun h => by omega⟩
  · rw [show c = 2 * (c / 2) + 1 by omega]
    refine ⟨v2, fun _ => ?_⟩
    rw [show 2 * (c / 2) + 1 - 1 = 2 * (c / 2) by omega]
    unfold Dl
    rw [hE]

private theorem word_spec (hd : d ≤ 64) (hgens : McL.Sub.gensOK MG d g = true) (hg : g < 128)
    (f : ℕ → Equiv.Perm (Fin d)) (hf : ∀ i < g, f i = Dl MG d (2 * i)) {W : ℕ} :
    ∀ n, (∀ i < n, wLet W i < 2 * g) →
      Val d (McL.evalW MG d W n) ∧ (E d (McL.evalW MG d W n))⁻¹ = bval f W n
  | 0, _ => by
    refine ⟨Val_pid hd, ?_⟩
    change (E d (McL.pid d))⁻¹ = _
    rw [E_pid hd]
    simp [bval]
  | n + 1, h => by
    obtain ⟨v, e⟩ := word_spec hd hgens hg f hf n fun i hi => h i (by omega)
    set c := wLet W n
    have hc : c < 2 * g := h n (by omega)
    obtain ⟨vc, hodd⟩ := gens_spec hd hgens c hc
    change Val d (McL.pmul d (McL.evalW MG d W n) (MG c)) ∧
      (E d (McL.pmul d (McL.evalW MG d W n) (MG c)))⁻¹ = _
    refine ⟨Val_pmul v vc, ?_⟩
    rw [E_pmul v vc, mul_inv_rev, e, bval_succ]
    congr 1
    unfold letV
    split_ifs with h255 h2
    · exact absurd h255 (by omega)
    · rw [hf _ (by omega), show 2 * (c / 2) = c by omega]
      rfl
    · rw [hf _ (by omega), show 2 * (c / 2) = c - 1 by omega, ← hodd (by omega)]
      rfl

private theorem ents_spec (hd : d ≤ 64) (M : Subgroup (Equiv.Perm (Fin d)))
    (hgens : McL.Sub.gensOK MG d g = true) (hM : ∀ c < 2 * g, Dl MG d c ∈ M)
    (hents : McL.Model.elemsOK MG EP ED d g BP nE = true) :
    ∀ e < nE, Val d (EP e) ∧ (E d (EP e))⁻¹ ∈ Kc d BP M (McL.Model.dL (ED e)) := by
  have hall := CFSG.Certificates.Co1D.allBelow_spec hents (by
    change nE ≤ 64 * (nE >>> 6 + 1)
    rw [Nat.shiftRight_eq_div_pow]
    omega)
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro he
  have hc := hall e he
  unfold McL.Model.entOK at hc
  dsimp only at hc
  set D := ED e
  set P := EP e
  cases h0 : Nat.beq (McL.Model.dKind D) 0 <;> rw [h0] at hc <;> dsimp only at hc
  · cases h1 : Nat.beq (McL.Model.dKind D) 1 <;> rw [h1] at hc <;> dsimp only at hc
    · cases h2 : Nat.beq (McL.Model.dKind D) 2 <;> rw [h2] at hc <;> dsimp only at hc
      · cases h3 : Nat.beq (McL.Model.dKind D) 3 <;> rw [h3] at hc <;> dsimp only at hc
        · exact absurd hc (by decide)
        ·
          simp only [LceP.andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hc
          obtain ⟨ha, hl1, hla, hP, hfix⟩ := hc
          obtain ⟨va, ma⟩ := ih _ ha (by omega)
          rw [← hP] at va ma
          refine ⟨va, ?_⟩
          have hm : (E d P)⁻¹ ∈ Kc d BP M (McL.Model.dL D - 1) := Kc_anti d BP M hla ma
          obtain ⟨l, hl⟩ : ∃ l, McL.Model.dL D = l + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hl1).symm⟩
          rw [hl] at hm hfix ⊢
          have e1 : Nat.sub (l + 1) 1 = l := Nat.add_sub_cancel l 1
          rw [Nat.add_sub_cancel] at hm
          rw [e1] at hfix
          change (E d P)⁻¹ ∈ (if h : McL.Model.bpt BP l < d then _ else _)
          split_ifs with hb
          · refine ⟨hm, ?_⟩
            change (E d P)⁻¹ ∈ MulAction.stabilizer (Equiv.Perm (Fin d)) _
            rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.Perm.inv_eq_iff_eq]
            exact Fin.ext (by rw [E_val va]; exact hfix.symm)
          · exact hm
      ·
        simp only [LceP.andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hc
        obtain ⟨ha, hla, hr, hcan, hm⟩ := hc
        obtain ⟨va, ma⟩ := ih _ ha (by omega)
        have hl : ∀ i < d, McL.pget (EP (McL.Model.dA D)) (McL.pget P i) = i := fun i hi => by
          have := congrArg (fun r => McL.pget r i) hm
          rwa [pget_pmul d _ _ hi, pget_pid hd hi] at this
        have vP : Val d P := ⟨canon_iff.1 hcan, inRange_iff.1 hr,
          fun i hi j hj h => by rw [← hl i hi, ← hl j hj, h]⟩
        refine ⟨vP, ?_⟩
        have e1 := E_pmul vP va
        rw [hm, E_pid hd] at e1
        have e2 : (E d P)⁻¹ = E d (EP (McL.Model.dA D)) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv]
          exact e1.symm
        rw [e2, ← inv_inv (E d (EP (McL.Model.dA D)))]
        exact Subgroup.inv_mem _ (Kc_anti d BP M hla ma)
    ·
      simp only [LceP.andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hc
      obtain ⟨ha, hb, hla, hlb, hP⟩ := hc
      obtain ⟨va, ma⟩ := ih _ ha (by omega)
      obtain ⟨vb, mb⟩ := ih _ hb (by omega)
      rw [hP]
      refine ⟨Val_pmul va vb, ?_⟩
      rw [E_pmul va vb, mul_inv_rev]
      exact Subgroup.mul_mem _ (Kc_anti d BP M hla ma) (Kc_anti d BP M hlb mb)
  ·
    simp only [LceP.andB_iff, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨ha, hl0, hP⟩ := hc
    rw [hP, hl0]
    exact ⟨(gens_spec hd hgens _ ha).1, hM _ ha⟩

end Model

section Orbit

variable {d : ℕ} (K : Subgroup (Equiv.Perm (Fin d))) (b : Fin d)

private def OInv (S : ℕ) : Prop :=
  S = 0 ∨ ∃ (c seen : ℕ) (f : ℕ → ℕ), 1 ≤ c ∧ c ≤ d ∧ seen < 2 ^ 64 ∧
    (∀ k < c, ∃ h : f k < d, (⟨f k, h⟩ : Fin d) ∈ MulAction.orbit K b) ∧
    (∀ k < c, ∀ k' < c, f k = f k' → k = k') ∧
    (∀ x, seen.testBit x = decide (∃ k < c, f k = x)) ∧
    S = c + 256 * seen + 2 ^ 72 * fold6 f c

private theorem OInv_dec {S c seen : ℕ} {f : ℕ → ℕ} (hc : c < 256) (hs : seen < 2 ^ 64)
    (hS : S = c + 256 * seen + 2 ^ 72 * fold6 f c) :
    Nat.land S 255 = c ∧ Nat.land (Nat.shiftRight S 8) (Nat.sub (Nat.shiftLeft 1 64) 1) = seen ∧
      Nat.shiftRight S 72 = fold6 f c := by
  refine ⟨?_, ?_, ?_⟩
  · change S &&& (2 ^ 8 - 1) = c
    rw [Nat.and_two_pow_sub_one_eq_mod, hS]
    omega
  · change (S >>> 8) &&& ((1 <<< 64) - 1) = seen
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, hS]
    have e : c + 256 * seen + 2 ^ 72 * fold6 f c = c + 2 ^ 8 * (seen + 2 ^ 64 * fold6 f c) := by ring
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  · change S >>> 72 = _
    rw [Nat.shiftRight_eq_div_pow, hS]
    have e : c + 256 * seen + 2 ^ 72 * fold6 f c = (c + 256 * seen) + 2 ^ 72 * fold6 f c := rfl
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt (by omega), zero_add]

private noncomputable def ostep (EP ED : ℕ → ℕ) (l J S : ℕ) : ℕ :=
  (fun cnt seen pts par gen => (fun p =>
      Bool.rec (motive := fun _ => Nat) 0
        (Nat.lor (Nat.succ cnt) (Nat.lor (Nat.shiftLeft (Nat.lor seen (Nat.shiftLeft 1 p)) 8)
          (Nat.shiftLeft (Nat.lor pts (Nat.shiftLeft p (Nat.mul 6 cnt))) 72)))
        (andB (Nat.blt 0 cnt) (andB (Nat.blt par cnt) (andB (Nat.blt 0 (EP gen))
          (andB (Nat.ble l (McL.Model.dL (ED gen)))
          (Nat.beq (Nat.land seen (Nat.shiftLeft 1 p)) 0))))))
      (McL.pget (EP gen) (McL.pget pts par)))
    (Nat.land S 255)
    (Nat.land (Nat.shiftRight S 8) (Nat.sub (Nat.shiftLeft 1 64) 1))
    (Nat.shiftRight S 72) (Nat.land J 63)
    (Nat.land (Nat.shiftRight J 6) 4095)

private noncomputable def orec (EP ED : ℕ → ℕ) (l m : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ S => S)
    (fun _ ih J S => ih (Nat.shiftRight J 18) (ostep EP ED l J S)) m

private theorem ostep_inv {EP ED : ℕ → ℕ} {l : ℕ} (hd : d ≤ 64)
    (hgen : ∀ gen < 4096, 0 < EP gen → l ≤ McL.Model.dL (ED gen) →
      Val d (EP gen) ∧ (E d (EP gen))⁻¹ ∈ K) (J : ℕ) {S : ℕ} (hS : OInv K b S) :
    OInv K b (ostep EP ED l J S) := by
  rcases hS with rfl | ⟨c, seen, f, hc1, hcd, hs, horb, hinj, hbits, hS⟩
  · exact Or.inl rfl
  obtain ⟨hd1, hd2, hd3⟩ := OInv_dec (by omega) hs hS
  unfold ostep
  rw [hd1, hd2, hd3]
  dsimp only
  rw [LceP.brec_eq]
  split_ifs with hcond
  swap
  · exact Or.inl rfl
  simp only [LceP.andB_iff, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq] at hcond
  obtain ⟨-, hpar, hEP, hlv, hseen⟩ := hcond
  set par := Nat.land J 63
  set gen := Nat.land (Nat.shiftRight J 6) 4095
  have hgen4 : gen < 4096 := by
    change Nat.land (Nat.shiftRight J 6) 4095 < 4096
    rw [LceP.land_lit _ 12 4095 (by norm_num)]
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨vg, mg⟩ := hgen gen hgen4 hEP hlv
  have hf64 : ∀ k < c, f k < 64 := fun k hk => by
    obtain ⟨h, -⟩ := horb k hk
    omega
  have hpts : McL.pget (fold6 f c) par = f par := by
    rw [(fold6_spec f c hf64).2]
    simp only [hpar, ↓reduceIte]
  rw [hpts]
  rw [hpts] at hseen
  obtain ⟨hxd, hxo⟩ := horb par hpar
  set p := McL.pget (EP gen) (f par)
  have hpv : p = (E d (EP gen) ⟨f par, hxd⟩).val := (E_val vg ⟨f par, hxd⟩).symm
  have hpd : p < d := by rw [hpv]; exact Fin.isLt _
  have hpo : (⟨p, hpd⟩ : Fin d) ∈ MulAction.orbit K b := by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 hxo
    have hmem : E d (EP gen) ∈ K := by
      have := K.inv_mem mg
      rwa [inv_inv] at this
    refine MulAction.mem_orbit_iff.2 ⟨⟨E d (EP gen), hmem⟩ * k, ?_⟩
    rw [mul_smul, hk, Subgroup.mk_smul, Equiv.Perm.smul_def]
    exact Fin.ext hpv.symm
  have hnew : ∀ k < c, f k ≠ p := by
    intro k hk he
    have hb := hbits p
    have h0 : seen.testBit p = false := by
      have := congrArg (fun x => Nat.testBit x p) hseen
      simp only [Nat.zero_testBit] at this
      change (seen &&& (1 <<< p)).testBit p = false at this
      rwa [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow_self, Bool.and_true] at this
    rw [h0] at hb
    have hb' : ∀ x < c, ¬ f x = p := by simpa using hb
    exact hb' k hk he
  set f' : ℕ → ℕ := fun k => if k < c then f k else p with hf'
  have hinj' : ∀ k < c + 1, ∀ k' < c + 1, f' k = f' k' → k = k' := by
    intro k hk k' hk' h
    simp only [hf'] at h
    split_ifs at h with h1 h2 h2
    · exact hinj k h1 k' h2 h
    · exact absurd h (hnew k h1)
    · exact absurd h.symm (hnew k' h2)
    · omega
  have hcd' : c + 1 ≤ d := by
    have := Finset.card_le_card_of_injOn f' (s := Finset.range (c + 1)) (t := Finset.range d)
      (fun k hk => by
        rw [Finset.mem_coe, Finset.mem_range] at hk ⊢
        simp only [hf']
        split_ifs with h1
        · exact (horb k h1).1
        · exact hpd)
      (fun k hk k' hk' h => hinj' k (Finset.mem_range.1 hk) k' (Finset.mem_range.1 hk') h)
    simpa using this
  have hp64 : p < 64 := by omega
  have hs' : (seen ||| 1 <<< p) < 2 ^ 64 := by
    refine Nat.or_lt_two_pow hs ?_
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) hp64
  have hfold : fold6 f c ||| p <<< (6 * c) = fold6 f' (c + 1) := by
    change _ = fold6 f' c ||| f' c <<< (6 * c)
    rw [fold6_congr c (f := f') (g := f) (fun k hk => by simp only [hf', hk, ↓reduceIte])]
    simp only [hf', lt_irrefl, ↓reduceIte]
  right
  refine ⟨c + 1, seen ||| 1 <<< p, f', by omega, hcd', hs', fun k hk => ?_, hinj', fun x => ?_, ?_⟩
  · simp only [hf']
    split_ifs with h1
    · exact horb k h1
    · exact ⟨hpd, hpo⟩
  · rw [Nat.testBit_or, hbits, Nat.one_shiftLeft, Nat.testBit_two_pow]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨k, hk, he⟩ | he)
      · exact ⟨k, by omega, by simp only [hf', hk, ↓reduceIte]; exact he⟩
      · exact ⟨c, by omega, by simp only [hf', lt_irrefl, ↓reduceIte]; exact he⟩
    · rintro ⟨k, hk, he⟩
      simp only [hf'] at he
      split_ifs at he with h1
      · exact Or.inl ⟨k, h1, he⟩
      · exact Or.inr he
  · change (c + 1) ||| ((seen ||| 1 <<< p) <<< 8 ||| (fold6 f c ||| p <<< (6 * c)) <<< 72) = _
    rw [hfold, show (72 : ℕ) = 64 + 8 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib]
    have e1 := LceP.lor_shl (a := seen ||| 1 <<< p) (b := fold6 f' (c + 1)) hs'
    change (seen ||| 1 <<< p) ||| fold6 f' (c + 1) <<< 64 = _ at e1
    rw [e1]
    have e2 := LceP.lor_shl (a := c + 1) (b := (seen ||| 1 <<< p) + fold6 f' (c + 1) * 2 ^ 64)
      (k := 8) (by norm_num; omega)
    change (c + 1) ||| ((seen ||| 1 <<< p) + fold6 f' (c + 1) * 2 ^ 64) <<< 8 = _ at e2
    rw [e2]
    ring

private theorem orec_inv {EP ED : ℕ → ℕ} {l : ℕ} (hd : d ≤ 64)
    (hgen : ∀ gen < 4096, 0 < EP gen → l ≤ McL.Model.dL (ED gen) →
      Val d (EP gen) ∧ (E d (EP gen))⁻¹ ∈ K) :
    ∀ m J S, OInv K b S → OInv K b (orec EP ED l m J S)
  | 0, _, _, hS => hS
  | m + 1, J, _, hS => orec_inv hd hgen m _ _ (ostep_inv K b hd hgen J hS)

private theorem OInv_start (hd : d ≤ 64) :
    OInv K b (Nat.lor 1 (Nat.lor (Nat.shiftLeft (Nat.shiftLeft 1 b.val) 8) (Nat.shiftLeft b.val 72))) := by
  right
  have hb64 : b.val < 64 := by have := b.isLt; omega
  have hs : (1 <<< b.val) < 2 ^ 64 := by
    rw [Nat.one_shiftLeft]
    exact Nat.pow_lt_pow_right (by norm_num) hb64
  refine ⟨1, 1 <<< b.val, fun _ => b.val, le_rfl, by have := b.isLt; omega, hs,
    fun k _ => ⟨b.isLt, MulAction.mem_orbit_self b⟩, fun k hk k' hk' _ => by omega, fun x => ?_, ?_⟩
  · rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact ⟨fun h => ⟨0, by omega, h⟩, fun ⟨_, _, h⟩ => h⟩
  · have hf : fold6 (fun _ => b.val) 1 = b.val := by
      change 0 ||| b.val <<< (6 * 0) = b.val
      simp
    rw [hf]
    change 1 ||| ((1 <<< b.val) <<< 8 ||| b.val <<< 72) = _
    rw [show (72 : ℕ) = 64 + 8 from rfl, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib]
    have e1 := LceP.lor_shl (a := 1 <<< b.val) (b := b.val) (k := 64) hs
    change (1 <<< b.val) ||| b.val <<< 64 = _ at e1
    rw [e1]
    have e2 := LceP.lor_shl (a := 1) (b := (1 <<< b.val) + b.val * 2 ^ 64) (k := 8) (by norm_num)
    change 1 ||| ((1 <<< b.val) + b.val * 2 ^ 64) <<< 8 = _ at e2
    rw [e2]
    ring

private theorem orbit_card (hd : d ≤ 64) {S : ℕ} (hS : OInv K b S) :
    McL.Model.orbCount (Nat.land S (Nat.sub (Nat.shiftLeft 1 72) 1)) ≤
      Nat.card (MulAction.orbit K b) := by
  rcases hS with rfl | ⟨c, seen, f, hc1, hcd, hs, horb, hinj, -, hS⟩
  · exact Nat.zero_le _
  have e : McL.Model.orbCount (Nat.land S (Nat.sub (Nat.shiftLeft 1 72) 1)) = c := by
    change (S &&& ((1 <<< 72) - 1)) &&& 255 = c
    rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod,
      show (255 : ℕ) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hS,
      Nat.mod_mod_of_dvd _ (by norm_num : (2 : ℕ) ^ 8 ∣ 2 ^ 72)]
    have h1 : c + 256 * seen + 2 ^ 72 * fold6 f c = c + 2 ^ 8 * (seen + 2 ^ 64 * fold6 f c) := by ring
    rw [h1, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  change McL.Model.orbCount (Nat.land S (Nat.sub (Nat.shiftLeft 1 72) 1)) ≤ _
  rw [e]
  let F : Fin c → MulAction.orbit K b := fun k =>
    ⟨⟨f k.val, (horb k.val k.isLt).1⟩, (horb k.val k.isLt).2⟩
  have hF : Function.Injective F := by
    intro k k' h
    have := congrArg (fun x => (x.val : Fin d).val) h
    exact Fin.ext (hinj _ k.isLt _ k'.isLt this)
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_fin] at this

private theorem card_split (b : Fin d) :
    Nat.card K = Nat.card (MulAction.orbit K b) *
      Nat.card (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin d)) b : Subgroup (Equiv.Perm (Fin d))) := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer K b)
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at h1
  have e : MulAction.stabilizer K b ≃
      (K ⊓ MulAction.stabilizer (Equiv.Perm (Fin d)) b : Subgroup (Equiv.Perm (Fin d))) :=
    { toFun := fun x => ⟨x.1.1, Subgroup.mem_inf.2 ⟨x.1.2, by
        rw [MulAction.mem_stabilizer_iff]
        exact (MulAction.mem_stabilizer_iff.1 x.2 : _)⟩⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, by
        rw [MulAction.mem_stabilizer_iff]
        exact (MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 x.2).2 : _)⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [← Nat.card_congr e, ← h1, Nat.mul_comm]

end Orbit

private def relSet (REL : ℕ → ℕ) (NR : ℕ) : Set (FreeGroup ℕ) :=
  {r | ∃ k < NR, r = bval FreeGroup.of (LceS.wWord (REL k)) (LceS.wLen (REL k))}

private theorem lift_rels {H : Type*} [Group H] {REL : ℕ → ℕ} {NR : ℕ} (f : ℕ → H)
    (hf : ∀ r < NR, bval f (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1) :
    ∀ r ∈ relSet REL NR, FreeGroup.lift f r = 1 := by
  rintro r ⟨k, hk, hr⟩
  rw [hr, bval_map]
  simp only [FreeGroup.lift_apply_of]
  exact hf k hk

theorem model_sound {G : Type*} [Group G] (y : ℕ → G) {MG EP ED REL : ℕ → ℕ}
    {d g BP nE NR N0 nLev : ℕ} {OM OJ ON : ℕ → ℕ} (hd : d ≤ 64)
    (hgens : McL.Sub.gensOK MG d g = true) (hrels : McL.Sub.relsHold MG REL d NR = true)
    (hlet : ∀ r < NR, ∀ i < LceS.wLen (REL r), wLet (LceS.wWord (REL r)) i < 2 * g)
    (hents : McL.Model.elemsOK MG EP ED d g BP nE = true)
    (hwrap : ∀ e < 4096, EP e = 0 ∨ ∃ e' < nE, EP e = EP e' ∧ ED e = ED e')
    (horb : ∀ l < nLev, McL.Model.orbCount (McL.Model.orbitRun EP ED BP l (OM l) (OJ l)) = ON l ∧
      McL.Model.bpt BP l < d)
    (hprod : N0 ≤ ∏ l ∈ Finset.range nLev, ON l)
    (hQ : ∀ (H : Type) [Group H] (z : ℕ → H),
      (∀ r < NR, bval z (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1) →
        Nat.card (Subgroup.closure (z '' {i | i < g})) ≠ 0 ∧
          Nat.card (Subgroup.closure (z '' {i | i < g})) ≤ N0)
    (hy : ∀ r < NR, bval y (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1)
    (hg : g < 128 := by decide) :
    ∃ (ψ : ℕ → G) (I : Set ℕ), (McL.pid d ∈ I ∧ ψ (McL.pid d) = 1) ∧
      (∀ p ∈ I, ∀ q ∈ I, McL.pmul d p q ∈ I ∧ ψ (McL.pmul d p q) = ψ p * ψ q) ∧
      (∀ p ∈ I, McL.Sub.pinv d p ∈ I ∧ ψ (McL.Sub.pinv d p) = (ψ p)⁻¹) ∧
      (∀ p ∈ I, McL.pairOK d p (McL.Sub.pinv d p) = true) ∧
      (∀ W n, (∀ i < n, wLet W i < 2 * g) →
        McL.evalW MG d W n ∈ I ∧ ψ (McL.evalW MG d W n) = bval y W n) := by
  classical
  set z : ℕ → Equiv.Perm (Fin d) := fun i => Dl MG d (2 * i) with hz
  have hword : ∀ W n, (∀ i < n, wLet W i < 2 * g) →
      Val d (McL.evalW MG d W n) ∧ (E d (McL.evalW MG d W n))⁻¹ = bval z W n :=
    fun W n h => word_spec (W := W) hd hgens hg z (fun i _ => rfl) n h
  have hzrel : ∀ r < NR, bval z (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1 := by
    intro r hr
    obtain ⟨-, e⟩ := hword _ (LceS.wLen (REL r)) (hlet r hr)
    have h1 := (LceP.allRec_iff (fun r => Nat.beq (McL.evalW MG d (LceS.wWord (REL r))
      (LceS.wLen (REL r))) (McL.pid d)) NR).1 hrels r hr
    rw [Nat.beq_eq] at h1
    rw [← e, h1, E_pid hd, inv_one]
  set M : Subgroup (Equiv.Perm (Fin d)) := Subgroup.closure (z '' {i | i < g}) with hMdef
  have hzM : ∀ i < g, z i ∈ M := fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hDl : ∀ c < 2 * g, Dl MG d c ∈ M := by
    intro c hc
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
    · have := hzM (c / 2) (by omega)
      change Dl MG d (2 * (c / 2)) ∈ M at this
      rwa [show 2 * (c / 2) = c by omega] at this
    · have := M.inv_mem (hzM (c / 2) (by omega))
      change (Dl MG d (2 * (c / 2)))⁻¹ ∈ M at this
      rwa [show 2 * (c / 2) = c - 1 by omega, ← (gens_spec hd hgens c hc).2 h1] at this
  have hents' := ents_spec hd M hgens hDl hents
  have hcard : N0 ≤ Nat.card M := by
    have step : ∀ l < nLev, ON l * Nat.card (Kc d BP M (l + 1)) ≤ Nat.card (Kc d BP M l) := by
      intro l hl
      obtain ⟨hon, hb⟩ := horb l hl
      set b : Fin d := ⟨McL.Model.bpt BP l, hb⟩
      have hK : Kc d BP M (l + 1) = Kc d BP M l ⊓ MulAction.stabilizer (Equiv.Perm (Fin d)) b := by
        change (if h : McL.Model.bpt BP l < d then _ else _) = _
        simp only [hb, ↓reduceDIte]
        rfl
      have hgen : ∀ gen < 4096, 0 < EP gen → l ≤ McL.Model.dL (ED gen) →
          Val d (EP gen) ∧ (E d (EP gen))⁻¹ ∈ Kc d BP M l := by
        intro gen hgen hpos hlv
        rcases hwrap gen hgen with h0 | ⟨e', he', hEP, hED⟩
        · omega
        obtain ⟨v, m⟩ := hents' e' he'
        rw [hEP]
        exact ⟨v, Kc_anti d BP M (by rw [← hED]; exact hlv) m⟩
      have horbit := orbit_card (Kc d BP M l) b hd (orec_inv (Kc d BP M l) b hd hgen (OM l) (OJ l) _
        (OInv_start (Kc d BP M l) b hd))
      have e : McL.Model.orbitRun EP ED BP l (OM l) (OJ l) = Nat.land (orec EP ED l (OM l) (OJ l)
          (Nat.lor 1 (Nat.lor (Nat.shiftLeft (Nat.shiftLeft 1 b.val) 8) (Nat.shiftLeft b.val 72))))
          (Nat.sub (Nat.shiftLeft 1 72) 1) := rfl
      rw [← e, hon] at horbit
      rw [card_split (Kc d BP M l) b, ← hK]
      exact Nat.mul_le_mul_right _ horbit
    have chain : ∀ k ≤ nLev, (∏ l ∈ Finset.range k, ON l) * Nat.card (Kc d BP M k) ≤ Nat.card M := by
      intro k
      induction k with
      | zero => intro _; simp [Kc]
      | succ k ih =>
        intro hk
        calc (∏ l ∈ Finset.range (k + 1), ON l) * Nat.card (Kc d BP M (k + 1))
            = (∏ l ∈ Finset.range k, ON l) * (ON k * Nat.card (Kc d BP M (k + 1))) := by
              rw [Finset.prod_range_succ, mul_assoc]
          _ ≤ (∏ l ∈ Finset.range k, ON l) * Nat.card (Kc d BP M k) :=
              Nat.mul_le_mul_left _ (step k (by omega))
          _ ≤ Nat.card M := ih (by omega)
    have h1 := chain nLev le_rfl
    have h2 : 1 ≤ Nat.card (Kc d BP M nLev) := Nat.card_pos
    calc N0 ≤ ∏ l ∈ Finset.range nLev, ON l := hprod
      _ ≤ (∏ l ∈ Finset.range nLev, ON l) * Nat.card (Kc d BP M nLev) := Nat.le_mul_of_pos_right _ h2
      _ ≤ Nat.card M := h1
  set rels : Set (FreeGroup ℕ) := relSet REL NR
  set x : ℕ → PresentedGroup rels := fun i => PresentedGroup.of i
  have hxrel : ∀ r < NR, bval x (LceS.wWord (REL r)) (LceS.wLen (REL r)) = 1 := by
    intro r hr
    have e := bval_map (PresentedGroup.mk rels) FreeGroup.of (LceS.wWord (REL r)) (LceS.wLen (REL r))
    change _ = bval x _ _ at e
    rw [← e]
    exact PresentedGroup.one_of_mem ⟨r, hr, rfl⟩
  obtain ⟨hX0, hXN⟩ := hQ (PresentedGroup rels) x hxrel
  set X := Subgroup.closure (x '' {i | i < g})
  have hXfin : Finite X := Nat.finite_of_card_ne_zero hX0
  let μ := PresentedGroup.toGroup (lift_rels z hzrel)
  let π := PresentedGroup.toGroup (lift_rels y hy)
  have hμx : ∀ i, μ (x i) = z i := fun i => PresentedGroup.toGroup.of _
  have hπx : ∀ i, π (x i) = y i := fun i => PresentedGroup.toGroup.of _
  have hmap : X.map μ = M := by
    rw [MonoidHom.map_closure, Set.image_image, hMdef]
    simp only [hμx]
  have hbij : Function.Bijective (μ.subgroupMap X) := by
    refine (MonoidHom.subgroupMap_surjective μ X).bijective_of_nat_card_le ?_
    rw [hmap]
    exact le_trans hXN hcard
  let e := MulEquiv.ofBijective (μ.subgroupMap X) hbij
  have hmem : ∀ σ ∈ M, σ ∈ X.map μ := fun σ h => by rw [hmap]; exact h
  set I : Set ℕ := {p | ∃ σ ∈ M, p = enc d σ}
  let ψ : ℕ → G := fun p => if h : ∃ σ ∈ M, p = enc d σ then
    π (e.symm ⟨(h.choose)⁻¹, hmem _ (M.inv_mem h.choose_spec.1)⟩) else 1
  have hψ : ∀ σ (hσ : σ ∈ M), ψ (enc d σ) = π (e.symm ⟨σ⁻¹, hmem _ (M.inv_mem hσ)⟩) := by
    intro σ hσ
    have h : ∃ τ ∈ M, enc d σ = enc d τ := ⟨σ, hσ, rfl⟩
    have hc : h.choose = σ := (enc_inj hd h.choose_spec.2).symm
    have key : ∀ (τ : Equiv.Perm (Fin d)) (h2 : τ⁻¹ ∈ X.map μ), τ = σ →
        π (e.symm ⟨τ⁻¹, h2⟩) = π (e.symm ⟨σ⁻¹, hmem _ (M.inv_mem hσ)⟩) := by
      rintro τ _ rfl
      rfl
    simp only [ψ, h, ↓reduceDIte]
    exact key _ _ hc
  refine ⟨ψ, I, ⟨⟨1, M.one_mem, (enc_one hd).symm⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [← enc_one hd, hψ 1 M.one_mem]
    have : (⟨(1 : Equiv.Perm (Fin d))⁻¹, hmem _ (M.inv_mem M.one_mem)⟩ : X.map μ) = 1 :=
      Subtype.ext (by simp)
    rw [this, map_one, OneMemClass.coe_one, map_one]
  · rintro p ⟨σ, hσ, rfl⟩ q ⟨τ, hτ, rfl⟩
    rw [enc_mul hd]
    refine ⟨⟨τ * σ, M.mul_mem hτ hσ, rfl⟩, ?_⟩
    rw [hψ _ (M.mul_mem hτ hσ), hψ _ hσ, hψ _ hτ]
    have : (⟨(τ * σ)⁻¹, hmem _ (M.inv_mem (M.mul_mem hτ hσ))⟩ : X.map μ) =
        ⟨σ⁻¹, hmem _ (M.inv_mem hσ)⟩ * ⟨τ⁻¹, hmem _ (M.inv_mem hτ)⟩ :=
      Subtype.ext (by simp)
    rw [this, map_mul, Subgroup.coe_mul, map_mul]
  · rintro p ⟨σ, hσ, rfl⟩
    rw [pinv_enc hd]
    refine ⟨⟨σ⁻¹, M.inv_mem hσ, rfl⟩, ?_⟩
    rw [hψ _ (M.inv_mem hσ), hψ _ hσ]
    have : (⟨σ⁻¹⁻¹, hmem _ (M.inv_mem (M.inv_mem hσ))⟩ : X.map μ) =
        (⟨σ⁻¹, hmem _ (M.inv_mem hσ)⟩)⁻¹ := Subtype.ext (by simp)
    rw [this, map_inv, Subgroup.coe_inv, map_inv]
  · rintro p ⟨σ, hσ, rfl⟩
    rw [pinv_enc hd]
    exact pairOK_enc hd σ
  · intro W n hW
    obtain ⟨v, hE⟩ := hword W n hW
    have hxX : bval x W n ∈ X := bval_mem x X (fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩) n hW
    have hμ : μ (bval x W n) = bval z W n := by
      rw [bval_map]
      simp only [hμx]
    have hEM : E d (McL.evalW MG d W n) ∈ M := by
      have : bval z W n ∈ M := bval_mem z M hzM n hW
      rw [← hE] at this
      simpa using M.inv_mem this
    rw [← enc_E hd v]
    refine ⟨⟨_, hEM, rfl⟩, ?_⟩
    rw [hψ _ hEM]
    have h1 : (⟨(E d (McL.evalW MG d W n))⁻¹, hmem _ (M.inv_mem hEM)⟩ : X.map μ) =
        μ.subgroupMap X ⟨bval x W n, hxX⟩ := Subtype.ext (by
      change (E d (McL.evalW MG d W n))⁻¹ = μ (bval x W n)
      rw [hμ, hE])
    have h2 : e.symm (μ.subgroupMap X ⟨bval x W n, hxX⟩) = ⟨bval x W n, hxX⟩ :=
      (MulEquiv.symm_apply_eq e).2 rfl
    rw [h1, h2]
    change π (bval x W n) = _
    rw [bval_map]
    simp only [hπx]

end CFSG.Certificates.McLM

end
