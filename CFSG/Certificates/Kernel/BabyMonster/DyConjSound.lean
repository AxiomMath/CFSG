module

public import CFSG.Certificates.Kernel.BabyMonster.Native.DyConj
public import CFSG.Certificates.Kernel.BabyMonster.DyLaneFld
public import CFSG.Certificates.Kernel.BabyMonster.DyStab
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KC.BM.Ln

open CFSG.KC.BM CFSG.KC.BM.Dy CFSG.KC.BM.Pkt
open scoped Matrix

@[expose] noncomputable def labMat (x : ℕ) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u =>
  if fld x u % 8192 = t then (if fld x u / 8192 = 1 then -1 else 1) else 0

@[expose] noncomputable def mkMat (T : ℕ) : Matrix (Fin 4371) (Fin 4371) ℚ := fun t u =>
  (kNumMono T t u : ℚ) / 8

@[expose] def LabOK (x : ℕ) : Prop := ∀ u < 4371, fld x u < 16384 ∧ fld x u % 8192 < 4371

@[expose] def MonoOK (Ms : List ℕ) (T NM : ℕ) : Prop :=
  netOK Ms T NM = true ∧ netV Ms T = true ∧ allAligned Ms = true

theorem shifts_dyDs : shifts16 dyDs = true := by decide

theorem xor_8192 {v : ℕ} (hv : v < 16384) :
    (v ^^^ 8192) % 8192 = v % 8192 ∧ (v ^^^ 8192) / 8192 = 1 - v / 8192 ∧ v ^^^ 8192 < 16384 := by
  obtain ⟨h, l, hl, hh, rfl⟩ : ∃ h l, l < 2 ^ 13 ∧ h < 2 ∧ v = 2 ^ 13 * h + l :=
    ⟨v / 8192, v % 8192, Nat.mod_lt _ (by decide), by omega, by have := Nat.div_add_mod v 8192; omega⟩
  have e : (2 ^ 13 * h + l) ^^^ 8192 = 2 ^ 13 * (1 - h) + l := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_xor, show (8192 : ℕ) = 2 ^ 13 from rfl, Nat.testBit_two_pow,
      Nat.testBit_two_pow_mul_add _ hl, Nat.testBit_two_pow_mul_add _ hl]
    by_cases hj : j < 13
    · rw [ite_eq_left hj, ite_eq_left hj, decide_eq_false (by omega), Bool.xor_false]
    · rw [ite_eq_right hj, ite_eq_right hj]
      rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
      · by_cases hj' : j = 13
        · subst hj'
          decide
        · rw [decide_eq_false (Ne.symm hj'), Bool.xor_false, Nat.zero_testBit,
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (1 : ℕ) < 2 ^ 1)
              (Nat.pow_le_pow_right (by decide) (by omega)))]
      · by_cases hj' : j = 13
        · subst hj'
          decide
        · rw [decide_eq_false (Ne.symm hj'), Bool.xor_false, Nat.zero_testBit,
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : (1 : ℕ) < 2 ^ 1)
              (Nat.pow_le_pow_right (by decide) (by omega)))]
  rw [e]
  have hl' : l < 8192 := hl
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp <;> omega

theorem labMat_letter {Ms : List ℕ} {T NM : ℕ} (hM : MonoOK Ms T NM) {x : ℕ} (hx : LabOK x) :
    LabOK (cjLetter Ms NM x) ∧ labMat (cjLetter Ms NM x) = labMat x * mkMat T := by
  obtain ⟨hn, hv, hal⟩ := hM
  obtain ⟨P, Pi, hP, h1, h2, hT, hhi⟩ := mono_net shifts_dyDs hal hn hv
  have hN := (andB_true (andB_true hn).1).2
  obtain ⟨hNal, hNhi⟩ := negMask_facts hN
  have hP43 : ∀ u < 4371, P u < 4371 := by
    intro u hu
    let f : Fin 4371 → Fin 4371 := fun t => ⟨Pi t, (hT t t.2).1⟩
    have hinj : Function.Injective f := fun a b hab => by
      have : Pi a = Pi b := congrArg Fin.val hab
      apply Fin.ext
      rw [← h1 a, ← h1 b, this]
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨u, hu⟩
    have : Pi t = u := congrArg Fin.val ht
    rw [← this, h1]
    exact t.2
  have hmask : ∀ u, fld (Nat.land NM (rep 8192 16 4371)) u =
      if u < 4371 ∧ fld NM u = 65535 then 8192 else 0 := by
    intro u
    change fld (NM &&& rep 8192 16 4371) u = _
    rw [fld_land, fld_rep (by decide)]
    rcases hNal u with h0 | h0
    · rw [h0, Nat.zero_and, ite_eq_right (by omega)]
    · rw [h0]
      by_cases hu : u < 4371
      · rw [ite_eq_left hu, ite_eq_left ⟨hu, rfl⟩]
        rfl
      · rw [ite_eq_right hu, ite_eq_right (fun h => hu h.1), Nat.and_zero]
  have hy : ∀ u, fld (cjLetter Ms NM x) u = fld x (P u) ^^^ (if u < 4371 ∧ fld NM u = 65535 then 8192 else 0) := by
    intro u
    change fld (benes Ms dyDs x ^^^ Nat.land NM (rep 8192 16 4371)) u = _
    rw [fld_xor, hP, hmask]
  have hyu : ∀ u < 4371, fld (cjLetter Ms NM x) u % 8192 = fld x (P u) % 8192 ∧
      fld (cjLetter Ms NM x) u / 8192 = (if fld NM u = 65535 then 1 - fld x (P u) / 8192 else fld x (P u) / 8192) ∧
      fld (cjLetter Ms NM x) u < 16384 := by
    intro u hu
    have hxP := hx (P u) (hP43 u hu)
    rw [hy u]
    by_cases hs : fld NM u = 65535
    · rw [ite_eq_left ⟨hu, hs⟩, ite_eq_left hs]
      exact xor_8192 hxP.1
    · rw [ite_eq_right (fun h => hs h.2), ite_eq_right hs, Nat.xor_zero]
      exact ⟨rfl, rfl, hxP.1⟩
  refine ⟨fun u hu => ⟨(hyu u hu).2.2, by rw [(hyu u hu).1]; exact (hx (P u) (hP43 u hu)).2⟩, ?_⟩
  ext t u
  rw [Matrix.mul_apply]
  have hkN : ∀ (k v : ℕ), kNumMono T k v =
      if v = fld T k % 8192 then (if fld T k / 8192 = 1 then -8 else 8) else 0 := fun _ _ => rfl
  have hk : ∀ k : Fin 4371, k ≠ ⟨P u, hP43 u u.2⟩ → mkMat T k u = 0 := by
    intro k hk
    unfold mkMat
    rw [hkN, ite_eq_right]
    · simp
    · intro e
      apply hk
      apply Fin.ext
      have := (hT k k.2).2.1
      change (k : ℕ) = P (u : ℕ)
      rw [e, this, h1]
  rw [Finset.sum_eq_single ⟨P u, hP43 u u.2⟩ (fun k _ hk' => by rw [hk k hk', mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  have hTP := hT (P u) (hP43 u u.2)
  rw [h2] at hTP
  obtain ⟨-, hTm, hTd⟩ := hTP
  have hmk : mkMat T ⟨P u, hP43 u u.2⟩ u = if fld NM u = 65535 then -1 else 1 := by
    unfold mkMat
    change ((kNumMono T (P u) u : ℤ) : ℚ) / 8 = _
    rw [hkN, hTm, ite_eq_left rfl, hTd]
    split <;> simp
  rw [hmk]
  obtain ⟨hm1, hm2, -⟩ := hyu u u.2
  unfold labMat
  simp only
  rw [hm1, hm2]
  have hb : fld x (P u) / 8192 < 2 := by have := (hx (P u) (hP43 u u.2)).1; omega
  generalize fld x (P u) / 8192 = d at hb ⊢
  rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> by_cases hs : fld NM u = 65535 <;>
    by_cases ht : fld x (P u) % 8192 = (t : ℕ) <;> simp [hs, ht]

theorem labMat_word : ∀ (L : List (List ℕ × ℕ × ℕ)), (∀ l ∈ L, MonoOK l.1 l.2.2 l.2.1) →
    ∀ x, LabOK x → LabOK (cjWord (L.map (·.1)) (L.map (·.2.1)) x) ∧
      labMat (cjWord (L.map (·.1)) (L.map (·.2.1)) x) = labMat x * (L.map (fun l => mkMat l.2.2)).prod
  | [], _, x, hx => ⟨hx, by simp [cjWord]⟩
  | l :: L, hL, x, hx => by
    obtain ⟨h1, h2⟩ := labMat_letter (hL l (List.mem_cons_self ..)) hx
    have e : cjWord ((l :: L).map (·.1)) ((l :: L).map (·.2.1)) x =
        cjWord (L.map (·.1)) (L.map (·.2.1)) (cjLetter l.1 l.2.1 x) := by
      change forceB (cjLetter l.1 l.2.1 x) (fun x' => cjWord (L.map (·.1)) (L.map (·.2.1)) x') = _
      rw [forceB_apply]
    obtain ⟨h3, h4⟩ := labMat_word L (fun l' hl' => hL l' (List.mem_cons_of_mem _ hl')) _ h1
    rw [e, h4, h2, List.map_cons, List.prod_cons, Matrix.mul_assoc]
    exact ⟨h3, rfl⟩

theorem labMat_labels : labMat (labels 0 8192) = 1 := by
  ext t u
  unfold labMat
  rw [labels_lo (by omega), Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Matrix.one_apply]
  by_cases h : (u : ℕ) = t
  · rw [ite_eq_left h, ite_eq_left (Fin.ext h).symm]
    simp
  · rw [ite_eq_right h, ite_eq_right (fun e => h (congrArg Fin.val e).symm)]

theorem labOK_labels : LabOK (labels 0 8192) := fun u hu => by
  rw [labels_lo (by omega)]
  omega

theorem cjRel_sound {A B : List (List ℕ × ℕ × ℕ)} (hA : ∀ l ∈ A, MonoOK l.1 l.2.2 l.2.1)
    (hB : ∀ l ∈ B, MonoOK l.1 l.2.2 l.2.1)
    (h : cjRel (A.map (·.1)) (A.map (·.2.1)) (B.map (·.1)) (B.map (·.2.1)) = true) :
    (A.map (fun l => mkMat l.2.2)).prod = (B.map (fun l => mkMat l.2.2)).prod := by
  have e := Nat.eq_of_beq_eq_true h
  have h1 := (labMat_word A hA _ labOK_labels).2
  have h2 := (labMat_word B hB _ labOK_labels).2
  rw [labMat_labels, Matrix.one_mul] at h1 h2
  rw [← h1, ← h2]
  exact congrArg labMat e

end CFSG.KC.BM.Ln

end
