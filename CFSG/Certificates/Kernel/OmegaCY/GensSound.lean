module

public import CFSG.Certificates.Kernel.OmegaCY.Hom
public import Certificates.Data.Kernel.OmegaCY.Gens
public import CFSG.Certificates.Kernel.OrbFindSound
public import CFSG.Certificates.Kernel.A45Cls.PockSound
public import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.OmegaCY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls

theorem tab_bit {tab : ℕ} (ht : tabOK tab = true) {b : ℕ}
    (hb : (7890336234772365312 : ℕ).testBit b = false) : tab.testBit b = false := by
  have e : tab ||| 7890336234772365312 = 7890336234772365312 := Nat.eq_of_beq_eq_true ht
  have := congrArg (fun x => x.testBit b) e
  simp only [Nat.testBit_or, hb, Bool.or_false] at this
  exact this

theorem cg_bit (tab i j k : ℕ) :
    (cg tab i j).testBit k = (tab.testBit (3 * (i * (i - 1) / 2 + j) + k) && decide (k < 3)) := by
  change ((tab >>> (3 * (i * (i - 1) / 2 + j))) &&& (2 ^ 3 - 1)).testBit k = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]

theorem mask_lo : ∀ i < 7, ∀ j < i, j < 3 → ∀ k < 3,
    (7890336234772365312 : ℕ).testBit (3 * (i * (i - 1) / 2 + j) + k) = false := by
  decide

theorem mask_b0 : ∀ i < 7, ∀ j < i,
    (7890336234772365312 : ℕ).testBit (3 * (i * (i - 1) / 2 + j) + 0) = false := by
  decide

theorem cg_zero {tab : ℕ} (ht : tabOK tab = true) {i j : ℕ} (hi : i < 7) (hj : j < i)
    (hj3 : j < 3) : cg tab i j = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [cg_bit, Nat.zero_testBit]
  by_cases hk : k < 3
  · rw [tab_bit ht (mask_lo i hi j hj hj3 k hk), Bool.false_and]
  · simp [hk]

theorem cg_bit0 {tab : ℕ} (ht : tabOK tab = true) {i j : ℕ} (hi : i < 7) (hj : j < i) :
    (cg tab i j).testBit 0 = false := by
  rw [cg_bit, tab_bit ht (mask_b0 i hi j hj), Bool.false_and]

theorem bf_two_pow {tab : ℕ} (ht : tabOK tab = true) : ∀ i < 7, ∀ j < i,
    bf tab (2 ^ i) (2 ^ j) = cg tab i j := by
  intro i hi j hj
  have z : ∀ i' j', i' < 7 → j' < i' → j' < 3 → 0 = cg tab i' j' :=
    fun i' j' h1 h2 h3 => (cg_zero ht h1 h2 h3).symm
  interval_cases i <;> interval_cases j <;>
    simp +decide [bf_eq, bfT_eq] <;> first | rfl | exact z _ _ (by omega) (by omega) (by omega)

theorem allR_iff {m : ℕ} {f : ℕ → Bool} : allR m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    have e : allR (m + 1) f = (f m && allR m f) := cy_bAndD _ _
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases him : i = m
      · rw [him]
        exact h1
      · exact h2 i (by omega)
    · intro h
      exact ⟨h m (by omega), fun i hi => h i (by omega)⟩

variable {n w : ℕ}

@[expose] noncomputable def psP (n w : ℕ) (G : ℕ → ℕ) (k m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (pidn n w)
    (fun i r => nIf(bt k i, pcomp n w (mask w) r (G (Nat.succ i)), r)) m

theorem psP_succ (G : ℕ → ℕ) (k m : ℕ) : psP n w G k (m + 1) =
    nIf(bt k m, pcomp n w (mask w) (psP n w G k m) (G (m + 1)), psP n w G k m) := rfl

theorem psiS_eq (G : ℕ → ℕ) (k : ℕ) : psiS n w G k = psP n w G k 6 := rfl

theorem prep_psiS (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : ℕ → ℕ}
    {σ : ℕ → Equiv.Perm (Fin n)} (hG : ∀ i < 6, PRep n w (G (i + 1)) (σ (i + 1))) (k : ℕ) :
    PRep n w (psiS n w G k) (psiG (fun i => σ (i + 1)) k 6) := by
  have hn' : n < 2 ^ 32 := lt_trans hn (by norm_num)
  have key : ∀ m ≤ 6, PRep n w (psP n w G k m) (psiG (fun i => σ (i + 1)) k m) := by
    intro m hm
    induction m with
    | zero =>
      rw [psiG_zero]
      exact prep_pidn hn hw
    | succ m ih =>
      rw [psiG_succ, psP_succ, cy_nIfD, bt_eq]
      cases hb : k.testBit m
      · simpa using ih (by omega)
      · simpa using prep_pcomp hn' (ih (by omega)) (hG m (by omega))
  rw [psiS_eq]
  exact key 6 le_rfl

theorem prep_cenS (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : ℕ → ℕ}
    {σ : ℕ → Equiv.Perm (Fin n)} (hG : ∀ i < 6, PRep n w (G (i + 1)) (σ (i + 1))) (v : ℕ) :
    PRep n w (cenS n w G v)
      ((if v.testBit 1 = true then σ 1 else 1) * (if v.testBit 2 = true then σ 2 else 1)) := by
  have hn' : n < 2 ^ 32 := lt_trans hn (by norm_num)
  unfold cenS
  rw [cy_nIfD, cy_nIfD, bt_eq, bt_eq]
  refine prep_pcomp hn' ?_ ?_
  · split
    · exact hG 0 (by norm_num)
    · exact prep_pidn hn hw
  · split
    · exact hG 1 (by norm_num)
    · exact prep_pidn hn hw

@[expose] def cyGen (σ : ℕ → Equiv.Perm (Fin n)) (i : ℕ) : Equiv.Perm (Fin n) × ℤˣ :=
  if i = 0 then (1, -1) else (σ i, 1)

theorem swap_eq {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1) :
    a * b = b * a * (a * b * (a * b)) := by
  simp only [← mul_assoc]
  rw [mul_assoc b a a, ha, mul_one, hb, one_mul]

theorem comm_of_sq {M : Type*} [Group M] {a b : M} (ha : a * a = 1) (hb : b * b = 1)
    (h : a * b * (a * b) = 1) : a * b = b * a := by
  have e := swap_eq ha hb
  rwa [h, mul_one] at e

theorem psiG_fst {M N : Type*} [Group M] [Group N] (h : ℕ → M × N) (k : ℕ) :
    ∀ m, (psiG h k m).1 = psiG (fun i => (h i).1) k m
  | 0 => by rw [psiG_zero, psiG_zero, Prod.fst_one]
  | m + 1 => by
    rw [psiG_succ, psiG_succ, Prod.fst_mul, psiG_fst h k m]
    split <;> rfl

theorem psiG_snd {M N : Type*} [Group M] [Group N] (h : ℕ → M × N) (k : ℕ) :
    ∀ m, (psiG h k m).2 = psiG (fun i => (h i).2) k m
  | 0 => by rw [psiG_zero, psiG_zero, Prod.snd_one]
  | m + 1 => by
    rw [psiG_succ, psiG_succ, Prod.snd_mul, psiG_snd h k m]
    split <;> rfl

theorem psiG_shift {M : Type*} [Group M] (h : ℕ → M) (k : ℕ) : ∀ m,
    psiG h k (m + 1) = (if k.testBit 0 = true then h 0 else 1) * psiG (fun i => h (i + 1)) (k / 2) m
  | 0 => by rw [psiG_succ, psiG_zero, psiG_zero, one_mul, mul_one]
  | m + 1 => by
    rw [psiG_succ k (m + 1), psiG_shift h k m, psiG_succ (k / 2) m, Nat.testBit_div_two, mul_assoc]

theorem psiG_one {M : Type*} [Group M] (k : ℕ) : ∀ m, psiG (fun _ => (1 : M)) k m = 1
  | 0 => psiG_zero k
  | m + 1 => by
    rw [psiG_succ, psiG_one k m]
    split <;> simp

theorem psi3_cyGen (σ : ℕ → Equiv.Perm (Fin n)) {e : ℕ} (he : e.testBit 0 = false) :
    psiG (cyGen σ) e 3 =
      ((if e.testBit 1 = true then σ 1 else 1) * (if e.testBit 2 = true then σ 2 else 1), 1) := by
  rw [psiG_succ, psiG_succ, psiG_succ, psiG_zero, he]
  cases e.testBit 1 <;> cases e.testBit 2 <;> simp [cyGen, Prod.ext_iff]

theorem gensK_sound (hn : n < 16777216) (hw : n + 1 < 2 ^ w) {G : ℕ → ℕ}
    {σ : ℕ → Equiv.Perm (Fin n)} (hG : ∀ i < 6, PRep n w (G (i + 1)) (σ (i + 1))) {tab : ℕ}
    (h : gensK n w G tab = true) :
    CyRel tab (cyGen σ) ∧ ∀ k, 0 < k → k < 2 ^ 7 → psiG (cyGen σ) k 7 ≠ 1 := by
  have hn' : n < 2 ^ 32 := lt_trans hn (by norm_num)
  unfold gensK at h
  simp only [cy_bAndD, Bool.and_eq_true, allR_iff] at h
  obtain ⟨ht, hsq0, hcm0, hid0⟩ := h
  have hGi : ∀ i, 1 ≤ i → i < 7 → PRep n w (G i) (σ i) := by
    intro i h1 h7
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact hG i' (by omega)
  have hsq : ∀ i, 1 ≤ i → i < 7 → σ i * σ i = 1 := by
    intro i h1 h7
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    exact (isIdK_iff (prep_pcomp hn' (hG i' (by omega)) (hG i' (by omega)))).1 (hsq0 i' (by omega))
  have hcm : ∀ i < 7, ∀ j < i, j ≠ 0 → σ i * σ j * (σ i * σ j) =
      (if (cg tab i j).testBit 1 = true then σ 1 else 1) *
        (if (cg tab i j).testBit 2 = true then σ 2 else 1) := by
    intro i hi j hj hj0
    have e := hcm0 i hi j hj
    rw [bIf_eq, if_neg (by simpa using hj0)] at e
    have hp := prep_pcomp hn' (hGi i (by omega) hi) (hGi j (by omega) (by omega))
    simpa using eq22_sound e (prep_pcomp hn' hp hp) (prep_pidn hn hw) (prep_cenS hn hw hG _)
      (prep_pidn hn hw)
  have hcz : ∀ i < 7, ∀ j < i, j ≠ 0 → j < 3 → σ i * σ j = σ j * σ i := by
    intro i hi j hj hj0 hj3
    have e := hcm i hi j hj hj0
    rw [cg_zero ht hi hj hj3, Nat.zero_testBit] at e
    exact comm_of_sq (hsq i (by omega) hi) (hsq j (by omega) (by omega)) (by simpa using e)
  have hfst : ∀ i k, i < 3 → k < 7 → (cyGen σ i).1 * (cyGen σ k).1 = (cyGen σ k).1 * (cyGen σ i).1 := by
    intro i k hi hk
    by_cases hi0 : i = 0
    · simp [cyGen, hi0]
    by_cases hk0 : k = 0
    · simp [cyGen, hk0]
    simp only [cyGen, hi0, hk0, if_false]
    rcases lt_trichotomy i k with hik | rfl | hik
    · exact (hcz k hk i hik hi0 hi).symm
    · rfl
    · exact hcz i (by omega) k hik hk0 (by omega)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    by_cases hi0 : i = 0
    · simp [cyGen, hi0, Int.units_mul_self]
    · simp only [cyGen, hi0, if_false]
      rw [Prod.mk_mul_mk, hsq i (by omega) hi, mul_one]
      rfl
  · intro i hi k hk
    exact Prod.ext (hfst i k hi hk) (mul_comm _ _)
  · intro i hi j hj
    rw [bf_two_pow ht i hi j hj, psi3_cyGen σ (cg_bit0 ht hi hj)]
    by_cases hj0 : j = 0
    · subst hj0
      rw [cg_zero ht hi hj (by norm_num)]
      simp [cyGen, show i ≠ 0 by omega]
    · have hi0 : i ≠ 0 := by omega
      simp only [cyGen, hi0, hj0, if_false, Prod.mk_mul_mk, mul_one]
      rw [← hcm i hi j hj hj0]
      exact congrArg (·, (1 : ℤˣ)) (swap_eq (hsq i (by omega) hi) (hsq j (by omega) (by omega)))
  · intro k hk0 hk h1
    have hs := congrArg Prod.snd h1
    have hf := congrArg Prod.fst h1
    rw [psiG_snd, psiG_shift] at hs
    rw [psiG_fst, psiG_shift] at hf
    have e2 : ∀ i, (cyGen σ (i + 1)).2 = 1 := fun i => by simp [cyGen]
    have e1 : ∀ i, (cyGen σ (i + 1)).1 = σ (i + 1) := fun i => by simp [cyGen]
    simp only [e2] at hs
    rw [psiG_one, mul_one] at hs
    simp only [e1] at hf
    have hb0 : k.testBit 0 = false := by
      cases hb : k.testBit 0
      · rfl
      · rw [hb] at hs
        simp [cyGen] at hs <;> exact absurd hs (by decide)
    rw [hb0] at hf
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, Prod.fst_one] at hf
    have hk2 : k / 2 = 0 := by
      by_contra hne
      obtain ⟨m, hm⟩ : ∃ m, k / 2 = m + 1 := ⟨k / 2 - 1, by omega⟩
      have e := hid0 m (by omega)
      have hid : isIdK n w (psiS n w G (Nat.succ m)) = true :=
        (isIdK_iff (prep_psiS hn hw hG _)).2 (by rw [Nat.succ_eq_add_one, ← hm]; exact hf)
      rw [hid] at e
      exact absurd e (by decide)
    have : k % 2 = 0 := by
      rw [Nat.testBit_zero] at hb0
      simpa using hb0
    omega

theorem caseK_parts {B BT : ℕ → ℕ} {z x tab : ℕ} (h : caseK n w B BT z x tab = true) :
    eqP n w z (genOf n w B BT x 1) = true ∧ eqP n w (BT (ixF x 4)) (genOf n w B BT x 1) = true ∧
      eqP n w (BT (ixF x 5)) (genOf n w B BT x 2) = true ∧ gensK n w (genOf n w B BT x) tab = true := by
  unfold caseK at h
  simpa only [cy_bAndD, Bool.and_eq_true] using h

end CFSG.KC.OmegaCY

end
