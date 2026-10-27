module

public import Certificates.Data.Kernel.Str83G5TypeK
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.Stroth.G5.K

private theorem brec_false (x b : Bool) : (Bool.rec false x b : Bool) = (b && x) := by
  cases b <;> rfl

theorem allBelow_eq_true {n : ℕ} {f : ℕ → Bool} : allBelow n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    change (Bool.rec false (f n) (allBelow n f) : Bool) = true ↔ _
    rw [brec_false, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h k hk
      · exact hn
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h n (Nat.lt_succ_self n)⟩

private theorem brec_beq {α : Sort _} (a b : α) (x y : ℕ) :
    (Bool.rec a b (Nat.beq x y) : α) = if x = y then b else a := by
  cases h : Nat.beq x y
  · rw [if_neg (Nat.ne_of_beq_eq_false h)]
  · rw [if_pos (Nat.eq_of_beq_eq_true h)]

private theorem brec_ble {α : Sort _} (a b : α) (x y : ℕ) :
    (Bool.rec a b (Nat.ble x y) : α) = if x ≤ y then b else a := by
  cases h : Nat.ble x y
  · rw [if_neg (fun h' => absurd (Nat.ble_eq_true_of_le h') (by rw [h]; decide))]
  · rw [if_pos (Nat.le_of_ble_eq_true h)]

private theorem brec_true (x b : Bool) : (Bool.rec true x b : Bool) = (!b || x) := by
  cases b <;> rfl

private theorem brec_or (x b : Bool) : (Bool.rec x true b : Bool) = (b || x) := by
  cases b <;> simp

theorem dSK_eq (p : Pattern) (m : ℕ) : dSK p.s2 p.s1 m = p.dS m := by
  simp only [dSK, Pattern.dS, brec_ble]

theorem dLK_eq (p : Pattern) (m : ℕ) : dLK p.l1 m = p.dL m := by
  simp only [dLK, Pattern.dL, brec_ble]

def eDrop (p : Pattern) (m : ℕ) : ℕ := if m % 2 = 1 then p.dL m else p.dS m

def oDrop (p : Pattern) (m : ℕ) : ℕ := if m % 2 = 1 then p.dS m else p.dL m

private theorem nat_mod (a b : ℕ) : Nat.mod a b = a % b := rfl
private theorem nat_div (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem nat_add (a b : ℕ) : Nat.add a b = a + b := rfl
private theorem nat_mul (a b : ℕ) : Nat.mul a b = a * b := rfl
private theorem nat_sub (a b : ℕ) : Nat.sub a b = a - b := rfl

private theorem ble_dec (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · exact (decide_eq_false fun h' => absurd (Nat.ble_eq_true_of_le h') (by rw [h]; decide)).symm
  · exact (decide_eq_true (Nat.le_of_ble_eq_true h)).symm

private theorem beq_dec (a b : ℕ) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · exact (decide_eq_false (Nat.ne_of_beq_eq_false h)).symm
  · exact (decide_eq_true (Nat.eq_of_beq_eq_true h)).symm

theorem eS_eq (p : Pattern) (n : ℕ) :
    p.eS n = (10 : ℤ) - ↑(∑ j ∈ Finset.Ico 1 n, eDrop p j) := by
  unfold Pattern.eS eDrop
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h, Nat.even_iff]

theorem oS_eq (p : Pattern) (n : ℕ) :
    p.oS n = (11 : ℤ) - ↑(∑ j ∈ Finset.Ico 1 n, oDrop p j) := by
  unfold Pattern.oS oDrop
  rw [Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rcases Nat.mod_two_eq_zero_or_one j with h | h <;> simp [h, Nat.even_iff]

@[expose] noncomputable def admStep (s2 s1 l1 : ℕ) (m : ℕ) (acc : ℕ × ℕ × Bool) : ℕ × ℕ × Bool :=
  let a := Bool.rec
    (Nat.add acc.1 (Bool.rec (dSK s2 s1 m) (dLK l1 m) (Nat.beq (Nat.mod m 2) 1))) acc.1
    (Nat.beq m 0)
  let b := Bool.rec
    (Nat.add acc.2.1 (Bool.rec (dLK l1 m) (dSK s2 s1 m) (Nat.beq (Nat.mod m 2) 1))) acc.2.1
    (Nat.beq m 0)
  (a, b, Bool.rec false
    (Bool.rec false
      (Bool.rec true (Nat.beq b (Nat.succ a)) (Nat.beq (Nat.mod m 2) 1))
      (Nat.ble b 11)) (Bool.rec false (Nat.ble a 10) acc.2.2))

theorem admK_eq (s2 s1 l1 : ℕ) : admK s2 s1 l1 =
    Bool.rec false
      (Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true) (admStep s2 s1 l1)
        (Nat.add (Nat.max s1 l1) 2)).2.2
      (Bool.rec false (Bool.rec false (Nat.ble 1 l1) (Nat.ble s2 s1)) (Nat.ble 1 s2)) := rfl

def admAt (p : Pattern) (m : ℕ) : Prop :=
  0 ≤ p.eS m ∧ 0 ≤ p.oS m ∧ (Even m → p.eS m = p.oS m)

theorem admLoop (p : Pattern) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true) (admStep p.s2 p.s1 p.l1) n).1 =
        ∑ j ∈ Finset.Ico 1 n, eDrop p j ∧
      (Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true) (admStep p.s2 p.s1 p.l1) n).2.1 =
        ∑ j ∈ Finset.Ico 1 n, oDrop p j ∧
      ((∀ m, 1 ≤ m → m ≤ n → admAt p m) →
        (Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true) (admStep p.s2 p.s1 p.l1) n).2.2 =
          true) := by
  induction n with
  | zero => exact ⟨rfl, rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [Nat.rec_add_one]
    generalize Nat.rec (motive := fun _ => ℕ × ℕ × Bool) (0, 0, true) (admStep p.s2 p.s1 p.l1) n
      = acc at ih ⊢
    obtain ⟨a, b, c⟩ := acc
    obtain ⟨h1, h2, h3⟩ := ih
    simp only at h1 h2 h3
    subst h1 h2
    have hE : ∑ j ∈ Finset.Ico 1 (n + 1), eDrop p j =
        if n = 0 then ∑ j ∈ Finset.Ico 1 n, eDrop p j else ∑ j ∈ Finset.Ico 1 n, eDrop p j + eDrop p n := by
      split_ifs with hn
      · subst hn
        rfl
      · exact Finset.sum_Ico_succ_top (by omega) _
    have hO : ∑ j ∈ Finset.Ico 1 (n + 1), oDrop p j =
        if n = 0 then ∑ j ∈ Finset.Ico 1 n, oDrop p j else ∑ j ∈ Finset.Ico 1 n, oDrop p j + oDrop p n := by
      split_ifs with hn
      · subst hn
        rfl
      · exact Finset.sum_Ico_succ_top (by omega) _
    simp only [admStep, brec_beq, brec_ble, dSK_eq, dLK_eq, brec_false, brec_true, nat_mod,
      nat_add]
    refine ⟨?_, ?_, fun hadm => ?_⟩
    · rw [hE]
      unfold eDrop
      split_ifs <;> rfl
    · rw [hO]
      unfold oDrop
      split_ifs <;> rfl
    · have hc := h3 fun m h1 h2 => hadm m h1 (by omega)
      obtain ⟨he, ho, hev⟩ := hadm (n + 1) (by omega) le_rfl
      rw [eS_eq, hE] at he hev
      rw [oS_eq, hO] at ho hev
      clear hE hO h3 hadm
      subst hc
      rw [Nat.even_add_one, Nat.not_even_iff_odd, Nat.odd_iff] at hev
      generalize ∑ j ∈ Finset.Ico 1 n, eDrop p j = A at *
      generalize ∑ j ∈ Finset.Ico 1 n, oDrop p j = B at *
      unfold eDrop oDrop at *
      rw [imp_iff_not_or] at hev
      simp only [ble_dec, beq_dec, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      split_ifs at * <;> simp only [decide_eq_true_eq, Bool.false_eq_true, and_true, and_false] <;>
        omega

theorem admK_of (p : Pattern) (hp : p.admissibleB = true) : admK p.s2 p.s1 p.l1 = true := by
  unfold Pattern.admissibleB at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  rw [admK_eq, brec_false, Bool.and_eq_true]
  refine ⟨?_, (admLoop p (Nat.add (Nat.max p.s1 p.l1) 2)).2.2 fun m hm1 hm2 => ?_⟩
  · simp only [brec_false, ble_dec, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2, h3⟩
  · change m ≤ max p.s1 p.l1 + 2 at hm2
    rcases h4 m (by unfold Pattern.J; omega) with h | ⟨⟨he, ho⟩, hev⟩
    · omega
    · exact ⟨he, ho, fun h => hev.resolve_left (not_not.mpr h)⟩

theorem natRec_sum (g : ℕ → ℕ) (n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.add acc (g k)) n : ℕ) =
      ∑ k ∈ Finset.range n, g k := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

theorem sum_Ioc_shift {M : Type*} [AddCommMonoid M] (F : ℤ → M) (a : ℤ) (n : ℕ) :
    ∑ l ∈ Finset.Ioc a (a + n), F l = ∑ k ∈ Finset.range n, F (a + 1 + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : Finset.Ioc a (a + ↑(n + 1)) = insert (a + 1 + n) (Finset.Ioc a (a + n)) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega), Finset.sum_range_succ, ih,
      add_comm]

theorem sum_Ico_shift {M : Type*} [AddCommMonoid M] (F : ℤ → M) (b : ℤ) (n : ℕ) :
    ∑ l ∈ Finset.Ico (b - n) b, F l = ∑ k ∈ Finset.range n, F (b - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : Finset.Ico (b - ↑(n + 1)) b = insert (b - 1 - n) (Finset.Ico (b - n) b) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), Finset.sum_range_succ, ih,
      add_comm]

theorem sum_map_sum {ι : Type*} (S : Finset ι) (M : ι → Multiset Lab) (G : Lab → ℕ) :
    ((∑ i ∈ S, M i).map G).sum = ∑ i ∈ S, ((M i).map G).sum := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp [Finset.sum_cons, ih]

theorem winOK_of (p : Pattern) (G : Lab → ℕ) (f : ℕ → ℕ → ℕ → ℕ) (i d : ℕ) (hd : d ≤ p.J)
    (hf : ∀ (s : Bool) (l : ℤ) (m lo : ℕ), (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1) →
      ((labContrib s l (p.dropAt l m)).map G).sum = f m lo s.toNat)
    (heq : ((p.labR i (i + d)).map G).sum = ((p.labL i (i + d)).map G).sum) :
    winOK f p.J (2 * (p.J + 1)) i d = true := by
  have hR : ∑ k ∈ Finset.range (p.J - d), f (d + 1 + k) (i + d + (k + 1) + 2 * (p.J + 1)) 0 =
      ((p.labR i (i + d)).map G).sum := by
    unfold Pattern.labR
    have hs : (i : ℤ) + p.J = (i + d : ℤ) + ((p.J - d : ℕ) : ℤ) := by omega
    rw [sum_map_sum, hs, sum_Ioc_shift]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hf false ((i : ℤ) + d + 1 + k) _ (i + d + (k + 1) + 2 * (p.J + 1)) (by push_cast; ring)]
    have hm : ((i : ℤ) + d + 1 + k - i).toNat = d + 1 + k := by omega
    rw [hm]
    rfl
  have hL : ∑ k ∈ Finset.range (p.J - d), f (d + 1 + k) (i + 2 * (p.J + 1) - (k + 1)) 1 =
      ((p.labL i (i + d)).map G).sum := by
    unfold Pattern.labL
    have hs : (i : ℤ) + d - p.J = (i : ℤ) - ((p.J - d : ℕ) : ℤ) := by omega
    rw [sum_map_sum, hs, sum_Ico_shift]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hf true ((i : ℤ) - 1 - k) _ (i + 2 * (p.J + 1) - (k + 1)) (by omega)]
    have hm : ((i : ℤ) + d - (i - 1 - k)).toNat = d + 1 + k := by omega
    rw [hm]
    rfl
  unfold winOK
  rw [beq_dec, decide_eq_true_eq, natRec_sum, natRec_sum]
  exact hR.trans (heq.trans hL.symm)

theorem allWin_of (p : Pattern) (τ : AType) (H : Lab → ℕ) (f : ℕ → ℕ → ℕ → ℕ)
    (hf : ∀ (s : Bool) (l : ℤ) (m lo : ℕ), (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1) →
      ((labContrib s l (p.dropAt l m)).map (fun x => H (τ.canon x))).sum = f m lo s.toNat)
    (hpa : τ.passAll p = true) : allWin f p.J = true := by
  unfold AType.passAll Pattern.windowLabs at hpa
  rw [List.all_eq_true] at hpa
  have hw : ∀ i : ℕ, i ≤ 1 → ∀ d ≤ p.J,
      ((p.labR i (i + d)).map (fun x => H (τ.canon x))).sum =
        ((p.labL i (i + d)).map (fun x => H (τ.canon x))).sum := by
    intro i hi d hd
    have hi' : (i : ℤ) ∈ [(0 : ℤ), 1] := by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp
    have h := hpa (p.labR i (i + d), p.labL i (i + d))
      (List.mem_flatMap.mpr ⟨(i : ℤ), hi',
        List.mem_map.mpr ⟨d, by simp <;> omega, rfl⟩⟩)
    rw [decide_eq_true_eq] at h
    have h' := congrArg (fun M => (M.map H).sum) h
    simp only [Multiset.map_map, Function.comp_def] at h'
    exact h'
  change allBelow (p.J + 1) (fun d => Bool.rec false (winOK f p.J (2 * (p.J + 1)) 1 d)
    (winOK f p.J (2 * (p.J + 1)) 0 d)) = true
  rw [allBelow_eq_true]
  intro d hd
  rw [brec_false, Bool.and_eq_true]
  exact ⟨winOK_of p _ f 0 d (by omega) hf (hw 0 (by omega) d (by omega)),
    winOK_of p _ f 1 d (by omega) hf (hw 1 le_rfl d (by omega))⟩

noncomputable def hPsi (c : ℤ) (x : Lab) : ℕ :=
  if x.isPsi then pk (4 * (x.t + c).toNat + 2 * x.neg.toNat + x.ctr.toNat) else 0

noncomputable def hChi (c : ℤ) (x : Lab) : ℕ :=
  if x.isPsi then 0 else pk (4 * (x.t + c).toNat + 2 * x.neg.toNat)

noncomputable def hLin (x : Lab) : ℕ := pk (4 * x.t.toNat + 2 * x.neg.toNat + x.ctr.toNat)

theorem nat_modDiv (N r c : ℕ) (hr : 0 < r) (t : ℤ) (h : (N : ℤ) = t + c * r) :
    N % r = (t % r).toNat ∧ ((N / r : ℕ) : ℤ) = t / r + c := by
  have hr' : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : ((N % r : ℕ) : ℤ) = t % r := by
    rw [Int.natCast_emod, h, Int.add_mul_emod_self_right]
  refine ⟨by omega, ?_⟩
  rw [Int.natCast_ediv, h, Int.add_mul_ediv_right _ _ hr']

theorem redK_spec (J1 r : ℕ) (e ε : Bool) (t : ℤ) (t' : ℕ) (ht : (t' : ℤ) = t + J1) :
    redK J1 r e.toNat t' ε.toNat =
      4 * ((redA r e t ε).1 + if r = 0 then (J1 : ℤ) else 0).toNat +
        2 * (redA r e t ε).2.toNat := by
  cases r with
  | zero =>
    simp only [redA, ↓reduceIte]
    change 4 * t' + 2 * ε.toNat = _
    have h : (t + J1).toNat = t' := by omega
    rw [h]
  | succ r₀ =>
    obtain ⟨h1, h2⟩ := nat_modDiv (t' + J1 * r₀) (r₀ + 1) J1 (Nat.succ_pos _) t
      (by push_cast; rw [ht]; ring)
    simp only [redA, Nat.add_one_ne_zero, ↓reduceIte, add_zero]
    change 4 * ((t' + J1 * r₀) % (r₀ + 1)) +
      2 * ((ε.toNat + e.toNat * (((t' + J1 * r₀) / (r₀ + 1) + J1) % 2)) % 2) = _
    rw [h1]
    generalize (t' + J1 * r₀) / (r₀ + 1) = Q at h2 ⊢
    generalize t / ((r₀ + 1 : ℕ) : ℤ) = q at h2 ⊢
    rcases Int.emod_two_eq q with hq | hq
    · have hQ : (Q + J1) % 2 = 0 := by omega
      have hodd : ¬ Odd q := by rw [Int.odd_iff]; omega
      rw [hQ]
      cases e <;> cases ε <;> simp [hodd]
    · have hQ : (Q + J1) % 2 = 1 := by omega
      have hodd : Odd q := by rw [Int.odd_iff]; omega
      rw [hQ]
      cases e <;> cases ε <;> simp [hodd]

theorem psi_step (p : Pattern) (r : ℕ) (e : Bool) (r' : ℕ) (e' : Bool) (s : Bool) (l : ℤ)
    (m lo : ℕ) (hlo : (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1)) :
    ((labContrib s l (p.dropAt l m)).map (fun x => hPsi (if r = 0 then ((p.J + 1 : ℕ) : ℤ) else 0)
      ((AType.unlinked r e r' e').canon x))).sum =
      psiStep (p.J + 1) r e.toNat p.s2 p.s1 m lo s.toNat := by
  have hb : ∀ δ : Bool, hPsi (if r = 0 then ((p.J + 1 : ℕ) : ℤ) else 0)
      ((AType.unlinked r e r' e').canon ⟨true, l / 2, s, δ⟩) =
        pk (redK (p.J + 1) r e.toNat (lo / 2) s.toNat + δ.toNat) := by
    intro δ
    rw [redK_spec (p.J + 1) r e s (l / 2) (lo / 2) (by push_cast; omega)]
    simp only [AType.canon, hPsi, ↓reduceIte]
  generalize (if r = 0 then ((p.J + 1 : ℕ) : ℤ) else 0) = c at hb ⊢
  unfold psiStep labContrib Pattern.dropAt
  simp only [brec_beq, nat_mod, nat_div, nat_add, dSK_eq]
  by_cases hl : Even l
  · have h0 : lo % 2 = 0 := by obtain ⟨k, hk⟩ := hl; omega
    simp only [hl, h0, ↓reduceIte]
    split_ifs <;> simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero, hb,
      Bool.toNat_false, Bool.toNat_true, add_zero]
  · have h0 : lo % 2 = 1 := by
      rw [Int.not_even_iff_odd] at hl
      obtain ⟨k, hk⟩ := hl
      omega
    simp only [hl, h0, ↓reduceIte, Nat.one_ne_zero]
    split_ifs <;> simp [AType.canon, hPsi]

theorem chi_step (p : Pattern) (r : ℕ) (e : Bool) (r' : ℕ) (e' : Bool) (s : Bool) (l : ℤ)
    (m lo : ℕ) (hlo : (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1)) :
    ((labContrib s l (p.dropAt l m)).map (fun x => hChi (if r' = 0 then ((p.J + 1 : ℕ) : ℤ) else 0)
      ((AType.unlinked r e r' e').canon x))).sum =
      chiStep (p.J + 1) r' e'.toNat p.l1 m lo s.toNat := by
  have hb : ¬ Even l → hChi (if r' = 0 then ((p.J + 1 : ℕ) : ℤ) else 0)
      ((AType.unlinked r e r' e').canon ⟨false, (l - 1) / 2, s, false⟩) =
        pk (redK (p.J + 1) r' e'.toNat (lo / 2) s.toNat) := by
    intro hl
    rw [Int.not_even_iff_odd] at hl
    obtain ⟨k, hk⟩ := hl
    rw [redK_spec (p.J + 1) r' e' s ((l - 1) / 2) (lo / 2) (by push_cast; omega)]
    simp only [AType.canon, hChi, ↓reduceIte, Bool.false_eq_true]
  generalize (if r' = 0 then ((p.J + 1 : ℕ) : ℤ) else 0) = c at hb ⊢
  unfold chiStep labContrib Pattern.dropAt
  simp only [brec_beq, nat_mod, nat_div, dLK_eq]
  by_cases hl : Even l
  · have h0 : lo % 2 = 0 := by obtain ⟨k, hk⟩ := hl; omega
    simp only [hl, h0, ↓reduceIte]
    split_ifs <;> simp [AType.canon, hChi]
  · have h0 : lo % 2 = 1 := by
      rw [Int.not_even_iff_odd] at hl
      obtain ⟨k, hk⟩ := hl
      omega
    simp only [hl, h0, ↓reduceIte, Nat.one_ne_zero]
    split_ifs
    · simp only [Multiset.map_singleton, Multiset.sum_singleton]
      exact hb hl
    · simp

theorem lin_step (p : Pattern) (k : ℕ) (ε δ : Bool) (s : Bool) (l : ℤ)
    (m lo : ℕ) (hlo : (lo : ℤ) = l + 2 * ((p.J : ℤ) + 1)) :
    ((labContrib s l (p.dropAt l m)).map
      (fun x => hLin ((AType.linked (2 * k + 1) ε δ).canon x))).sum =
      linStep (p.J + 1) (2 * k + 1) ε.toNat δ.toNat p.s2 p.s1 p.l1 m lo s.toNat := by
  have hk : 2 * k + 1 - 1 = 2 * k := by omega
  unfold linStep labContrib Pattern.dropAt
  simp only [brec_beq, nat_mod, nat_div, nat_add, nat_mul, nat_sub, Nat.succ_eq_add_one, dSK_eq,
    dLK_eq, hk]
  by_cases hl : Even l
  · have h0 : lo % 2 = 0 := by obtain ⟨k, hk⟩ := hl; omega
    have hJ : (lo : ℤ) / 2 = l / 2 + ((p.J : ℤ) + 1) := by obtain ⟨k, hk⟩ := hl; omega
    obtain ⟨hx, -⟩ := nat_modDiv (lo / 2 + (p.J + 1) * (2 * k)) (2 * k + 1) (p.J + 1) (by omega)
      (l / 2) (by push_cast; rw [hJ]; ring)
    simp only [hl, h0, ↓reduceIte, hx]
    split_ifs <;> simp [AType.canon, hLin, add_assoc]
  · have h0 : lo % 2 = 1 := by
      rw [Int.not_even_iff_odd] at hl
      obtain ⟨k, hk⟩ := hl
      omega
    have hJ : (lo : ℤ) / 2 = (l - 1) / 2 + ((p.J : ℤ) + 1) := by
      rw [Int.not_even_iff_odd] at hl
      obtain ⟨k, hk⟩ := hl
      omega
    obtain ⟨hx, -⟩ := nat_modDiv (lo / 2 + (p.J + 1) * (2 * k) + (2 * k + 1 + 1) / 2) (2 * k + 1)
      (p.J + 1) (by omega) ((l - 1) / 2 + ((2 * k + 1 + 1) / 2 : ℕ))
      (by push_cast; rw [hJ]; ring)
    simp only [hl, h0, ↓reduceIte, Nat.one_ne_zero, hx]
    split_ifs
    · simp only [Multiset.map_singleton, Multiset.sum_singleton, AType.canon, hLin]
      congr 2
      cases s <;> cases ε <;> rfl
    · simp

theorem brec_true_of {x b : Bool} (h : (Bool.rec true x b : Bool) = true) (hb : b = true) :
    x = true := by
  subst hb
  exact h

theorem memP_eq (r r' : ℕ) : memP r r' = decide ((r, r') ∈ pairs30) := by
  unfold memP
  generalize pairs30 = L
  induction L with
  | nil => rfl
  | cons x L ih =>
    dsimp only
    rw [ih]
    obtain ⟨a, b⟩ := x
    simp only [beq_dec, List.mem_cons, Prod.mk.injEq]
    by_cases ha : a = r
    · by_cases hb : b = r'
      · subst ha hb
        simp
      · simp [ha, hb, Ne.symm hb]
    · simp [ha, Ne.symm ha]

theorem isP_eq (p : Pattern) (a b c : ℕ) : isP p a b c = decide (p = ⟨a, b, c⟩) := by
  obtain ⟨s2, s1, l1⟩ := p
  simp [isP, beq_dec, brec_false, Pattern.mk.injEq]

theorem okK_eq (p : Pattern) (r r' : ℕ) (e e' : Bool) :
    okK p r e.toNat r' e'.toNat = okType p (.unlinked r e r' e') := by
  cases e
  · simp [okK, okType, brec_false, beq_dec]
  cases e'
  · simp [okK, okType, brec_false, beq_dec]
  simp only [okK, okType, brec_false, brec_true, brec_or, beq_dec, memP_eq, isP_eq,
    Bool.toNat_true]
  generalize decide ((r, r') ∈ pairs30) = M
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not, Prod.mk.injEq, true_and, and_true, Bool.and_eq_false_iff,
    Bool.or_eq_false_iff]
  simp only [Pattern.p16, Pattern.p17, Pattern.p18, Pattern.p20, Pattern.target]
  tauto

theorem chkK_sound (p : Pattern) (hp : p.admissibleB = true)
    (h : (Bool.rec true (chkK p) (admK p.s2 p.s1 p.l1) : Bool) = true) :
    ((typeList (p.J + 2)).all fun τ => !τ.passAll p || okType p τ) = true := by
  rw [admK_of p hp] at h
  change chkK p = true at h
  unfold chkK chkG at h
  rw [brec_false, Bool.and_eq_true] at h
  obtain ⟨hlin, hall⟩ := h
  rw [List.all_eq_true]
  intro τ hτ
  rw [Bool.or_eq_true, Bool.not_eq_true']
  by_cases hpa : τ.passAll p = true
  · right
    unfold typeList at hτ
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hτ
    rcases hτ with ⟨r, hr, e, he, r', hr', e', he', rfl⟩ | ⟨_, ⟨k, hk, rfl⟩, ε₀, -, δ₀, -, rfl⟩
    · have hbits : ∀ (r : ℕ) (e : Bool), e ∈ (if r = 0 then [false] else [false, true]) →
          e.toNat < nbits r := by
        intro r e he
        rw [nbits, brec_beq]
        split_ifs at he ⊢ <;> cases e <;> simp_all
      have h1 := allBelow_eq_true.mp (allBelow_eq_true.mp hall r (by change r < p.J + 3; omega))
        e.toNat (hbits r e he)
      have h2 := brec_true_of h1 (allWin_of p _ _ _ (psi_step p r e r' e') hpa)
      have h3 := allBelow_eq_true.mp (allBelow_eq_true.mp h2 r' (by change r' < p.J + 3; omega))
        e'.toNat (hbits r' e' he')
      rw [← okK_eq]
      exact brec_true_of h3 (allWin_of p _ _ _ (chi_step p r e r' e') hpa)
    · exfalso
      have h1 := allBelow_eq_true.mp (allBelow_eq_true.mp hlin k (by change k < p.J + 3; omega))
        (2 * ε₀.toNat + δ₀.toNat) (by cases ε₀ <;> cases δ₀ <;> decide)
      have h1' : Bool.not (allWin (linStep (p.J + 1) (2 * k + 1) ε₀.toNat δ₀.toNat p.s2 p.s1 p.l1)
          p.J) = true := by
        cases ε₀ <;> cases δ₀ <;> exact h1
      rw [allWin_of p _ _ _ (lin_step p k ε₀ δ₀) hpa] at h1'
      exact absurd h1' (by decide)
  · left
    simpa using hpa

theorem typeCheck_of_fullK (h : fullK = true) : typeCheck () = true := by
  unfold typeCheck admissibleList
  rw [List.all_eq_true]
  intro p hp
  rw [List.mem_filter] at hp
  obtain ⟨hp, hadm⟩ := hp
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hp
  obtain ⟨s1, hs1, s2, hs2, l1, hl1, rfl⟩ := hp
  exact chkK_sound _ hadm
    (allBelow_eq_true.mp (allBelow_eq_true.mp (allBelow_eq_true.mp h s1 hs1) s2 hs2) l1 hl1)

end CFSG.Quasithin.Stroth.G5.K

end
