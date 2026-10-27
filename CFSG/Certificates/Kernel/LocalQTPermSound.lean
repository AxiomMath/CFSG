module

public import Certificates.Data.Kernel.LocalQT.Perm
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.KC.LQT.P

open Equiv Finset CFSG.KC.Ord

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem orB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem notB_iff {a : Bool} : notB a = true ↔ ¬ a = true := by
  cases a <;> simp [notB]

theorem impB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> simp [impB]

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem allN_iff (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => simp [allN]
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      exacts [h2 i hi, h1]
    · exact fun h => ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem anyN_iff (m : ℕ) (f : ℕ → Bool) : anyN m f = true ↔ ∃ i < m, f i = true := by
  induction m with
  | zero => simp [anyN]
  | succ m ih =>
    change orB (f m) (anyN m f) = true ↔ _
    rw [orB_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      exacts [⟨m, Nat.lt_succ_self m, h⟩, ⟨i, Nat.lt_succ_of_lt hi, h⟩]
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      exacts [Or.inr ⟨i, hi, h⟩, Or.inl h]

theorem allL_iff (L : List ℕ) (f : ℕ → Bool) : allL L f = true ↔ ∀ x ∈ L, f x = true := by
  induction L with
  | nil => simp [allL]
  | cons x L ih =>
    change andB (f x) (allL L f) = true ↔ _
    rw [andB_iff, ih]
    simp

theorem anyL_iff (L : List ℕ) (f : ℕ → Bool) : anyL L f = true ↔ ∃ x ∈ L, f x = true := by
  induction L with
  | nil => simp [anyL]
  | cons x L ih =>
    change orB (f x) (anyL L f) = true ↔ _
    rw [orB_iff, ih]
    simp

theorem allN_fin (m : ℕ) (f : ℕ → Bool) : allN m f = true ↔ ∀ i : Fin m, f i = true := by
  rw [allN_iff]
  exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i, hi⟩⟩

theorem anyN_fin (m : ℕ) (f : ℕ → Bool) : anyN m f = true ↔ ∃ i : Fin m, f i = true := by
  rw [anyN_iff]
  exact ⟨fun ⟨i, hi, h⟩ => ⟨⟨i, hi⟩, h⟩, fun ⟨i, h⟩ => ⟨i, i.isLt, h⟩⟩

theorem beq_fin {m : ℕ} (a b : Fin m) : Nat.beq a b = true ↔ a = b := by
  rw [beq_iff, Fin.val_inj]

def E (f : ℕ → ℕ) (m : ℕ) : ℕ := ∑ i ∈ range m, f i * 32 ^ i

theorem E_zero (f : ℕ → ℕ) : E f 0 = 0 := by simp [E]

theorem E_succ (f : ℕ → ℕ) (m : ℕ) : E f (m + 1) = E f m + f m * 32 ^ m := by
  rw [E, sum_range_succ, ← E]

theorem E_congr {f g : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i = g i) : E f m = E g m :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

theorem E_lt {f : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i < 32) : E f m < 32 ^ m := by
  induction m with
  | zero => simp [E]
  | succ m ih =>
    rw [E_succ, pow_succ]
    have h1 := ih fun i hi => h i (by omega)
    have h2 : f m * 32 ^ m ≤ 31 * 32 ^ m := Nat.mul_le_mul_right _ (by have := h m (by omega); omega)
    omega

theorem E_digit {f : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i < 32) {j : ℕ} (hj : j < m) :
    E f m / 32 ^ j % 32 = f j := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [E_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · have e : f m * 32 ^ m = (f m * 32 ^ (m - j - 1)) * 32 * 32 ^ j := by
        rw [mul_assoc, mul_assoc, ← pow_succ', ← pow_add]
        congr 2
        omega
      rw [e, Nat.add_mul_div_right _ _ (by positivity),
        Nat.add_mul_mod_self_right]
      exact ih (fun i hi => h i (by omega)) hj
    · rw [Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (E_lt fun i hi => h i (by omega)), zero_add]
      exact Nat.mod_eq_of_lt (h j (by omega))

theorem E_succ_left (f : ℕ → ℕ) (m : ℕ) : E f (m + 1) = f 0 + 32 * E (fun k => f (k + 1)) m := by
  rw [E, sum_range_succ', E, mul_sum]
  simp only [pow_zero, mul_one, pow_succ]
  rw [add_comm]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [mul_comm (32 ^ i) 32, mul_left_comm]

theorem img_eq (s i : ℕ) : img s i = s / 32 ^ i % 32 := by
  change (s >>> (5 * i)) &&& (2 ^ 5 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  rfl

theorem shl_eq (v k : ℕ) : Nat.shiftLeft v (Nat.mul 5 k) = v * 32 ^ k := by
  change v <<< (5 * k) = _
  rw [Nat.shiftLeft_eq, pow_mul]
  rfl

theorem rec_sum (g : ℕ → ℕ) (n : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (g i)) n = ∑ i ∈ range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (g i)) n) (g n) = _
    rw [ih, sum_range_succ]
    rfl

theorem ofFn_eq (n : ℕ) (g : ℕ → ℕ) : ofFn n g = E g n := by
  rw [ofFn, E, ← rec_sum]
  congr 1
  funext i acc
  rw [shl_eq]

variable {n : ℕ}

@[expose] def code (σ : Perm (Fin n)) : ℕ :=
  ((List.finRange n).map fun i => (σ i : ℕ) * 32 ^ (i : ℕ)).sum

def vals (σ : Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then σ ⟨i, h⟩ else 0

theorem vals_lt (hn : n ≤ 32) (σ : Perm (Fin n)) : ∀ i < n, vals σ i < 32 := fun i hi => by
  have := (σ ⟨i, hi⟩).isLt
  simp only [vals, hi, ↓reduceDIte]
  omega

theorem vals_fin (σ : Perm (Fin n)) (i : Fin n) : vals σ i = σ i := by
  simp [vals, i.isLt]

theorem code_fin (σ : Perm (Fin n)) : code σ = ∑ i : Fin n, (σ i : ℕ) * 32 ^ (i : ℕ) := by
  rw [code, ← Fin.sum_univ_def]

theorem code_eq (σ : Perm (Fin n)) : code σ = E (vals σ) n := by
  rw [code_fin, E, ← Fin.sum_univ_eq_sum_range (fun i => vals σ i * 32 ^ i)]
  refine sum_congr rfl fun i _ => ?_
  rw [vals_fin]

theorem img_code' (hn : n ≤ 32) (σ : Perm (Fin n)) {i : ℕ} (hi : i < n) :
    img (code σ) i = vals σ i := by
  rw [img_eq, code_eq, E_digit (vals_lt hn σ) hi]

theorem img_code (hn : n ≤ 32) (σ : Perm (Fin n)) (i : Fin n) : img (code σ) i = σ i := by
  rw [img_code' hn σ i.isLt, vals_fin]

theorem code_inj (hn : n ≤ 32) {σ τ : Perm (Fin n)} (h : code σ = code τ) : σ = τ := by
  ext i
  have := img_code hn σ i
  rw [h, img_code hn τ i] at this
  exact this.symm

theorem code_eq_iff (hn : n ≤ 32) {σ τ : Perm (Fin n)} : code σ = code τ ↔ σ = τ :=
  ⟨code_inj hn, fun h => h ▸ rfl⟩

theorem beq_code (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    Nat.beq (code σ) (code τ) = true ↔ σ = τ := by
  rw [beq_iff, code_eq_iff hn]

theorem code_of_vals (σ : Perm (Fin n)) {g : ℕ → ℕ} (h : ∀ i < n, g i = vals σ i) :
    E g n = code σ := by
  rw [code_eq, E_congr h]

theorem code_mul (hn : n ≤ 32) (σ τ : Perm (Fin n)) : mul n (code σ) (code τ) = code (σ * τ) := by
  rw [mul, ofFn_eq]
  refine code_of_vals _ fun i hi => ?_
  rw [img_code' hn τ hi]
  simp only [vals, hi, ↓reduceDIte, Perm.mul_apply]
  exact img_code hn σ _

theorem code_one : one n = code (1 : Perm (Fin n)) := by
  rw [one, ofFn_eq]
  exact code_of_vals _ fun i hi => by simp [vals, hi]

theorem code_pow (hn : n ≤ 32) (σ : Perm (Fin n)) (k : ℕ) : pow n (code σ) k = code (σ ^ k) := by
  induction k with
  | zero => exact code_one
  | succ k ih =>
    change mul n (pow n (code σ) k) (code σ) = _
    rw [ih, code_mul hn, pow_succ]

theorem code_swap (a b : Fin n) : swap n a b = code (Equiv.swap a b) := by
  rw [swap, ofFn_eq]
  refine code_of_vals _ fun i hi => ?_
  simp only [vals, hi, ↓reduceDIte, Equiv.swap_apply_def]
  have bf : ∀ {x y : ℕ}, x ≠ y → Nat.beq x y = false := fun {x y} h => by
    cases e : Nat.beq x y
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) h
  by_cases h1 : (⟨i, hi⟩ : Fin n) = a
  · rw [ite_eq_left h1, beq_iff.2 (congrArg Fin.val h1)]
  · rw [ite_eq_right h1, bf fun e => h1 (Fin.ext e)]
    by_cases h2 : (⟨i, hi⟩ : Fin n) = b
    · rw [ite_eq_left h2, beq_iff.2 (congrArg Fin.val h2)]
    · rw [ite_eq_right h2, bf fun e => h2 (Fin.ext e)]

theorem code_inv (hn : n ≤ 32) (σ : Perm (Fin n)) : inv n (code σ) = code σ⁻¹ := by
  have e1 : inv n (code σ) = ∑ i ∈ range n, i * 32 ^ img (code σ) i := by
    rw [inv, ← rec_sum]
    congr 1
    funext i acc
    rw [shl_eq]
  rw [e1, ← Fin.sum_univ_eq_sum_range (fun i => i * 32 ^ img (code σ) i), code_fin σ⁻¹]
  simp only [img_code hn]
  rw [← Equiv.sum_comp σ (fun j => ((σ⁻¹ j : Fin n) : ℕ) * 32 ^ (j : ℕ))]
  simp

theorem comm_code (hn : n ≤ 32) (σ τ : Perm (Fin n)) :
    comm n (code σ) (code τ) = true ↔ σ * τ = τ * σ := by
  rw [comm, code_mul hn, code_mul hn, beq_code hn]

theorem conj_code (hn : n ≤ 32) (g σ : Perm (Fin n)) :
    conj n (code g) (code σ) = code (g * σ * g⁻¹) := by
  rw [conj, code_mul hn, code_inv hn, code_mul hn]

theorem fix_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    fix n (code σ) = (univ.filter fun i : Fin n => σ i = i).card := by
  have e1 : fix n (code σ) = ∑ i ∈ range n,
      Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (img (code σ) i) i) := by
    rw [fix, ← rec_sum]
  rw [e1, card_filter, ← Fin.sum_univ_eq_sum_range
    (fun i => Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq (img (code σ) i) i))]
  refine sum_congr rfl fun i _ => ?_
  rw [img_code hn]
  by_cases h : σ i = i
  · rw [ite_eq_left h, h, Nat.beq_refl]
  · rw [ite_eq_right h]
    have : Nat.beq (σ i : ℕ) i = false := by
      cases e : Nat.beq (σ i : ℕ) i
      · rfl
      · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true e)) h
    rw [this]

theorem signAux_eq_sign (σ : Perm (Fin n)) : Perm.signAux σ = Perm.sign σ := by
  induction σ using Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih => rw [Perm.signAux_mul, Perm.sign_mul, ih, Perm.signAux_swap hxy,
      Perm.sign_swap hxy]

theorem sum_attachFin (s : Finset ℕ) (h : ∀ m ∈ s, m < n) (g : Fin n → ℕ) :
    ∑ i ∈ s.attachFin h, g i = ∑ i ∈ s, if hi : i < n then g ⟨i, hi⟩ else 0 := by
  refine sum_bij (fun a _ => a.val) (fun a ha => (mem_attachFin h).1 ha)
    (fun a₁ _ a₂ _ e => Fin.ext e) (fun b hb => ⟨⟨b, h b hb⟩, (mem_attachFin h).2 hb, rfl⟩)
    (fun a _ => by simp [a.isLt])

theorem invs_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    invs n (code σ) = (Perm.finPairsLT n |>.filter fun x => σ x.1 ≤ σ x.2).card := by
  have e1 : invs n (code σ) = ∑ j ∈ range n, ∑ i ∈ range j,
      Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt (img (code σ) j) (img (code σ) i)) := by
    rw [invs, ← rec_sum]
    congr 1
    funext j acc
    rw [← rec_sum]
  rw [e1, Perm.finPairsLT, filter_sigma, card_sigma,
    ← Fin.sum_univ_eq_sum_range (fun j => ∑ i ∈ range j,
      Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.blt (img (code σ) j) (img (code σ) i)))]
  refine sum_congr rfl fun a _ => ?_
  dsimp only
  rw [card_filter, sum_attachFin]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < n := (mem_range.1 hi).trans a.isLt
  rw [img_code hn, img_code' hn σ hi', dite_eq_left hi']
  simp only [vals, hi', ↓reduceDIte]
  have hne : σ a ≠ σ ⟨i, hi'⟩ := fun h => by
    have := congrArg Fin.val (σ.injective h)
    simp at this
    have := mem_range.1 hi
    omega
  by_cases h : σ a ≤ σ ⟨i, hi'⟩
  · have hl : (σ a : ℕ) < σ ⟨i, hi'⟩ := lt_of_le_of_ne h (fun e => hne (Fin.ext e))
    rw [ite_eq_left h, Nat.blt_eq.mpr hl]
  · have : Nat.blt (σ a : ℕ) (σ ⟨i, hi'⟩) = false := by
      cases e : Nat.blt (σ a : ℕ) (σ ⟨i, hi'⟩)
      · rfl
      · exact absurd (le_of_lt (Nat.blt_eq.mp e)) h
    rw [ite_eq_right h, this]

theorem even_code (hn : n ≤ 32) (σ : Perm (Fin n)) :
    even n (code σ) = true ↔ Perm.sign σ = 1 := by
  rw [← signAux_eq_sign, Perm.signAux, prod_ite, prod_const, prod_const_one, mul_one, ← invs_code hn]
  change Nat.beq (invs n (code σ) % 2) 0 = true ↔ _
  rw [beq_iff, ← Nat.even_iff, neg_one_pow_eq_one_iff_even (by decide)]

theorem bit_eq (mask v : ℕ) :
    Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)) = mask.testBit v := by
  change Nat.blt 0 (mask &&& 1 <<< v) = _
  have e : mask &&& 1 <<< v = if mask.testBit v then 2 ^ v else 0 := by
    rw [Nat.one_shiftLeft]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow]
    split_ifs with h
    · rw [Nat.testBit_two_pow]
      by_cases hi : v = i
      · subst hi; simp [h]
      · simp [hi]
    · simp only [Nat.zero_testBit]
      by_cases hi : v = i
      · subst hi; simp [h]
      · simp [hi]
  rw [e]
  split_ifs with h
  · rw [h]
    exact Nat.blt_eq.mpr (Nat.two_pow_pos v)
  · rw [Bool.not_eq_true] at h
    rw [h]
    rfl

theorem lor_eq (mask v : ℕ) : Nat.lor mask (Nat.shiftLeft 1 v) = mask ||| 2 ^ v := by
  change mask ||| 1 <<< v = _
  rw [Nat.one_shiftLeft]

def ext : ℕ → ℕ → List ℕ → ℕ
  | acc, _, [] => acc
  | acc, pos, v :: l => ext (acc + v * 32 ^ pos) (pos + 1) l

def Adm (n mask : ℕ) (l : List ℕ) : Prop := l.Nodup ∧ ∀ v ∈ l, v < n ∧ mask.testBit v = false

theorem adm_nil (n mask : ℕ) : Adm n mask [] := ⟨List.nodup_nil, by simp⟩

theorem adm_cons {n mask v : ℕ} {l : List ℕ} :
    Adm n mask (v :: l) ↔ v < n ∧ mask.testBit v = false ∧ Adm n (mask ||| 2 ^ v) l := by
  simp only [Adm, List.nodup_cons, List.mem_cons, forall_eq_or_imp, Nat.testBit_or,
    Nat.testBit_two_pow, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨hv, hl⟩, ⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, hl, fun u hu => ⟨(h3 u hu).1, (h3 u hu).2, fun e => hv (e ▸ hu)⟩⟩
  · rintro ⟨h1, h2, hl, h3⟩
    exact ⟨⟨fun hv => (h3 v hv).2.2 rfl, hl⟩, ⟨h1, h2⟩, fun u hu => ⟨(h3 u hu).1, (h3 u hu).2.1⟩⟩

theorem dfs_and (f : ℕ → Bool) : ∀ d pos mask acc,
    dfs n andB true f d pos mask acc = true ↔
      ∀ l : List ℕ, l.length = d → Adm n mask l → f (ext acc pos l) = true := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc
    change f acc = true ↔ _
    constructor
    · intro h l hl _
      rw [List.length_eq_zero_iff.1 hl]
      exact h
    · exact fun h => h [] rfl (adm_nil n mask)
  | succ d ih =>
    intro pos mask acc
    change allN n (fun v => Bool.rec (motive := fun _ => Bool)
      (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))) fun a =>
        letB (Nat.lor mask (Nat.shiftLeft 1 v)) fun m => dfs n andB true f d (Nat.succ pos) m a)
      true (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) = true ↔ _
    rw [allN_iff]
    simp only [letB_eq, bit_eq, lor_eq, shl_eq]
    constructor
    · intro h l hl hadm
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := adm_cons.1 hadm
      have := h v hv
      rw [hb] at this
      exact (ih _ _ _).1 this l' (by simpa using hl) hadm'
    · intro h v hv
      cases hb : mask.testBit v
      · refine (ih _ _ _).2 fun l' hl' hadm' => ?_
        exact h (v :: l') (by simp [hl']) (adm_cons.2 ⟨hv, hb, hadm'⟩)
      · rfl

theorem dfs_or (f : ℕ → Bool) : ∀ d pos mask acc,
    dfs n orB false f d pos mask acc = true ↔
      ∃ l : List ℕ, l.length = d ∧ Adm n mask l ∧ f (ext acc pos l) = true := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc
    change f acc = true ↔ _
    constructor
    · exact fun h => ⟨[], rfl, adm_nil n mask, h⟩
    · rintro ⟨l, hl, _, h⟩
      rw [List.length_eq_zero_iff.1 hl] at h
      exact h
  | succ d ih =>
    intro pos mask acc
    change anyN n (fun v => Bool.rec (motive := fun _ => Bool)
      (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))) fun a =>
        letB (Nat.lor mask (Nat.shiftLeft 1 v)) fun m => dfs n orB false f d (Nat.succ pos) m a)
      false (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) = true ↔ _
    rw [anyN_iff]
    simp only [letB_eq, bit_eq, lor_eq, shl_eq]
    constructor
    · rintro ⟨v, hv, h⟩
      cases hb : mask.testBit v
      · rw [hb] at h
        obtain ⟨l', hl', hadm', hf⟩ := (ih _ _ _).1 h
        exact ⟨v :: l', by simp [hl'], adm_cons.2 ⟨hv, hb, hadm'⟩, hf⟩
      · rw [hb] at h
        cases h
    · rintro ⟨l, hl, hadm, hf⟩
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := adm_cons.1 hadm
      refine ⟨v, hv, ?_⟩
      rw [hb]
      exact (ih _ _ _).2 ⟨l', by simpa using hl, hadm', hf⟩

theorem ext_eq : ∀ (l : List ℕ) (acc pos : ℕ),
    ext acc pos l = acc + 32 ^ pos * E (fun k => l.getD k 0) l.length
  | [], acc, pos => by simp [ext, E]
  | v :: l, acc, pos => by
    rw [ext, ext_eq l, List.length_cons, E_succ_left]
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_succ]
    rw [mul_add, ← mul_assoc, mul_comm (32 ^ pos) v, add_assoc]

def imgs (σ : Perm (Fin n)) : List ℕ := List.ofFn fun i => (σ i : ℕ)

theorem imgs_getD (σ : Perm (Fin n)) {k : ℕ} (hk : k < n) : (imgs σ).getD k 0 = vals σ k := by
  simp [imgs, vals, hk, List.getD_eq_getElem?_getD]

theorem ext_imgs (σ : Perm (Fin n)) : ext 0 0 (imgs σ) = code σ := by
  rw [ext_eq, pow_zero, one_mul, zero_add, imgs, List.length_ofFn, ← imgs]
  exact code_of_vals σ fun k hk => imgs_getD σ hk

theorem adm_imgs (σ : Perm (Fin n)) : Adm n 0 (imgs σ) := by
  refine ⟨?_, ?_⟩
  · rw [imgs, List.nodup_ofFn]
    exact fun i j h => σ.injective (Fin.ext h)
  · intro v hv
    simp only [imgs, List.mem_ofFn] at hv
    obtain ⟨i, rfl⟩ := hv
    exact ⟨(σ i).isLt, Nat.zero_testBit _⟩

theorem exists_imgs {l : List ℕ} (hl : l.length = n) (hadm : Adm n 0 l) :
    ∃ σ : Perm (Fin n), imgs σ = l := by
  let g : Fin n → Fin n := fun i => ⟨l[i.val]'(hl ▸ i.isLt), (hadm.2 _ (List.getElem_mem _)).1⟩
  have hg : Function.Injective g := by
    intro i j h
    have h' : l[i.val]'(hl ▸ i.isLt) = l[j.val]'(hl ▸ j.isLt) := congrArg Fin.val h
    exact Fin.ext ((hadm.1.getElem_inj_iff).1 h')
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), ?_⟩
  apply List.ext_getElem
  · simp [imgs, hl]
  · intro k h1 h2
    simp [imgs, g]

theorem allP_iff (f : ℕ → Bool) :
    allP n f = true ↔ ∀ σ : Perm (Fin n), f (code σ) = true := by
  rw [allP, dfs_and]
  constructor
  · intro h σ
    rw [← ext_imgs σ]
    exact h _ (by simp [imgs]) (adm_imgs σ)
  · intro h l hl hadm
    obtain ⟨σ, rfl⟩ := exists_imgs hl hadm
    rw [ext_imgs σ]
    exact h σ

theorem anyP_iff (f : ℕ → Bool) :
    anyP n f = true ↔ ∃ σ : Perm (Fin n), f (code σ) = true := by
  rw [anyP, dfs_or]
  constructor
  · rintro ⟨l, hl, hadm, hf⟩
    obtain ⟨σ, rfl⟩ := exists_imgs hl hadm
    rw [ext_imgs σ] at hf
    exact ⟨σ, hf⟩
  · rintro ⟨σ, hf⟩
    exact ⟨imgs σ, by simp [imgs], adm_imgs σ, by rw [ext_imgs σ]; exact hf⟩

def OkL (ok : ℕ → ℕ → ℕ → Bool) : ℕ → ℕ → List ℕ → Prop
  | _, _, [] => True
  | acc, pos, v :: l => ok acc pos v = true ∧ OkL ok (acc + v * 32 ^ pos) (pos + 1) l

theorem dfsC_and (s si : ℕ) (f : ℕ → Bool) : ∀ d pos mask acc,
    dfsC n s si andB true f d pos mask acc = true ↔
      ∀ l : List ℕ, l.length = d → Adm n mask l → OkL (cOK s si) acc pos l →
        f (ext acc pos l) = true := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc
    change f acc = true ↔ _
    constructor
    · intro h l hl _ _
      rw [List.length_eq_zero_iff.1 hl]
      exact h
    · exact fun h => h [] rfl (adm_nil n mask) trivial
  | succ d ih =>
    intro pos mask acc
    change allN n (fun v => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) true
        (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))) fun a =>
          letB (Nat.lor mask (Nat.shiftLeft 1 v)) fun m =>
            dfsC n s si andB true f d (Nat.succ pos) m a)
        (cOK s si acc pos v))
      true (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) = true ↔ _
    rw [allN_iff]
    simp only [letB_eq, bit_eq, lor_eq, shl_eq]
    constructor
    · intro h l hl hadm hok
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := adm_cons.1 hadm
      obtain ⟨hc, hok'⟩ := hok
      have := h v hv
      rw [hb, hc] at this
      exact (ih _ _ _).1 this l' (by simpa using hl) hadm' hok'
    · intro h v hv
      cases hb : mask.testBit v
      · cases hc : cOK s si acc pos v
        · rfl
        · exact (ih _ _ _).2 fun l' hl' hadm' hok' =>
            h (v :: l') (by simp [hl']) (adm_cons.2 ⟨hv, hb, hadm'⟩) ⟨hc, hok'⟩
      · rfl

theorem dfsC_or (s si : ℕ) (f : ℕ → Bool) : ∀ d pos mask acc,
    dfsC n s si orB false f d pos mask acc = true ↔
      ∃ l : List ℕ, l.length = d ∧ Adm n mask l ∧ OkL (cOK s si) acc pos l ∧
        f (ext acc pos l) = true := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc
    change f acc = true ↔ _
    constructor
    · exact fun h => ⟨[], rfl, adm_nil n mask, trivial, h⟩
    · rintro ⟨l, hl, _, _, h⟩
      rw [List.length_eq_zero_iff.1 hl] at h
      exact h
  | succ d ih =>
    intro pos mask acc
    change anyN n (fun v => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (letB (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))) fun a =>
          letB (Nat.lor mask (Nat.shiftLeft 1 v)) fun m =>
            dfsC n s si orB false f d (Nat.succ pos) m a)
        (cOK s si acc pos v))
      false (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) = true ↔ _
    rw [anyN_iff]
    simp only [letB_eq, bit_eq, lor_eq, shl_eq]
    constructor
    · rintro ⟨v, hv, h⟩
      cases hb : mask.testBit v
      · rw [hb] at h
        cases hc : cOK s si acc pos v
        · rw [hc] at h
          cases h
        · rw [hc] at h
          obtain ⟨l', hl', hadm', hok', hf⟩ := (ih _ _ _).1 h
          exact ⟨v :: l', by simp [hl'], adm_cons.2 ⟨hv, hb, hadm'⟩, ⟨hc, hok'⟩, hf⟩
      · rw [hb] at h
        cases h
    · rintro ⟨l, hl, hadm, hok, hf⟩
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := adm_cons.1 hadm
      obtain ⟨hc, hok'⟩ := hok
      refine ⟨v, hv, ?_⟩
      rw [hb, hc]
      exact (ih _ _ _).2 ⟨l', by simpa using hl, hadm', hok', hf⟩

theorem okL_iff (ok : ℕ → ℕ → ℕ → Bool) : ∀ (l : List ℕ) (acc pos : ℕ),
    OkL ok acc pos l ↔ ∀ k (hk : k < l.length), ok (ext acc pos (l.take k)) (pos + k) l[k] = true
  | [], acc, pos => by simp [OkL]
  | v :: l, acc, pos => by
    rw [OkL, okL_iff ok l]
    constructor
    · rintro ⟨h0, h⟩ k hk
      cases k with
      | zero => simpa [ext] using h0
      | succ k =>
        have := h k (by simpa using hk)
        rw [Nat.add_right_comm, Nat.add_assoc] at this
        simpa [ext] using this
    · intro h
      have h0 := h 0 (by simp)
      simp only [List.take_zero, ext, Nat.add_zero, List.getElem_cons_zero] at h0
      refine ⟨h0, fun k hk => ?_⟩
      have := h (k + 1) (by simpa using hk)
      rw [← Nat.add_assoc, Nat.add_right_comm pos k 1] at this
      simpa [ext] using this

theorem ext_take (σ : Perm (Fin n)) {k : ℕ} (hk : k ≤ n) :
    ext 0 0 ((imgs σ).take k) = E (vals σ) k := by
  rw [ext_eq, pow_zero, one_mul, zero_add, List.length_take, imgs, List.length_ofFn,
    Nat.min_eq_left hk, ← imgs]
  refine E_congr fun i hi => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD,
    imgs_getD σ (by omega)]

theorem img_E (hn : n ≤ 32) (σ : Perm (Fin n)) {k : ℕ} (hk : k ≤ n) (j : Fin n) (hj : (j : ℕ) < k) :
    img (E (vals σ) k) j = σ j := by
  rw [img_eq, E_digit (fun i hi => vals_lt hn σ i (by omega)) hj, vals_fin]

theorem cOK_iff (hn : n ≤ 32) (σ g : Perm (Fin n)) (k : Fin n) :
    cOK (code σ) (code σ⁻¹) (E (vals g) k) k (g k) = true ↔
      (σ k < k → g (σ k) = σ (g k)) ∧ (σ⁻¹ k < k → g k = σ (g (σ⁻¹ k))) := by
  have hk : (k : ℕ) ≤ n := k.isLt.le
  unfold cOK
  rw [andB_iff, impB_iff, impB_iff, blt_iff, blt_iff, img_code hn σ k, img_code hn σ⁻¹ k,
    beq_iff, beq_iff, img_code hn σ (g k)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := h1 h
      rw [img_E hn g hk _ h] at this
      exact Fin.ext this
    · have := h2 h
      rw [img_E hn g hk _ h, img_code hn σ] at this
      exact Fin.ext this
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [img_E hn g hk _ h, h1 h]
    · rw [img_E hn g hk _ h, img_code hn σ, h2 h]

theorem comm_of_cond (σ g : Perm (Fin n)) (h1 : ∀ k, σ k < k → g (σ k) = σ (g k))
    (h2 : ∀ k, σ⁻¹ k < k → g k = σ (g (σ⁻¹ k))) : g * σ = σ * g := by
  have hm : ∀ q, σ q ≠ q → g (σ q) = σ (g q) := fun q hq => by
    rcases lt_or_gt_of_ne hq with h | h
    · exact h1 q h
    · have := h2 (σ q) (by simpa using h)
      simpa using this
  have hsupp : σ.support.image g = σ.support := by
    refine eq_of_subset_of_card_le (fun x hx => ?_) (card_image_of_injective _ g.injective).ge
    obtain ⟨r, hr, rfl⟩ := mem_image.1 hx
    rw [Perm.mem_support] at hr ⊢
    rw [← hm r hr]
    exact fun e => hr (g.injective e)
  ext q
  simp only [Perm.mul_apply]
  by_cases hq : σ q = q
  · rw [hq]
    by_contra hne
    have : g q ∈ σ.support := Perm.mem_support.2 fun e => hne (congrArg Fin.val e.symm)
    rw [← hsupp] at this
    obtain ⟨r, hr, e⟩ := mem_image.1 this
    rw [g.injective e] at hr
    exact Perm.mem_support.1 hr hq
  · rw [hm q hq]

theorem cond_of_comm {σ g : Perm (Fin n)} (h : g * σ = σ * g) (k : Fin n) :
    (σ k < k → g (σ k) = σ (g k)) ∧ (σ⁻¹ k < k → g k = σ (g (σ⁻¹ k))) := by
  have e : ∀ x, g (σ x) = σ (g x) := fun x => by
    have := congrArg (fun p => p x) h
    simpa using this
  refine ⟨fun _ => e k, fun _ => ?_⟩
  rw [← e]
  simp

theorem okL_comm (hn : n ≤ 32) (σ g : Perm (Fin n)) :
    OkL (cOK (code σ) (code σ⁻¹)) 0 0 (imgs g) ↔ g * σ = σ * g := by
  rw [okL_iff]
  have hl : (imgs g).length = n := by simp [imgs]
  have key : ∀ k (hk : k < (imgs g).length),
      cOK (code σ) (code σ⁻¹) (ext 0 0 ((imgs g).take k)) (0 + k) (imgs g)[k] = true ↔
        (σ ⟨k, hl ▸ hk⟩ < ⟨k, hl ▸ hk⟩ → g (σ ⟨k, hl ▸ hk⟩) = σ (g ⟨k, hl ▸ hk⟩)) ∧
        (σ⁻¹ ⟨k, hl ▸ hk⟩ < ⟨k, hl ▸ hk⟩ → g ⟨k, hl ▸ hk⟩ = σ (g (σ⁻¹ ⟨k, hl ▸ hk⟩))) := by
    intro k hk
    rw [ext_take g (by omega), zero_add]
    have : (imgs g)[k] = (g ⟨k, hl ▸ hk⟩ : ℕ) := by simp [imgs]
    rw [this]
    exact cOK_iff hn σ g ⟨k, hl ▸ hk⟩
  constructor
  · intro h
    refine comm_of_cond σ g (fun k hk => ((key k (hl.symm ▸ k.isLt)).1 (h k _)).1 hk)
      (fun k hk => ((key k (hl.symm ▸ k.isLt)).1 (h k _)).2 hk)
  · intro h k hk
    exact (key k hk).2 (cond_of_comm h _)

theorem allC_iff (hn : n ≤ 32) (σ : Perm (Fin n)) (f : ℕ → Bool) :
    allC n (code σ) f = true ↔ ∀ g : Perm (Fin n), g * σ = σ * g → f (code g) = true := by
  rw [allC, letB_eq, code_inv hn, dfsC_and]
  constructor
  · intro h g hg
    rw [← ext_imgs g]
    exact h _ (by simp [imgs]) (adm_imgs g) ((okL_comm hn σ g).2 hg)
  · intro h l hl hadm hok
    obtain ⟨g, rfl⟩ := exists_imgs hl hadm
    rw [ext_imgs g]
    exact h g ((okL_comm hn σ g).1 hok)

theorem anyC_iff (hn : n ≤ 32) (σ : Perm (Fin n)) (f : ℕ → Bool) :
    anyC n (code σ) f = true ↔ ∃ g : Perm (Fin n), g * σ = σ * g ∧ f (code g) = true := by
  rw [anyC, letB_eq, code_inv hn, dfsC_or]
  constructor
  · rintro ⟨l, hl, hadm, hok, hf⟩
    obtain ⟨g, rfl⟩ := exists_imgs hl hadm
    rw [ext_imgs g] at hf
    exact ⟨g, (okL_comm hn σ g).1 hok, hf⟩
  · rintro ⟨g, hg, hf⟩
    exact ⟨imgs g, by simp [imgs], adm_imgs g, (okL_comm hn σ g).2 hg, by rw [ext_imgs g]; exact hf⟩

theorem allL_map (L : List (Perm (Fin n))) (f : ℕ → Bool) :
    allL (L.map code) f = true ↔ ∀ g ∈ L, f (code g) = true := by
  rw [allL_iff]
  simp

theorem anyL_map (L : List (Perm (Fin n))) (f : ℕ → Bool) :
    anyL (L.map code) f = true ↔ ∃ g ∈ L, f (code g) = true := by
  rw [anyL_iff]
  simp

theorem mem_map_code (hn : n ≤ 32) (L : List (Perm (Fin n))) (g : Perm (Fin n)) :
    code g ∈ L.map code ↔ g ∈ L := by
  simp [code_eq_iff hn]

theorem testBit_fold (f : ℕ → ℕ) (v : ℕ) : ∀ m, (Nat.rec (motive := fun _ => ℕ) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) m).testBit v = true ↔ ∃ i < m, f i = v := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    change (Nat.lor (Nat.rec (motive := fun _ => ℕ) 0
      (fun i acc => Nat.lor acc (Nat.shiftLeft 1 (f i))) m) (Nat.shiftLeft 1 (f m))).testBit v = _ ↔ _
    rw [lor_eq, Nat.testBit_or, Bool.or_eq_true, ih, Nat.testBit_two_pow, decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      exacts [⟨i, by omega, h⟩, ⟨m, by omega, h⟩]
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      exacts [Or.inl ⟨i, hi, h⟩, Or.inr h]

theorem exists_of_permK {s : ℕ} (h : permK n s = true) : ∃ σ : Perm (Fin n), code σ = s := by
  unfold permK at h
  rw [andB_iff, andB_iff, beq_iff, beq_iff, allN_iff] at h
  obtain ⟨hs, hlt, hm⟩ := h
  have hlt' : ∀ i < n, img s i < n := fun i hi => blt_iff.1 (hlt i hi)
  let g : Fin n → Fin n := fun i => ⟨img s i, hlt' i i.isLt⟩
  have hsurj : Function.Surjective g := by
    intro v
    have hb : (Nat.sub (Nat.shiftLeft 1 n) 1).testBit v = true := by
      change (1 <<< n - 1 : ℕ).testBit v = true
      rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true_iff]
      exact v.isLt
    rw [← hm, testBit_fold] at hb
    obtain ⟨i, hi, e⟩ := hb
    exact ⟨⟨i, hi⟩, Fin.ext e⟩
  have hbij : Function.Bijective g := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨Equiv.ofBijective g hbij, ?_⟩
  rw [code_eq]
  refine Eq.trans ?_ ((ofFn_eq n (img s)).symm.trans hs.symm)
  exact E_congr fun i hi => by simp [vals, hi, g]

def cl (n : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, acc => [acc]
  | d + 1, pos, mask, acc => (List.range n).flatMap fun v =>
      if mask.testBit v then [] else cl n d (pos + 1) (mask ||| 2 ^ v) (acc + v * 32 ^ pos)

def cntD (n : ℕ) (f : ℕ → Bool) (d : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ)
    (fun _ _ acc => Bool.rec (motive := fun _ => ℕ) 0 1 (f acc))
    (fun _ ih pos mask acc =>
      Nat.rec (motive := fun _ => ℕ) 0
        (fun v rest => Nat.add
          (Bool.rec (motive := fun _ => ℕ)
            (ih (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft 1 v))
              (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))))
            0 (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v))))
          rest) n) d

theorem rec_add (g : ℕ → ℕ) (m : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun v rest => Nat.add (g v) rest) m =
      ((List.range m).map g).sum := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Nat.add (g m) (Nat.rec (motive := fun _ => ℕ) 0 (fun v rest => Nat.add (g v) rest) m) = _
    rw [ih, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    exact Nat.add_comm _ _

theorem cntD_eq (f : ℕ → Bool) : ∀ d pos mask acc,
    cntD n f d pos mask acc = (cl n d pos mask acc).countP f := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc
    change Bool.rec (motive := fun _ => ℕ) 0 1 (f acc) = [acc].countP f
    rw [List.countP_singleton]
    cases f acc <;> rfl
  | succ d ih =>
    intro pos mask acc
    change Nat.rec (motive := fun _ => ℕ) 0 (fun v rest => Nat.add
      (Bool.rec (motive := fun _ => ℕ)
        (cntD n f d (Nat.succ pos) (Nat.lor mask (Nat.shiftLeft 1 v))
          (Nat.add acc (Nat.shiftLeft v (Nat.mul 5 pos))))
        0 (Nat.blt 0 (Nat.land mask (Nat.shiftLeft 1 v)))) rest) n = _
    rw [rec_add, cl, List.countP_flatMap]
    congr 1
    refine List.map_congr_left fun v _ => ?_
    simp only [bit_eq, lor_eq, shl_eq, Function.comp_apply]
    cases hb : mask.testBit v
    · exact ih _ _ _
    · rfl

theorem mem_cl : ∀ (d pos mask acc x : ℕ),
    x ∈ cl n d pos mask acc ↔ ∃ l : List ℕ, l.length = d ∧ Adm n mask l ∧ x = ext acc pos l := by
  intro d
  induction d with
  | zero =>
    intro pos mask acc x
    simp only [cl, List.mem_singleton]
    constructor
    · exact fun h => ⟨[], rfl, adm_nil n mask, h⟩
    · rintro ⟨l, hl, _, rfl⟩
      rw [List.length_eq_zero_iff.1 hl]
      rfl
  | succ d ih =>
    intro pos mask acc x
    rw [cl, List.mem_flatMap]
    constructor
    · rintro ⟨v, hv, hx⟩
      cases hb : mask.testBit v
      · rw [hb] at hx
        obtain ⟨l', hl', hadm', rfl⟩ := (ih _ _ _ _).1 hx
        exact ⟨v :: l', by simp [hl'], adm_cons.2 ⟨List.mem_range.1 hv, hb, hadm'⟩, rfl⟩
      · rw [hb] at hx
        simp at hx
    · rintro ⟨l, hl, hadm, rfl⟩
      obtain ⟨v, l', rfl⟩ := List.exists_cons_of_length_eq_add_one hl
      obtain ⟨hv, hb, hadm'⟩ := adm_cons.1 hadm
      refine ⟨v, List.mem_range.2 hv, ?_⟩
      rw [hb]
      exact (ih _ _ _ _).2 ⟨l', by simpa using hl, hadm', rfl⟩

theorem ext_mod (l : List ℕ) {acc pos : ℕ} (h : acc < 32 ^ pos) : ext acc pos l % 32 ^ pos = acc := by
  rw [ext_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem nodup_cl (hn : n ≤ 32) : ∀ d pos mask acc, acc < 32 ^ pos → (cl n d pos mask acc).Nodup := by
  intro d
  induction d with
  | zero => exact fun _ _ _ _ => List.nodup_singleton _
  | succ d ih =>
    intro pos mask acc hacc
    have hlt : ∀ v < n, acc + v * 32 ^ pos < 32 ^ (pos + 1) := fun v hv => by
      have : v * 32 ^ pos ≤ 31 * 32 ^ pos := Nat.mul_le_mul_right _ (by omega)
      rw [pow_succ]
      omega
    rw [cl, List.nodup_flatMap]
    refine ⟨fun v hv => ?_, ?_⟩
    · cases mask.testBit v
      · exact ih _ _ _ (hlt v (List.mem_range.1 hv))
      · exact List.nodup_nil
    · refine List.nodup_range.pairwise_of_forall_ne fun v hv w hw hvw => ?_
      intro x hx hx'
      have key : ∀ u ∈ List.range n, x ∈ (if mask.testBit u then [] else
          cl n d (pos + 1) (mask ||| 2 ^ u) (acc + u * 32 ^ pos)) →
          x % 32 ^ (pos + 1) = acc + u * 32 ^ pos := fun u hu hxu => by
        cases hb : mask.testBit u
        · rw [hb] at hxu
          obtain ⟨l, _, _, rfl⟩ := (mem_cl _ _ _ _ _).1 hxu
          exact ext_mod l (hlt u (List.mem_range.1 hu))
        · rw [hb] at hxu
          simp at hxu
      have e := (key v hv hx).symm.trans (key w hw hx')
      exact hvw (Nat.eq_of_mul_eq_mul_right (by positivity) (Nat.add_left_cancel e))

theorem cntP_eq (hn : n ≤ 32) (f : ℕ → Bool) :
    cntP n f = (univ.filter fun σ : Perm (Fin n) => f (code σ) = true).card := by
  change cntD n f n 0 0 0 = _
  rw [cntD_eq, List.countP_eq_length_filter]
  have hL : (cl n n 0 0 0).Nodup := nodup_cl hn n 0 0 0 (by norm_num)
  rw [← List.toFinset_card_of_nodup (hL.filter _),
    ← card_image_of_injective _ (fun a b h => code_inj hn h)]
  congr 1
  ext x
  simp only [List.mem_toFinset, List.mem_filter, mem_image, mem_filter, mem_univ, true_and,
    mem_cl]
  constructor
  · rintro ⟨⟨l, hl, hadm, rfl⟩, hf⟩
    obtain ⟨σ, rfl⟩ := exists_imgs hl hadm
    exact ⟨σ, by rw [ext_imgs σ] at hf; exact hf, (ext_imgs σ).symm⟩
  · rintro ⟨σ, hf, rfl⟩
    exact ⟨⟨imgs σ, by simp [imgs], adm_imgs σ, (ext_imgs σ).symm⟩, hf⟩

end CFSG.KC.LQT.P

end
