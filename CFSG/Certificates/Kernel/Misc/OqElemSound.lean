module

public import Certificates.Data.Kernel.Misc.Oq
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqInputs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneOqDataKill
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.List.GetD

public section

namespace CFSG.KC.Misc.Oq

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

private def packR (w : ℕ) (ent : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k acc => Nat.lor acc (Nat.shiftLeft (ent k) (Nat.mul w k))) n

private theorem packR_spec (w : ℕ) (ent : ℕ → ℕ) (hent : ∀ k, ent k < 2 ^ w) (n : ℕ) :
    packR w ent n < 2 ^ (w * n) ∧
    ∀ j < n, (packR w ent n >>> (w * j)) &&& (2 ^ w - 1) = ent j := by
  induction n with
  | zero => simp [packR]
  | succ n ih =>
    obtain ⟨hP, hF⟩ := ih
    have hE : ent n <<< (w * n) < 2 ^ (w * (n + 1)) := by
      rw [Nat.shiftLeft_eq, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * n))]
      exact Nat.mul_lt_mul_of_pos_right (hent n) (Nat.two_pow_pos _)
    have hmono : 2 ^ (w * n) ≤ 2 ^ (w * (n + 1)) :=
      Nat.pow_le_pow_right Nat.two_pos (Nat.mul_le_mul_left _ (Nat.le_succ n))
    have hP' : packR w ent n < 2 ^ (w * (n + 1)) := lt_of_lt_of_le hP hmono
    have hrec : packR w ent (n + 1) = packR w ent n ||| (ent n <<< (w * n)) := rfl
    refine ⟨by rw [hrec]; exact Nat.or_lt_two_pow hP' hE, fun j hj => ?_⟩
    rw [hrec]
    refine Nat.eq_of_testBit_eq fun m => ?_
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
      Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hm : m < w
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · have h1 := congrArg (fun x => x.testBit m) (hF j hj)
        simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at h1
        simp only [hm, decide_true, Bool.and_true] at h1
        have : ¬ (w * n ≤ w * j + m) := by
          have := Nat.mul_le_mul_left w (show j + 1 ≤ n from hj)
          rw [Nat.mul_succ] at this
          omega
        simp [hm, this, h1]
      · subst hj
        have h1 : (packR w ent j).testBit (w * j + m) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le hP (Nat.pow_le_pow_right Nat.two_pos (by omega))
        simp [hm, h1]
    · simp only [hm, decide_false, Bool.and_false]
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (hent j) (Nat.pow_le_pow_right Nat.two_pos (by omega)))).symm


open CFSG.EvenSmallLie.OmegaEight.SpBranch (xorBits xorBits_succ xorBits_zero)

private theorem xorBits_congr {f g : ℕ → ℕ} (n v : ℕ) (h : ∀ j < n, f j = g j) :
    xorBits n f v = xorBits n g v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem xorBits_xor (f : ℕ → ℕ) (n x y : ℕ) :
    xorBits n f (x ^^^ y) = xorBits n f x ^^^ xorBits n f y := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, xorBits_succ, ih, Nat.testBit_xor]
    by_cases hx : x.testBit n <;> by_cases hy : y.testBit n <;> simp [hx, hy] <;>
      simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

private theorem xorBits_lt {f : ℕ → ℕ} {N : ℕ} (hf : ∀ j, f j < 2 ^ N) (n v : ℕ) :
    xorBits n f v < 2 ^ N := by
  induction n with
  | zero => simp [xorBits_zero]; exact Nat.two_pow_pos _
  | succ n ih =>
    rw [xorBits_succ]
    refine Nat.xor_lt_two_pow ih ?_
    split
    · exact hf n
    · exact Nat.two_pow_pos _

private theorem xorBits_basis' (f : ℕ → ℕ) (n i : ℕ) :
    xorBits n f (2 ^ i) = if i < n then f i else 0 := by
  induction n with
  | zero => simp [xorBits_zero]
  | succ n ih =>
    rw [xorBits_succ, ih, Nat.testBit_two_pow]
    by_cases h1 : i < n
    · simp [h1, show i < n + 1 by omega, show i ≠ n by omega]
    · by_cases h2 : i = n
      · subst h2; simp
      · simp [h1, h2, show ¬ i < n + 1 by omega, show ¬ i = n from h2]

private theorem xorBits_basis (f : ℕ → ℕ) {n i : ℕ} (hi : i < n) :
    xorBits n f (2 ^ i) = f i := by
  rw [xorBits_basis', if_pos hi]

private theorem lin_eq_xorBits (f : ℕ → ℕ) (hadd : ∀ x y, f (x ^^^ y) = f x ^^^ f y) (n v : ℕ) :
    f (v % 2 ^ n) = xorBits n (fun j => f (2 ^ j)) v := by
  have h0 : f 0 = 0 := by
    have := hadd 0 0
    simpa using this
  induction n with
  | zero => simp [xorBits_zero, h0, Nat.mod_one]
  | succ n ih =>
    rw [xorBits_succ, ← ih]
    have : v % 2 ^ (n + 1) = (v % 2 ^ n) ^^^ (if v.testBit n then 2 ^ n else 0) := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
      by_cases hv : v.testBit n
      · simp only [hv, if_true, Nat.testBit_two_pow]
        by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega, show n ≠ i by omega]
        · by_cases hin : i = n
          · subst hin; simp [hv]
          · simp [hi, show ¬ i < n + 1 by omega, Ne.symm hin]
      · simp only [hv, Bool.false_eq_true, if_false, Nat.zero_testBit, Bool.xor_false]
        by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega]
        · by_cases hin : i = n
          · subst hin; simp [hv]
          · simp [hi, show ¬ i < n + 1 by omega]
    rw [this, hadd]
    split <;> simp [h0]


private def unpack9 (P : ℕ) : List ℕ := (List.range 9).map fun i => P / 512 ^ i % 512

private theorem fld6_eq (P i : ℕ) : fld6 P i = P / 64 ^ i % 64 := by
  have : fld6 P i = (P >>> (6 * i)) &&& (2 ^ 6 - 1) := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem fld9_eq (P i : ℕ) : fld9 P i = P / 512 ^ i % 512 := by
  have : fld9 P i = (P >>> (9 * i)) &&& (2 ^ 9 - 1) := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

private theorem fld6_lt (P i : ℕ) : fld6 P i < 64 := by
  rw [fld6_eq]; exact Nat.mod_lt _ (by decide)

private theorem fld9_lt (P i : ℕ) : fld9 P i < 512 := by
  rw [fld9_eq]; exact Nat.mod_lt _ (by decide)

private theorem unpack6_getD (P : ℕ) {j : ℕ} (hj : j < 6) : (unpack6 P).getD j 0 = fld6 P j := by
  simp [unpack6, fld6_eq, hj, List.getD_eq_getElem?_getD]

private theorem unpack9_getD (P : ℕ) {j : ℕ} (hj : j < 9) : (unpack9 P).getD j 0 = fld9 P j := by
  simp [unpack9, fld9_eq, hj, List.getD_eq_getElem?_getD]

private theorem bit_eq (v j : ℕ) : bit v j = if v.testBit j then 1 else 0 := by
  have h : bit v j = (v >>> j) &&& 1 := rfl
  have h2 : v.testBit j = (v >>> j).testBit 0 := by simp [Nat.testBit_shiftRight]
  rw [h, Nat.and_one_is_mod, h2, Nat.testBit_zero]
  have := Nat.mod_two_eq_zero_or_one (v >>> j)
  by_cases h3 : (v >>> j) % 2 = 1 <;> simp [h3] <;> omega

private theorem natrec_xor (f : ℕ → ℕ) (v n : ℕ) :
    (Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.xor acc (Nat.mul (bit v j) (f j))) n : ℕ)
      = xorBits n f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.xor _ _ = _
    rw [ih, xorBits_succ, bit_eq]
    by_cases h : v.testBit n <;> simp [h]


private theorem xorBits_congr_v {f : ℕ → ℕ} (n : ℕ) {x y : ℕ}
    (h : ∀ j < n, x.testBit j = y.testBit j) : xorBits n f x = xorBits n f y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [xorBits_succ, xorBits_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

private theorem evV_eq (P v : ℕ) : evV P v = evalV (unpack6 P) v := by
  have h : evV P v = xorBits 6 (fun j => fld6 P j) v := natrec_xor _ v 6
  rw [h]
  exact xorBits_congr 6 v (fun j hj => (unpack6_getD P hj).symm)

private theorem evE_eq (P v : ℕ) : evE P v = evalE (unpack9 P) v := by
  have h : evE P v = xorBits 9 (fun j => fld9 P j) v := natrec_xor _ v 9
  rw [h]
  exact xorBits_congr 9 v (fun j hj => (unpack9_getD P hj).symm)

private theorem evalV_lt (P v : ℕ) : evalV (unpack6 P) v < 64 := by
  have : evalV (unpack6 P) v < 2 ^ 6 := by
    refine xorBits_lt (N := 6) (fun j => ?_) 6 v
    by_cases hj : j < 6
    · rw [unpack6_getD P hj]; exact fld6_lt _ _
    · rw [List.getD_eq_default _ _ (by simp [unpack6]; omega)]; decide
  exact this

private theorem evalE_lt (P v : ℕ) : evalE (unpack9 P) v < 512 := by
  have : evalE (unpack9 P) v < 2 ^ 9 := by
    refine xorBits_lt (N := 9) (fun j => ?_) 9 v
    by_cases hj : j < 9
    · rw [unpack9_getD P hj]; exact fld9_lt _ _
    · rw [List.getD_eq_default _ _ (by simp [unpack9]; omega)]; decide
  exact this

private theorem evalV_xor (l : List ℕ) (x y : ℕ) :
    evalV l (x ^^^ y) = evalV l x ^^^ evalV l y := xorBits_xor _ 6 x y

private theorem evalE_xor (l : List ℕ) (x y : ℕ) :
    evalE l (x ^^^ y) = evalE l x ^^^ evalE l y := xorBits_xor _ 9 x y

private theorem evalV_basis (l : List ℕ) {i : ℕ} (hi : i < 6) : evalV l (2 ^ i) = l.getD i 0 :=
  xorBits_basis _ hi

private theorem evalE_basis (l : List ℕ) {i : ℕ} (hi : i < 9) : evalE l (2 ^ i) = l.getD i 0 :=
  xorBits_basis _ hi

private theorem evalV_mod (l : List ℕ) (v : ℕ) : evalV l (v % 64) = evalV l v :=
  xorBits_congr_v 6 (fun j hj => by
    have : v % 64 = v % 2 ^ 6 := rfl
    rw [this, Nat.testBit_mod_two_pow]; simp [hj])

private theorem evalV_lin (g : ℕ → ℕ) (hadd : ∀ x y, g (x ^^^ y) = g x ^^^ g y) (l : List ℕ)
    (hl : ∀ j < 6, l.getD j 0 = g (2 ^ j)) (v : ℕ) : evalV l v = g (v % 64) := by
  have := lin_eq_xorBits g hadd 6 v
  change xorBits 6 (fun j => l.getD j 0) v = _
  rw [xorBits_congr 6 v hl]
  exact this.symm

private theorem lk_tabK (P : ℕ) {x : ℕ} (hx : x < 64) : lk (tabK P) x = evalV (unpack6 P) x := by
  have h := (packR_spec 6 (evV P) (fun k => by rw [evV_eq]; exact evalV_lt P k) 64).2 x hx
  rw [evV_eq] at h
  exact h


private theorem unpack6_length (P : ℕ) : (unpack6 P).length = 6 := by simp [unpack6]

private theorem unpack6_basis (P : ℕ) {i : ℕ} (hi : i < 6) :
    evalV (unpack6 P) (2 ^ i) = P / 64 ^ i % 64 := by
  rw [evalV_basis _ hi, unpack6_getD P hi, fld6_eq]

private theorem two_pow_lt {i : ℕ} (hi : i < 6) : 2 ^ i < 64 :=
  lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hi) (by decide)

private theorem compT_getD (a b : List ℕ) {j : ℕ} (hj : j < b.length) :
    (compT a b).getD j 0 = evalV a (b.getD j 0) := by
  simp [compT, List.getD_eq_getElem?_getD, hj]

private theorem g_add (r s : ℕ) (x y : ℕ) :
    evalV (unpack6 r) (evalV (unpack6 s) (x ^^^ y)) =
      evalV (unpack6 r) (evalV (unpack6 s) x) ^^^ evalV (unpack6 r) (evalV (unpack6 s) y) := by
  rw [evalV_xor, evalV_xor]

private theorem compT_basis (r s : ℕ) {j : ℕ} (hj : j < 6) :
    (compT (unpack6 r) (unpack6 s)).getD j 0 =
      evalV (unpack6 r) (evalV (unpack6 s) (2 ^ j)) := by
  rw [compT_getD _ _ (by rw [unpack6_length]; exact hj), ← evalV_basis (unpack6 s) hj]

private theorem evalV_compT (r s v : ℕ) :
    evalV (compT (unpack6 r) (unpack6 s)) v =
      evalV (unpack6 r) (evalV (unpack6 s) (v % 64)) :=
  evalV_lin (fun v => evalV (unpack6 r) (evalV (unpack6 s) v)) (g_add r s) _
    (fun j hj => compT_basis r s hj) v

private theorem packT_unpack (r s : ℕ) :
    unpack6 (packT (tabK r) (tabK s)) = compT (unpack6 r) (unpack6 s) := by
  have hspec := (packR_spec 6 (fun i => lk (tabK r) (lk (tabK s) (2 ^ i)))
    (fun k => fld6_lt _ _) 6).2
  have hent : ∀ i < 6, packT (tabK r) (tabK s) / 64 ^ i % 64 =
      evalV (unpack6 r) (evalV (unpack6 s) (2 ^ i)) := by
    intro i hi
    have h1 := hspec i hi
    rw [lk_tabK s (two_pow_lt hi), lk_tabK r (lt_of_lt_of_le (evalV_lt s _) le_rfl)] at h1
    rw [← fld6_eq]
    exact h1
  calc unpack6 (packT (tabK r) (tabK s))
      = (List.range 6).map (fun i => packT (tabK r) (tabK s) / 64 ^ i % 64) := rfl
    _ = (List.range 6).map (fun i => evalV (unpack6 r) (s / 64 ^ i % 64)) := by
        refine List.map_congr_left fun i hi => ?_
        have hi' : i < 6 := List.mem_range.1 hi
        rw [hent i hi', unpack6_basis s hi']
    _ = compT (unpack6 r) (unpack6 s) := by
        exact (List.map_map (g := evalV (unpack6 r)) (f := fun i => s / 64 ^ i % 64)
          (l := List.range 6)).symm


private theorem eAndB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

private theorem eOrB_iff {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [orB]

private theorem eNotB_iff {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> simp [notB]

private theorem eImpB_iff {a b : Bool} : impB a b = true ↔ (a = true → b = true) := by
  cases a <;> simp [impB]

private theorem eEqN_iff {a b : ℕ} : eqN a b = true ↔ a = b := by
  change Nat.beq a b = true ↔ _
  exact ⟨Nat.eq_of_beq_eq_true, fun h => by subst h; exact Nat.beq_refl a⟩

private theorem eAllN_iff {m : ℕ} {f : ℕ → Bool} :
    allN m f = true ↔ ∀ i, i < m → f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ m ih =>
    change andB (f m) (allN m f) = true ↔ _
    rw [eAndB_iff, ih, Nat.forall_lt_succ_right, and_comm]

private theorem eAnyN_iff {m : ℕ} {f : ℕ → Bool} :
    anyN m f = true ↔ ∃ i, i < m ∧ f i = true := by
  induction m with
  | zero =>
    refine ⟨fun h => ?_, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero _)⟩
    change false = true at h
    exact absurd h (by decide)
  | succ m ih =>
    change orB (f m) (anyN m f) = true ↔ _
    rw [eOrB_iff, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨m, Nat.lt_succ_self m, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h

private theorem letB_eq (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by cases y <;> rfl

private theorem lkk (r s : ℕ) {x : ℕ} (hx : x < 64) :
    lk (tabK r) (lk (tabK s) x) = evalV (unpack6 r) (evalV (unpack6 s) x) := by
  rw [lk_tabK s hx, lk_tabK r (evalV_lt s x)]

private theorem idT_getD : ∀ i < 6, idT.getD i 0 = 2 ^ i := by decide

private theorem compT_length (a b : List ℕ) : (compT a b).length = b.length := by
  simp [compT]

private theorem invT_of (r s : ℕ) (h : isInvT (compT (unpack6 r) (unpack6 s)) = true) :
    invT (tabK r) (tabK s) = true := by
  have h' : compT (compT (unpack6 r) (unpack6 s)) (compT (unpack6 r) (unpack6 s)) = idT ∧
      compT (unpack6 r) (unpack6 s) ≠ idT := by
    simpa [isInvT] using h
  obtain ⟨h1, h2⟩ := h'
  have hL : (compT (unpack6 r) (unpack6 s)).length = 6 := by
    rw [compT_length, unpack6_length]
  have hg : ∀ i < 6, evalV (unpack6 r) (evalV (unpack6 s) (evalV (unpack6 r)
      (evalV (unpack6 s) (2 ^ i)))) = 2 ^ i := by
    intro i hi
    have e1 : (compT (compT (unpack6 r) (unpack6 s)) (compT (unpack6 r) (unpack6 s))).getD i 0 =
        idT.getD i 0 := by rw [h1]
    rw [compT_getD _ _ (by rw [hL]; exact hi), compT_basis r s hi, evalV_compT,
      Nat.mod_eq_of_lt (evalV_lt r (evalV (unpack6 s) (2 ^ i))), idT_getD i hi] at e1
    exact e1
  unfold invT
  rw [eAndB_iff]
  constructor
  · rw [eAllN_iff]
    intro i hi
    rw [eEqN_iff]
    have hx := two_pow_lt hi
    change lk (tabK r) (lk (tabK s) (lk (tabK r) (lk (tabK s) (2 ^ i)))) = 2 ^ i
    rw [lkk r s hx, lkk r s (evalV_lt r _)]
    exact hg i hi
  · by_contra hcon
    apply h2
    have hcon' : ∀ i < 6, evalV (unpack6 r) (evalV (unpack6 s) (2 ^ i)) = 2 ^ i := by
      intro i hi
      by_contra hne
      apply hcon
      rw [eAnyN_iff]
      refine ⟨i, hi, ?_⟩
      rw [eNotB_iff, Bool.eq_false_iff, ne_eq, eEqN_iff]
      change ¬ lk (tabK r) (lk (tabK s) (2 ^ i)) = 2 ^ i
      rw [lkk r s (two_pow_lt hi)]
      exact hne
    refine List.ext_getElem (by rw [hL]; rfl) fun i h1 h2 => ?_
    have hi : i < 6 := by rw [hL] at h1; exact h1
    have := compT_basis r s hi
    rw [List.getD_eq_getElem _ _ h1, hcon' i hi] at this
    rw [this]
    have := idT_getD i hi
    rw [List.getD_eq_getElem _ _ h2] at this
    exact this.symm


private theorem wp_eq (v : ℕ) : wp v = wpart v := by
  unfold wp wpart
  rw [Nat.or_assoc]
  rfl

private theorem mkv_vals : mkv 0 1 = 2 ∧ mkv 0 2 = 8 ∧ mkv 0 4 = 32 := by decide

private theorem presT_false (L : List ℕ) (h : presT false L = true) :
    wpart (evalV L 2) = 0 ∧ wpart (evalV L 8) = 0 ∧ wpart (evalV L 32) = 0 := by
  simp [presT, imNl, List.range_succ, mkv_vals] at h
  exact h

private theorem unpack6_omK : unpack6 omK = omT := by decide +kernel

private theorem unpack6_idK : unpack6 idK = idT := by decide +kernel

private theorem unpack6_om2K : unpack6 om2K = compT omT omT := by decide +kernel

private theorem omT_length : omT.length = 6 := by decide

private theorem presTT_of (u : Bool) (r s : ℕ) (h : presT u (compT (unpack6 r) (unpack6 s)) = true) :
    presTT (if u then 1 else 0) (tabK r) (tabK s) = true := by
  cases u
  · have h' := presT_false _ h
    have hv : ∀ x, x < 64 → wpart (evalV (compT (unpack6 r) (unpack6 s)) x) = 0 →
        eqN (wp (lk (tabK r) (lk (tabK s) x))) 0 = true := by
      intro x hx hw
      rw [eEqN_iff, wp_eq, lkk r s hx]
      rw [evalV_compT, Nat.mod_eq_of_lt hx] at hw
      exact hw
    change andB (inNl (lk (tabK r) (lk (tabK s) 2))) (andB (inNl (lk (tabK r) (lk (tabK s) 8)))
      (inNl (lk (tabK r) (lk (tabK s) 32)))) = true
    rw [eAndB_iff, eAndB_iff]
    exact ⟨hv 2 (by decide) h'.1, hv 8 (by decide) h'.2.1, hv 32 (by decide) h'.2.2⟩
  · have h' : compT (compT (unpack6 r) (unpack6 s)) omT =
        compT omT (compT (unpack6 r) (unpack6 s)) := by
      simpa [presT] using h
    have hL : (compT (unpack6 r) (unpack6 s)).length = 6 := by
      rw [compT_length, unpack6_length]
    change commT (tabK r) (tabK s) omTab omK = true
    unfold commT
    rw [eAllN_iff]
    intro i hi
    rw [eEqN_iff]
    have e1 : (compT (compT (unpack6 r) (unpack6 s)) omT).getD i 0 =
        (compT omT (compT (unpack6 r) (unpack6 s))).getD i 0 := by rw [h']
    have hω : fld6 omK i = omT.getD i 0 := by rw [← unpack6_getD omK hi, unpack6_omK]
    rw [compT_getD _ _ (by rw [omT_length]; exact hi), ← hω, evalV_compT,
      Nat.mod_eq_of_lt (fld6_lt _ _), compT_getD _ _ (by rw [hL]; exact hi),
      compT_basis r s hi] at e1
    change lk (tabK r) (lk (tabK s) (fld6 omK i)) =
      lk (tabK omK) (lk (tabK r) (lk (tabK s) (2 ^ i)))
    rw [lkk r s (fld6_lt _ _), lkk r s (two_pow_lt hi), lk_tabK omK (evalV_lt _ _), unpack6_omK]
    exact e1


private theorem xp_eq (v : ℕ) : xp v = xpart v := by
  unfold xp xpart
  rw [Nat.or_assoc]
  rfl

private theorem outK_eq (a b : ℕ) : outK a b = outer a b := by
  unfold outK outer
  rw [bit_eq, bit_eq, bit_eq, Nat.xor_assoc]
  have h1 : ∀ (c : Bool) (x : ℕ), Nat.mul (if c then 1 else 0) x = if c then x else 0 := by
    intro c x; cases c <;> simp
  rw [h1, h1, h1]
  rfl

private theorem qK_eq (u : Bool) (v : ℕ) : qK (if u then 1 else 0) v = qOf u v := by
  unfold qK qOf
  rw [outK_eq, outK_eq, outK_eq, wp_eq, xp_eq, Nat.xor_assoc]
  cases u <;> simp

private theorem outK_lt (a b : ℕ) : outK a b < 512 := by
  have hb : b &&& 7 < 8 := Nat.lt_succ_of_le (Nat.and_le_right)
  have h1 : ∀ (j : ℕ) (x : ℕ), x < 512 → Nat.mul (bit a j) x < 512 := by
    intro j x hx
    rw [bit_eq]
    split <;> simp [hx]
  unfold outK
  refine Nat.xor_lt_two_pow (n := 9) (h1 0 _ ?_) (Nat.xor_lt_two_pow (n := 9) (h1 1 _ ?_) (h1 2 _ ?_))
  · show b &&& 7 < 512
    omega
  · show (b &&& 7) <<< 3 < 512
    rw [Nat.shiftLeft_eq]; omega
  · show (b &&& 7) <<< 6 < 512
    rw [Nat.shiftLeft_eq]; omega


private theorem qK_lt {u : ℕ} (hu : u ≤ 1) (v : ℕ) : qK u v < 512 := by
  unfold qK
  refine Nat.xor_lt_two_pow (n := 9) (outK_lt _ _) (Nat.xor_lt_two_pow (n := 9) (outK_lt _ _) ?_)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl
  · show 0 * _ < 512; simp
  · show 1 * _ < 512; simpa using outK_lt _ _

private theorem bEntK_letN (y : ℕ) (k : ℕ → ℕ) : bEntK.letN y k = k y := by cases y <;> rfl

private theorem bEntK_eq (u P k : ℕ) : bEntK u P k =
    if k / 3 = k % 3 then qK u (evV P (4 ^ (k / 3)))
    else Nat.xor (qK u (evV P (4 ^ (k / 3) + 2 * 4 ^ (k % 3))))
      (Nat.xor (qK u (evV P (4 ^ (k / 3)))) (u * qK u (evV P (2 * 4 ^ (k % 3))))) := by
  unfold bEntK
  rw [bEntK_letN, bEntK_letN]
  cases hb : Nat.beq (Nat.div k 3) (Nat.mod k 3)
  · have h : ¬ (k / 3 = k % 3) := Nat.ne_of_beq_eq_false hb
    rw [if_neg h]
    rfl
  · have h : k / 3 = k % 3 := Nat.eq_of_beq_eq_true hb
    rw [if_pos h]
    rfl

private theorem bEntK_lt {u : ℕ} (hu : u ≤ 1) (P k : ℕ) : bEntK u P k < 512 := by
  rw [bEntK_eq]
  split
  · exact qK_lt hu _
  · exact Nat.xor_lt_two_pow (n := 9) (qK_lt hu _) (Nat.xor_lt_two_pow (n := 9) (qK_lt hu _)
      (by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hu with rfl | rfl
        · simp
        · simpa using qK_lt hu _))


private theorem evalV_zero (l : List ℕ) : evalV l 0 = 0 := by
  have := evalV_xor l 0 0
  simpa using this

private theorem qOf_zero (u : Bool) : qOf u 0 = 0 := by cases u <;> decide

private theorem mkv_A : ∀ i < 3, mkv (2 ^ i) 0 = 4 ^ i := by decide
private theorem mkv_B : ∀ i < 3, ∀ j < 3, mkv (2 ^ i) (2 ^ j) = 4 ^ i + 2 * 4 ^ j := by decide
private theorem mkv_C : ∀ j < 3, mkv 0 (2 ^ j) = 2 * 4 ^ j := by decide

private theorem bOf_getD_diag (u : Bool) (l : List ℕ) {k : ℕ} (hk : k < 9) (hd : k / 3 = k % 3) :
    (bOf u l).getD k 0 = qOf u (evalV l (mkv (2 ^ (k / 3)) 0)) := by
  simp [bOf, spanW, List.getD_eq_getElem?_getD, hk, hd, evalV_zero, qOf_zero]

private theorem bOf_getD_off (u : Bool) (l : List ℕ) {k : ℕ} (hk : k < 9) (hd : ¬ k / 3 = k % 3) :
    (bOf u l).getD k 0 = qOf u (evalV l (mkv (2 ^ (k / 3)) (2 ^ (k % 3)))) ^^^
      qOf u (evalV l (mkv (2 ^ (k / 3)) 0)) ^^^
      qOf u (evalV l (if u then mkv 0 (2 ^ (k % 3)) else 0)) := by
  simp [bOf, spanW, List.getD_eq_getElem?_getD, hk, hd]

private theorem bEnt_eq (u : Bool) (P : ℕ) {k : ℕ} (hk : k < 9) :
    bEntK (if u then 1 else 0) P k = (bOf u (unpack6 P)).getD k 0 := by
  rw [bEntK_eq]
  have hi : k / 3 < 3 := by omega
  have hj : k % 3 < 3 := by omega
  by_cases hd : k / 3 = k % 3
  · rw [if_pos hd, bOf_getD_diag u _ hk hd, mkv_A _ hi, qK_eq, evV_eq]
  · rw [if_neg hd, bOf_getD_off u _ hk hd, mkv_B _ hi _ hj, mkv_A _ hi]
    simp only [qK_eq, evV_eq]
    cases u
    · simp [evalV_zero, qOf_zero, Nat.xor_assoc]
    · simp [mkv_C _ hj, Nat.xor_assoc]


private theorem ite_le_one (u : Bool) : (if u then 1 else 0 : ℕ) ≤ 1 := by cases u <;> simp

private theorem unpack9_length (P : ℕ) : (unpack9 P).length = 9 := by simp [unpack9]

private theorem bOfK_pack (u : Bool) (P : ℕ) :
    bOfK (if u then 1 else 0) P = packR 9 (bEntK (if u then 1 else 0) P) 9 := rfl

private theorem bOfK_lt (u : Bool) (P : ℕ) : bOfK (if u then 1 else 0) P < 2 ^ 81 := by
  rw [bOfK_pack]
  exact (packR_spec 9 _ (fun k => bEntK_lt (ite_le_one u) P k) 9).1

private theorem bOfK_unpack (u : Bool) (P : ℕ) :
    unpack9 (bOfK (if u then 1 else 0) P) = bOf u (unpack6 P) := by
  have hlen : (bOf u (unpack6 P)).length = 9 := by simp [bOf, spanW]
  refine List.ext_getElem (by rw [unpack9_length, hlen]) fun k h1 h2 => ?_
  have hk : k < 9 := by rw [unpack9_length] at h1; exact h1
  have e1 := (packR_spec 9 _ (fun k => bEntK_lt (ite_le_one u) P k) 9).2 k hk
  rw [← bOfK_pack] at e1
  have e2 := bEnt_eq u P hk
  rw [List.getD_eq_getElem _ _ h2] at e2
  rw [← e2, ← e1]
  exact (by simp [unpack9, fld9_eq] :
    (unpack9 (bOfK (if u then 1 else 0) P))[k] = fld9 (bOfK (if u then 1 else 0) P) k)

private theorem eq_of_fld9 {P Q : ℕ} (hP : P < 2 ^ 81) (hQ : Q < 2 ^ 81)
    (h : ∀ i < 9, fld9 P i = fld9 Q i) : P = Q := by
  refine Nat.eq_of_testBit_eq fun m => ?_
  by_cases hm : m < 81
  · have hi : m / 9 < 9 := by omega
    have e : ∀ X : ℕ, fld9 X (m / 9) = (X >>> (9 * (m / 9))) &&& (2 ^ 9 - 1) := fun X => rfl
    have := congrArg (fun x => x.testBit (m % 9)) (h (m / 9) hi)
    simp only [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
    have hm9 : m % 9 < 9 := Nat.mod_lt _ (by decide)
    have hmm : 9 * (m / 9) + m % 9 = m := by omega
    simpa [hm9, hmm] using this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hP (Nat.pow_le_pow_right Nat.two_pos (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hQ (Nat.pow_le_pow_right Nat.two_pos (by omega)))]


private theorem bMul_unpack9 (A B : ℕ) :
    bMul (unpack9 A) (unpack9 B) = unpack9 (compE9 A B) := by
  have hspec := (packR_spec 9 (fun k => evE A (fld9 B k))
    (fun k => by rw [evE_eq]; exact evalE_lt A _) 9).2
  have hent : ∀ i < 9, compE9 A B / 512 ^ i % 512 = evalE (unpack9 A) (B / 512 ^ i % 512) := by
    intro i hi
    have h1 := hspec i hi
    rw [evE_eq, fld9_eq] at h1
    rw [← fld9_eq]
    exact h1
  have e1 : bMul (unpack9 A) (unpack9 B) =
      (List.range 9).map (fun i => evalE (unpack9 A) (B / 512 ^ i % 512)) := by
    simp only [bMul, unpack9, List.map_map, Function.comp_def]
  rw [e1]
  have e2 : unpack9 (compE9 A B) = (List.range 9).map (fun i => compE9 A B / 512 ^ i % 512) := by
    simp only [unpack9]
  rw [e2]
  refine List.map_congr_left fun i hi => ?_
  rw [hent i (List.mem_range.1 hi)]

private theorem unpack9_idEK : unpack9 idEK = idE := by decide +kernel

private theorem idE_getD : ∀ i < 9, idE.getD i 0 = 2 ^ i := by decide

private theorem bMul_getD (A B : List ℕ) {j : ℕ} (hj : j < B.length) :
    (bMul A B).getD j 0 = evalE A (B.getD j 0) := by
  simp [bMul, List.getD_eq_getElem?_getD, hj]

private theorem left_inv_of (A X : ℕ) (h : bMul (unpack9 A) (unpack9 X) = idE) (e : ℕ) :
    evalE (unpack9 A) (evalE (unpack9 X) (e % 512)) = e % 512 := by
  have hg : ∀ x y, evalE (unpack9 A) (evalE (unpack9 X) (x ^^^ y)) =
      evalE (unpack9 A) (evalE (unpack9 X) x) ^^^ evalE (unpack9 A) (evalE (unpack9 X) y) := by
    intro x y; rw [evalE_xor, evalE_xor]
  have key := lin_eq_xorBits (fun e => evalE (unpack9 A) (evalE (unpack9 X) e)) hg 9 e
  have hb : ∀ j < 9, evalE (unpack9 A) (evalE (unpack9 X) (2 ^ j)) = 2 ^ j := by
    intro j hj
    have e1 : (bMul (unpack9 A) (unpack9 X)).getD j 0 = idE.getD j 0 := by rw [h]
    rw [bMul_getD _ _ (by rw [unpack9_length]; exact hj), idE_getD j hj] at e1
    rw [evalE_basis _ hj]
    exact e1
  rw [xorBits_congr 9 e hb] at key
  have := CFSG.EvenSmallLie.OmegaEight.SpBranch.xorBits_two_pow 9 e
  rw [this] at key
  exact key

private theorem surj_of_inj (n : ℕ) (G : ℕ → ℕ) (hG : ∀ x < n, G x < n)
    (hinj : ∀ x < n, ∀ y < n, G x = G y → x = y) : ∀ y < n, ∃ x < n, G x = y := by
  intro y hy
  by_contra hcon'
  have hcon : ∀ x < n, G x ≠ y := fun x hx h => hcon' ⟨x, hx, h⟩
  have hnd : ((List.range n).map G).Nodup :=
    List.Nodup.map_on (fun x hx y hy' h => hinj x (List.mem_range.1 hx) y (List.mem_range.1 hy') h)
      List.nodup_range
  have hsub : (List.range n).map G ⊆ (List.range n).erase y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    have hxn := List.mem_range.1 hx
    refine (List.mem_erase_of_ne (hcon x hxn)).2 (List.mem_range.2 (hG x hxn))
  have hle := hnd.length_le_of_subset hsub
  rw [List.length_map, List.length_range, List.length_erase_of_mem (List.mem_range.2 hy),
    List.length_range] at hle
  omega

private theorem inv_unique (A b Bs : ℕ) (hb : b < 2 ^ 81) (hBs : Bs < 2 ^ 81)
    (h1 : compE9 A b = idEK) (h2 : bMul (unpack9 A) (unpack9 Bs) = idE) : Bs = b := by
  have h1' : bMul (unpack9 A) (unpack9 b) = idE := by
    rw [bMul_unpack9, h1, unpack9_idEK]
  have hAb : ∀ e < 512, evalE (unpack9 A) (evalE (unpack9 b) e) = e := by
    intro e he
    have := left_inv_of A b h1' e
    rwa [Nat.mod_eq_of_lt he] at this
  have hABs : ∀ e < 512, evalE (unpack9 A) (evalE (unpack9 Bs) e) = e := by
    intro e he
    have := left_inv_of A Bs h2 e
    rwa [Nat.mod_eq_of_lt he] at this
  have hinjb : ∀ x < 512, ∀ y < 512, evalE (unpack9 b) x = evalE (unpack9 b) y → x = y := by
    intro x hx y hy h
    rw [← hAb x hx, ← hAb y hy, h]
  have hsurj := surj_of_inj 512 (evalE (unpack9 b)) (fun x _ => evalE_lt _ _) hinjb
  have hinjA : ∀ x < 512, ∀ y < 512, evalE (unpack9 A) x = evalE (unpack9 A) y → x = y := by
    intro x hx y hy h
    obtain ⟨z1, hz1, rfl⟩ := hsurj x hx
    obtain ⟨z2, hz2, rfl⟩ := hsurj y hy
    rw [hAb z1 hz1, hAb z2 hz2] at h
    rw [h]
  have hagree : ∀ i < 9, (unpack9 Bs).getD i 0 = (unpack9 b).getD i 0 := by
    intro i hi
    have hi512 : 2 ^ i < 512 := lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) hi) (by decide)
    have := hinjA _ (evalE_lt Bs (2 ^ i)) _ (evalE_lt b (2 ^ i))
      ((hABs _ hi512).trans (hAb _ hi512).symm)
    rwa [evalE_basis _ hi, evalE_basis _ hi] at this
  refine eq_of_fld9 hBs hb fun i hi => ?_
  rw [← unpack9_getD _ hi, ← unpack9_getD _ hi]
  exact hagree i hi


private theorem eMemK_iff {x : ℕ} {L : List ℕ} : memK x L = true ↔ x ∈ L := by
  induction L with
  | nil =>
    refine ⟨fun h => ?_, fun h => absurd h List.not_mem_nil⟩
    change false = true at h
    exact absurd h (by decide)
  | cons y t ih =>
    change orB (Nat.beq y x) (memK x t) = true ↔ _
    rw [List.mem_cons, ← ih]
    cases h : Nat.beq y x
    · have hne : x ≠ y := fun e => Nat.ne_of_beq_eq_false h e.symm
      change memK x t = true ↔ _
      simp [hne]
    · have he : x = y := (Nat.eq_of_beq_eq_true h).symm
      change true = true ↔ _
      simp [he]

private theorem rtK_cons (r : ℕ) (t : List ℕ) (b : ℕ) (t' : List ℕ) :
    rtK (r :: t) (b :: t') = (tabK r, b) :: rtK t t' := rfl

private theorem invsK_sound (U : ℕ) : ∀ (R BR : List ℕ), invsK U R BR = true →
    ∀ r ∈ R, ∃ b, (tabK r, b) ∈ rtK R BR ∧ b < 2 ^ 81 ∧ compE9 (bOfK U r) b = idEK := by
  intro R
  induction R with
  | nil => intro BR _ r hr; exact absurd hr List.not_mem_nil
  | cons r t ih =>
    intro BR h x hx
    cases BR with
    | nil =>
      change false = true at h
      exact absurd h (by decide)
    | cons b t' =>
      change andB (andB (Nat.blt b 2417851639229258349412352)
        (eqN (compE9 (bOfK U r) b) idEK)) (invsK U t t') = true at h
      rw [eAndB_iff, eAndB_iff, Nat.blt_eq, eEqN_iff] at h
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, by rw [rtK_cons]; exact List.mem_cons_self .., h.1.1, h.1.2⟩
      · obtain ⟨b', hb', h1, h2⟩ := ih t' h.2 x hx
        exact ⟨b', by rw [rtK_cons]; exact List.mem_cons_of_mem _ hb', h1, h2⟩

private theorem allL2_iff {L : List (ℕ × ℕ)} {f : ℕ → ℕ → Bool} :
    elemT.allL2 L f = true ↔ ∀ p ∈ L, f p.1 p.2 = true := by
  induction L with
  | nil => exact ⟨fun _ p hp => absurd hp List.not_mem_nil, fun _ => rfl⟩
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    change andB (f a b) (elemT.allL2 t f) = true ↔ _
    rw [eAndB_iff, ih, List.forall_mem_cons]

private theorem elemT_sound (u : ℕ) (RT : List (ℕ × ℕ)) (I : List ℕ) (Ts Bs : ℕ)
    (h : elemT u RT I Ts Bs = true) : ∀ p ∈ RT, kerT u p.1 Ts p.2 Bs = true ∧
      impB (andB (invT p.1 Ts) (presTT u p.1 Ts)) (memK (packT p.1 Ts) I) = true := by
  have h' : elemT.allL2 RT (fun Tr Bri => andB (kerT u Tr Ts Bri Bs)
      (impB (andB (invT Tr Ts) (presTT u Tr Ts)) (memK (packT Tr Ts) I))) = true := h
  intro p hp
  have := allL2_iff.1 h' p hp
  exact eAndB_iff.1 this


theorem elem_sound' (u : Bool) {R S BR I : List ℕ}
    (hinv : invsK (if u then 1 else 0) R BR = true)
    (h : ∀ s ∈ S, elemT (if u then 1 else 0) (rtK R BR) I (tabK s)
      (bOfK (if u then 1 else 0) s) = true) :
    ∀ r ∈ R, ∀ s ∈ S,
      (u = true → bMul (bOf u (unpack6 r)) (bOf u (unpack6 s)) = idE →
        compT (unpack6 r) (unpack6 s) = idT ∨ compT (unpack6 r) (unpack6 s) = omT ∨
          compT (unpack6 r) (unpack6 s) = compT omT omT) ∧
      (isInvT (compT (unpack6 r) (unpack6 s)) = true →
        presT u (compT (unpack6 r) (unpack6 s)) = true →
          compT (unpack6 r) (unpack6 s) ∈ I.map unpack6) := by
  intro r hr s hs
  obtain ⟨b, hmem, hb, hcomp⟩ := invsK_sound _ R BR hinv r hr
  obtain ⟨hker, himp⟩ := elemT_sound _ _ _ _ _ (h s hs) _ hmem
  constructor
  · intro hu hmul
    subst hu
    have hbs : bOfK (if true then 1 else 0) s = b := by
      refine inv_unique (bOfK (if true then 1 else 0) r) b _ (by simpa using hb)
        (bOfK_lt true s) hcomp ?_
      rw [bOfK_unpack, bOfK_unpack]
      exact hmul
    unfold kerT at hker
    rw [eImpB_iff] at hker
    have hk := hker (by
      rw [eAndB_iff]
      exact ⟨rfl, eEqN_iff.2 hbs⟩)
    rw [letB_eq, eOrB_iff, eOrB_iff, eEqN_iff, eEqN_iff, eEqN_iff] at hk
    have hu := packT_unpack r s
    rcases hk with hk | hk | hk
    · left; rw [← hu, hk, unpack6_idK]
    · right; left; rw [← hu, hk, unpack6_omK]
    · right; right; rw [← hu, hk, unpack6_om2K]
  · intro hI hp
    rw [eImpB_iff] at himp
    have := himp (by rw [eAndB_iff]; exact ⟨invT_of r s hI, presTT_of u r s hp⟩)
    rw [eMemK_iff] at this
    rw [← packT_unpack r s]
    exact List.mem_map_of_mem this

end CFSG.KC.Misc.Oq

end
