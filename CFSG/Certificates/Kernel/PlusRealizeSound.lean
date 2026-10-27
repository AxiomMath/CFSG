module

public import Certificates.Data.Kernel.PlusRealizeK
public import CFSG.OddTranspositions.PartThree.Eleven.Plus.RealizeCheck
import all CFSG.OddTranspositions.PartThree.Eleven.Plus.RealizeCheck

public section

namespace CFSG.KC.PlusRealizeK

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.PlusRealize
open CFSG.RankThree.Native Matrix

attribute [-instance] CFSG.RankThree.Native.fact_prime_five

theorem zinv_mul {x : ZMod 5} (h : x ≠ 0) : x⁻¹ * x = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact inv_mul_cancel₀ h

theorem zmul_inv' {x : ZMod 5} (h : x ≠ 0) : x * x⁻¹ = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact mul_inv_cancel₀ h

theorem zmul_inv (x y : ZMod 5) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact mul_inv x y

theorem allL_iff {α : Type} {p : α → Bool} {L : List α} :
    allL p L = true ↔ ∀ x ∈ L, p x = true := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx (List.not_mem_nil), fun _ => rfl⟩
  | cons x xs ih =>
    change (p x && allL p xs) = true ↔ _
    rw [Bool.and_eq_true, ih, List.forall_mem_cons]

theorem anyL_iff {α : Type} {p : α → Bool} {L : List α} :
    anyL p L = true ↔ ∃ x ∈ L, p x = true := by
  induction L with
  | nil =>
    exact ⟨fun h => absurd (show false = true from h) Bool.false_ne_true,
      fun ⟨x, hx, _⟩ => absurd hx List.not_mem_nil⟩
  | cons x xs ih =>
    change (p x || anyL p xs) = true ↔ _
    rw [Bool.or_eq_true, ih]
    simp

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ k < n, f k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero _), fun _ => rfl⟩
  | succ n ih =>
    change (f n && allN n f) = true ↔ _
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h2 k h
      · exact h ▸ h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem pairwise_of_pw {α : Type} {R : α → α → Bool} {L : List α} (h : pw R L = true) :
    L.Pairwise (fun x y => R x y = true) := by
  induction L with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    have h' : (allL (R x) xs && pw R xs) = true := h
    rw [Bool.and_eq_true, allL_iff] at h'
    exact List.Pairwise.cons h'.1 (ih h'.2)

theorem getL_eq (t : Nat) (L : List (List Nat)) : getL t L = L.getD t [] := by
  induction L generalizing t with
  | nil => simp [getL]
  | cons x xs ih =>
    cases t with
    | zero => rfl
    | succ k =>
      change getL k xs = _
      rw [ih k]
      simp

theorem on4_spec {f : Nat → Nat → Nat → Nat → Bool} {x : List Nat} (h : on4 f x = true) :
    ∃ a b c d, x = [a, b, c, d] ∧ f a b c d = true := by
  rcases x with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, x⟩⟩⟩⟩⟩
  · exact absurd (show false = true from h) Bool.false_ne_true
  · exact absurd (show false = true from h) Bool.false_ne_true
  · exact absurd (show false = true from h) Bool.false_ne_true
  · exact absurd (show false = true from h) Bool.false_ne_true
  · exact ⟨a, b, c, d, rfl, h⟩
  · exact absurd (show false = true from h) Bool.false_ne_true

theorem eqN4_spec {x : List Nat} {a b c d : Nat} (h : eqN4 x a b c d = true) :
    x = [a, b, c, d] := by
  obtain ⟨p, q, r, s, rfl, h⟩ := on4_spec h
  have h' : (Nat.beq p a && Nat.beq q b && Nat.beq r c && Nat.beq s d) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4]

theorem leadN_cases (a b c d : Nat) :
    leadN a b c d = a ∨ leadN a b c d = b ∨ leadN a b c d = c ∨ leadN a b c d = d := by
  unfold leadN
  cases Nat.beq a 0 <;> cases Nat.beq b 0 <;> cases Nat.beq c 0 <;> simp

@[expose] def dv4 (a b c d : Nat) : Fin 4 → ZMod 5 := ![(a : ZMod 5), b, c, d]

theorem form_eq (x y : Fin 4 → ZMod 5) :
    fiveForm 3 true x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 - x 3 * y 3 := by
  simp only [fiveForm, Fin.sum_univ_three, ↓reduceIte, one_mul]
  rfl

theorem h5 : (5 : ZMod 5) = 0 := rfl

theorem form_symm (x y : Fin 4 → ZMod 5) : fiveForm 3 true x y = fiveForm 3 true y x := by
  rw [form_eq, form_eq]
  ring

theorem form_sub_smul_left (x y z : Fin 4 → ZMod 5) (c : ZMod 5) :
    fiveForm 3 true (x - c • y) z = fiveForm 3 true x z - c * fiveForm 3 true y z := by
  simp only [form_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem form_sub_smul_right (x y z : Fin 4 → ZMod 5) (c : ZMod 5) :
    fiveForm 3 true x (y - c • z) = fiveForm 3 true x y - c * fiveForm 3 true x z := by
  simp only [form_eq, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem form_smul_left (x z : Fin 4 → ZMod 5) (c : ZMod 5) :
    fiveForm 3 true (c • x) z = c * fiveForm 3 true x z := by
  simp only [form_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem form_smul_right (x z : Fin 4 → ZMod 5) (c : ZMod 5) :
    fiveForm 3 true x (c • z) = c * fiveForm 3 true x z := by
  simp only [form_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem dv0 (a b c d : Nat) : dv4 a b c d 0 = (a : ZMod 5) := rfl
theorem dv1 (a b c d : Nat) : dv4 a b c d 1 = (b : ZMod 5) := rfl
theorem dv2 (a b c d : Nat) : dv4 a b c d 2 = (c : ZMod 5) := rfl
theorem dv3 (a b c d : Nat) : dv4 a b c d 3 = (d : ZMod 5) := rfl

theorem qN_cast (a b c d : Nat) :
    ((qN a b c d : Nat) : ZMod 5) = fiveForm 3 true (dv4 a b c d) (dv4 a b c d) := by
  rw [form_eq, qN, ZMod.natCast_mod, dv0, dv1, dv2, dv3]
  push_cast
  linear_combination ((d : ZMod 5) * d) * h5

theorem bN_cast (a b c d e f g h : Nat) :
    ((bN a b c d e f g h : Nat) : ZMod 5) = fiveForm 3 true (dv4 a b c d) (dv4 e f g h) := by
  rw [form_eq, bN, ZMod.natCast_mod, dv0, dv1, dv2, dv3, dv0, dv1, dv2, dv3]
  push_cast
  linear_combination ((d : ZMod 5) * h) * h5

theorem lin1 (q e r a : Nat) :
    ((((q * e + r * a) % 5 : Nat)) : ZMod 5) = (q : ZMod 5) * e + (r : ZMod 5) * a := by
  rw [ZMod.natCast_mod]
  push_cast
  ring

theorem dv4_lin (q r a b c d e f g h : Nat) :
    dv4 ((q * e + r * a) % 5) ((q * f + r * b) % 5) ((q * g + r * c) % 5) ((q * h + r * d) % 5) =
      (q : ZMod 5) • dv4 e f g h + (r : ZMod 5) • dv4 a b c d := by
  funext k
  fin_cases k
  · exact lin1 q e r a
  · exact lin1 q f r b
  · exact lin1 q g r c
  · exact lin1 q h r d

@[expose] def sg (u x : Fin 4 → ZMod 5) : Fin 4 → ZMod 5 :=
  x - (2 * (fiveForm 3 true u u)⁻¹ * fiveForm 3 true x u) • u

theorem reflMat_mulVec (u x : Fin 4 → ZMod 5) : reflMat u *ᵥ x = sg u x := by
  funext a
  simp only [mulVec, dotProduct, reflMat, Fin.sum_univ_four, sg, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, form_eq, Jv]
  fin_cases a <;> simp <;> ring

theorem mat_ext {M N : Matrix (Fin 4) (Fin 4) (ZMod 5)} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

theorem sg_sg {u : Fin 4 → ZMod 5} (hu : fiveForm 3 true u u ≠ 0) (x : Fin 4 → ZMod 5) :
    sg u (sg u x) = x := by
  have hq : (fiveForm 3 true u u)⁻¹ * fiveForm 3 true u u = 1 := zinv_mul hu
  have e : sg u (sg u x) = sg u x - (2 * (fiveForm 3 true u u)⁻¹ *
      (fiveForm 3 true x u - (2 * (fiveForm 3 true u u)⁻¹ * fiveForm 3 true x u) *
        fiveForm 3 true u u)) • u := by
    rw [sg, sg, form_sub_smul_left]
  rw [e]
  funext a
  simp only [sg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (4 * (fiveForm 3 true u u)⁻¹ * fiveForm 3 true x u * u a) * hq

theorem form_sg_left (u x y : Fin 4 → ZMod 5) :
    fiveForm 3 true (sg u x) y = fiveForm 3 true x (sg u y) := by
  rw [sg, sg, form_sub_smul_left, form_sub_smul_right, form_symm u y]
  ring

theorem sg_sub_smul (u a b : Fin 4 → ZMod 5) (c : ZMod 5) :
    sg u (a - c • b) = sg u a - c • sg u b := by
  rw [sg, sg, sg, form_sub_smul_left]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem form_sg_sg {u : Fin 4 → ZMod 5} (hu : fiveForm 3 true u u ≠ 0) (v : Fin 4 → ZMod 5) :
    fiveForm 3 true (sg u v) (sg u v) = fiveForm 3 true v v := by
  rw [form_sg_left, sg_sg hu]

theorem sg_conj {u : Fin 4 → ZMod 5} (hu : fiveForm 3 true u u ≠ 0) (v x : Fin 4 → ZMod 5) :
    sg u (sg v (sg u x)) = sg (sg u v) x := by
  have e : sg v (sg u x) = sg u x - (2 * (fiveForm 3 true v v)⁻¹ *
      fiveForm 3 true (sg u x) v) • v := rfl
  rw [e, sg_sub_smul, sg_sg hu, form_sg_left]
  conv_rhs => rw [sg, form_sg_sg hu]

theorem sg_smul {c : ZMod 5} (hc : c ≠ 0) (w : Fin 4 → ZMod 5) : sg (c • w) = sg w := by
  funext x
  have hc' : c⁻¹ * c = 1 := zinv_mul hc
  rw [sg, sg, form_smul_left, form_smul_right, form_smul_right]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, zmul_inv]
  linear_combination (-(2 * (fiveForm 3 true w w)⁻¹ * fiveForm 3 true x w * w k) *
    (c⁻¹ * c + 1)) * hc'

theorem eq_smul_of_sg {u v : Fin 4 → ZMod 5} (hu : fiveForm 3 true u u ≠ 0)
    (h : sg u u = sg v u) : ∃ c : ZMod 5, u = c • v := by
  have hq : (fiveForm 3 true u u)⁻¹ * fiveForm 3 true u u = 1 := zinv_mul hu
  refine ⟨3 * (2 * (fiveForm 3 true v v)⁻¹ * fiveForm 3 true u v), ?_⟩
  funext a
  have ha := congrFun h a
  simp only [sg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at ha ⊢
  linear_combination (-3) * ha + (-6 * u a) * hq + (-(u a)) * h5

theorem pow4 {l : Nat} (h0 : 0 < l) (h5' : l < 5) : ((l : Nat) : ZMod 5) ^ 4 = 1 := by
  interval_cases l <;> decide

theorem dv4_norm {l : Nat} (hl : ((l : Nat) : ZMod 5) ^ 4 = 1) (a b c d : Nat) :
    dv4 a b c d = ((l : Nat) : ZMod 5) •
      dv4 (a * invN l % 5) (b * invN l % 5) (c * invN l % 5) (d * invN l % 5) := by
  have sc : ∀ x : Nat, ((x : Nat) : ZMod 5) = ((l : Nat) : ZMod 5) * ((x * invN l % 5 : Nat) : ZMod 5) := by
    intro x
    rw [ZMod.natCast_mod, invN]
    push_cast
    rw [ZMod.natCast_mod]
    push_cast
    linear_combination (-(x : ZMod 5)) * hl
  funext k
  fin_cases k
  · exact sc a
  · exact sc b
  · exact sc c
  · exact sc d

theorem normEq_spec {x : List Nat} {a b c d : Nat} (ha : a < 5) (hb : b < 5) (hc : c < 5)
    (hd : d < 5) (h : normEq x a b c d = true) :
    ∃ l : ZMod 5, l ≠ 0 ∧ ∃ p q r s, x = [p, q, r, s] ∧ dv4 a b c d = l • dv4 p q r s := by
  simp only [normEq, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨h0, h1⟩ := h
  have hl5 : leadN a b c d < 5 := by
    rcases leadN_cases a b c d with e | e | e | e <;> rw [e] <;> assumption
  have h4 := pow4 h0 hl5
  refine ⟨_, fun e => ?_, _, _, _, _, eqN4_spec h1, dv4_norm h4 a b c d⟩
  rw [e] at h4
  exact absurd h4 (by decide)

theorem decode_of_toList {w : Array Nat} {a b c d : Nat} (h : w.toList = [a, b, c, d]) :
    decode w = dv4 a b c d := by
  rcases w with ⟨l⟩
  simp only at h
  subst h
  funext k
  fin_cases k <;> rfl

theorem sq1 : IsSquare (1 : ZMod 5) := ⟨1, by decide⟩
theorem sq4 : IsSquare (4 : ZMod 5) := ⟨2, by decide⟩
theorem nsq2 : ¬IsSquare (2 : ZMod 5) := by
  rintro ⟨r, hr⟩
  fin_cases r <;> revert hr <;> decide
theorem nsq3 : ¬IsSquare (3 : ZMod 5) := by
  rintro ⟨r, hr⟩
  fin_cases r <;> revert hr <;> decide

theorem signB_spec {π : Bool} {n : Nat} (h : signB π n = true) :
    ((n : Nat) : ZMod 5) ≠ 0 ∧ (IsSquare ((n : Nat) : ZMod 5) ↔ π = true) := by
  cases π <;> simp only [signB, cond_true, cond_false, Bool.or_eq_true, Nat.beq_eq] at h <;>
    rcases h with rfl | rfl
  · exact ⟨by decide, by simp [nsq2]⟩
  · exact ⟨by decide, by simp [nsq3]⟩
  · exact ⟨by decide, by simp [sq1]⟩
  · exact ⟨by decide, by simp [sq4]⟩

theorem signB_of {π : Bool} {n : Nat} (h0 : 0 < n) (h5' : n < 5)
    (h : IsSquare ((n : Nat) : ZMod 5) ↔ π = true) : signB π n = true := by
  interval_cases n <;> cases π <;> simp_all [signB, sq1, sq4, nsq2, nsq3]

theorem vecA_toList (A : Array (Array Nat)) (hA : A.size = 60) (i : Fin 60) :
    (A[(i : Nat)]!).toList = (VSof A)[(i : Nat)]'(by simp [VSof, hA]) := by
  rw [getElem!_pos A (i : Nat) (by rw [hA]; exact i.2)]
  simp [VSof]

theorem mem_VS (A : Array (Array Nat)) (hA : A.size = 60) (i : Fin 60) :
    (A[(i : Nat)]!).toList ∈ VSof A := by
  rw [vecA_toList A hA i]
  exact List.getElem_mem _

theorem sign_at {π : Bool} {A : Array (Array Nat)} (hA : A.size = 60)
    (hs : signOK π (VSof A) = true) (i : Fin 60) :
    ∃ a b c d, (A[(i : Nat)]!).toList = [a, b, c, d] ∧ signB π (qN a b c d) = true :=
  on4_spec ((allL_iff.1 hs) _ (mem_VS A hA i))

section Sign

variable {π : Bool} {A : Array (Array Nat)} (hv : ∀ i : Fin 60, vecA π i = A[(i : Nat)]!)
  (hA : A.size = 60) (hs : signOK π (VSof A) = true)
include hv hA hs

theorem signProp_of : signProp π := by
  intro i
  obtain ⟨a, b, c, d, e, hq⟩ := sign_at hA hs i
  have : vecD π i = dv4 a b c d := by rw [vecD, hv i]; exact decode_of_toList e
  rw [this, ← qN_cast]
  exact signB_spec hq

theorem form_ne (i : Fin 60) : fiveForm 3 true (vecD π i) (vecD π i) ≠ 0 :=
  (signProp_of hv hA hs i).1

theorem f5Mat_MA (i : Fin 60) : f5Mat (MA π i) = reflMat (vecD π i) := f5Mat_reflArr _

theorem reflMat_sq (i : Fin 60) : reflMat (vecD π i) * reflMat (vecD π i) = 1 :=
  mat_ext fun x => by
    rw [← Matrix.mulVec_mulVec, reflMat_mulVec, reflMat_mulVec, sg_sg (form_ne hv hA hs i),
      Matrix.one_mulVec]

theorem validA_MA (i : Fin 60) : f5ValidA (MA π i) = true := by
  have hu : IsUnit (f5Mat (MA π i)) := by
    rw [f5Mat_MA hv hA hs i]
    exact ⟨⟨_, _, reflMat_sq hv hA hs i, reflMat_sq hv hA hs i⟩, rfl⟩
  have hd : ((f5DetZ (MA π i) : Int) : ZMod 5) ≠ 0 := by
    rw [← f5Mat_det]
    have : Fact (1 < 5) := ⟨by norm_num⟩
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero
  simp only [f5ValidA, bne_iff_ne, ne_eq]
  intro h0
  exact hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (Int.dvd_of_emod_eq_zero h0))

theorem inv_MA (i : Fin 60) : f5EqA (f5MulA (MA π i) (MA π i)) f5IdA = true := by
  apply f5EqA_of_mat_eq
  rw [f5Mat_mulA, f5Mat_idA, f5Mat_MA hv hA hs i]
  exact reflMat_sq hv hA hs i

theorem distinct_MA (hd : distOK (VSof A) = true) {i j : Fin 60} (hij : i ≠ j) :
    f5EqA (MA π i) (MA π j) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hm := f5Mat_eq_of_eqA h
  rw [f5Mat_MA hv hA hs, f5Mat_MA hv hA hs] at hm
  obtain ⟨a, b, c, d, ei, _⟩ := sign_at hA hs i
  obtain ⟨e, f, g, k, ej, _⟩ := sign_at hA hs j
  have di : vecD π i = dv4 a b c d := by rw [vecD, hv i]; exact decode_of_toList ei
  have dj : vecD π j = dv4 e f g k := by rw [vecD, hv j]; exact decode_of_toList ej
  have hsg : sg (vecD π i) (vecD π i) = sg (vecD π j) (vecD π i) := by
    rw [← reflMat_mulVec, ← reflMat_mulVec, hm]
  obtain ⟨m, hmv⟩ := eq_smul_of_sg (form_ne hv hA hs i) hsg
  rw [di, dj] at hmv
  have key : ∀ (x y : List Nat), (∀ p q r s, x = [p, q, r, s] → ∀ p' q' r' s',
      y = [p', q', r', s'] → dv4 p q r s = m • dv4 p' q' r' s' → propM x y m.val = true) := by
    intro x y p q r s hx p' q' r' s' hy he
    subst hx hy
    have c : ∀ (n n' : Nat), ((n : Nat) : ZMod 5) = m * (n' : ZMod 5) →
        Nat.beq (n % 5) (n' * m.val % 5) = true := by
      intro n n' hn
      rw [Nat.beq_eq]
      have e : ((n : Nat) : ZMod 5) = ((n' * m.val : Nat) : ZMod 5) := by
        rw [hn, Nat.cast_mul, ZMod.natCast_zmod_val]
        ring
      exact (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
    have e0 : (p : ZMod 5) = m * (p' : ZMod 5) := congrFun he 0
    have e1 : (q : ZMod 5) = m * (q' : ZMod 5) := congrFun he 1
    have e2 : (r : ZMod 5) = m * (r' : ZMod 5) := congrFun he 2
    have e3 : (s : ZMod 5) = m * (s' : ZMod 5) := congrFun he 3
    change (Nat.beq (p % 5) (p' * m.val % 5) && Nat.beq (q % 5) (q' * m.val % 5) &&
      Nat.beq (r % 5) (r' * m.val % 5) && Nat.beq (s % 5) (s' * m.val % 5)) = true
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨c _ _ e0, c _ _ e1⟩, c _ _ e2⟩, c _ _ e3⟩
  have hp := key _ _ a b c d ei e f g k ej hmv
  have hpw := List.pairwise_iff_getElem.1 (pairwise_of_pw hd)
  have hiV := vecA_toList A hA i
  have hjV := vecA_toList A hA j
  have hm5 : m.val < 5 := ZMod.val_lt m
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hl | hl
  · have := allN_iff.1 (hpw i j (by simp [VSof, hA]) (by simp [VSof, hA]) hl) m.val hm5
    simp only [← hiV, ← hjV, hp, Bool.not_true, Bool.false_and] at this
    exact Bool.false_ne_true this
  · have := allN_iff.1 (hpw j i (by simp [VSof, hA]) (by simp [VSof, hA]) hl) m.val hm5
    simp only [← hiV, ← hjV, hp, Bool.not_true, Bool.and_false] at this
    exact Bool.false_ne_true this

theorem table_MA (hT : tabOK (VSof A) (VSof plusTable) = true)
    (hR : allL (fun r : List Nat => Nat.beq r.length 60) (VSof plusTable) = true)
    (hzR : plusTable.size = 60) (i j : Fin 60) :
    f5EqA (f5MulA (f5MulA (MA π i) (MA π j)) (MA π i)) (MA π (TA i j)) = true := by
  apply f5EqA_of_mat_eq
  rw [f5Mat_mulA, f5Mat_mulA, f5Mat_MA hv hA hs, f5Mat_MA hv hA hs, f5Mat_MA hv hA hs]
  have hLi : (i : Nat) < (VSof A).length := by simp [VSof, hA]
  have hTi : (i : Nat) < (VSof plusTable).length := by simp [VSof, hzR]
  have hrow : ((VSof plusTable)[(i : Nat)]).length = 60 := by
    have := (allL_iff.1 hR) _ (List.getElem_mem hTi)
    simpa using this
  have hLj : (j : Nat) < (VSof A).length := by simp [VSof, hA]
  have hTj : (j : Nat) < ((VSof plusTable)[(i : Nat)]).length := by rw [hrow]; exact j.2
  have m1 : ((VSof A)[(i : Nat)], (VSof plusTable)[(i : Nat)]) ∈
      List.zip (VSof A) (VSof plusTable) := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hLi, hTi], by simp⟩
  have m2 : ((VSof A)[(j : Nat)], ((VSof plusTable)[(i : Nat)])[(j : Nat)]) ∈
      List.zip (VSof A) ((VSof plusTable)[(i : Nat)]) := by
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp [hLj, hTj], by simp⟩
  have ht := (allL_iff.1 ((allL_iff.1 hT) _ m1)) _ m2
  obtain ⟨a, b, c, d, ei, _⟩ := sign_at hA hs i
  obtain ⟨e, f, g, k, ej, _⟩ := sign_at hA hs j
  have hiV : (VSof A)[(i : Nat)] = [a, b, c, d] := (vecA_toList A hA i).symm.trans ei
  have hjV : (VSof A)[(j : Nat)] = [e, f, g, k] := (vecA_toList A hA j).symm.trans ej
  set t := ((VSof plusTable)[(i : Nat)])[(j : Nat)] with ht_def
  rw [hiV, hjV] at ht
  have ht' : normEq (getL t (VSof A))
      ((qN a b c d * e + 3 * bN e f g k a b c d * a) % 5)
      ((qN a b c d * f + 3 * bN e f g k a b c d * b) % 5)
      ((qN a b c d * g + 3 * bN e f g k a b c d * c) % 5)
      ((qN a b c d * k + 3 * bN e f g k a b c d * d) % 5) = true := ht
  obtain ⟨l, hl, p, q, r, s, hg, hw⟩ := normEq_spec (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) ht'
  rw [getL_eq] at hg
  have htl : t < (VSof A).length := by
    by_contra hc
    have h0 : (VSof A).getD t [] = [] := by
      simp [List.getD, List.getElem?_eq_none (by omega : (VSof A).length ≤ t)]
    rw [h0] at hg
    exact List.cons_ne_nil _ _ hg.symm
  have hgt : (VSof A)[t] = [p, q, r, s] := by
    rw [← hg]
    simp [List.getD, List.getElem?_eq_getElem htl]
  have ht60 : t < 60 := by simpa [VSof, hA] using htl
  have hTA : (TA i j : Nat) = t := by
    have e1 : plusTable[(i : Nat)]! = plusTable[(i : Nat)] :=
      getElem!_pos plusTable (i : Nat) (by rw [hzR]; exact i.2)
    have hsz : (j : Nat) < (plusTable[(i : Nat)]).size := by
      have : ((VSof plusTable)[(i : Nat)]) = (plusTable[(i : Nat)]).toList := by
        simp [VSof]
        rfl
      rw [this] at hTj
      simpa using hTj
    have e2 : (plusTable[(i : Nat)])[(j : Nat)]! = (plusTable[(i : Nat)])[(j : Nat)] :=
      getElem!_pos _ (j : Nat) hsz
    have e3 : t = (plusTable[(i : Nat)])[(j : Nat)] := by
      simp [ht_def, VSof]
      rfl
    change (Fin.ofNat 60 ((plusTable[(i : Nat)]!)[(j : Nat)]!) : Nat) = t
    rw [Fin.val_ofNat, e1, e2, ← e3]
    exact Nat.mod_eq_of_lt ht60
  have hT : TA i j = ⟨t, ht60⟩ := Fin.ext hTA
  have dT : vecD π (TA i j) = dv4 p q r s := by
    rw [vecD, hv, hT]
    exact decode_of_toList ((vecA_toList A hA ⟨t, ht60⟩).trans hgt)
  have di : vecD π i = dv4 a b c d := by rw [vecD, hv i]; exact decode_of_toList ei
  have dj : vecD π j = dv4 e f g k := by rw [vecD, hv j]; exact decode_of_toList ej
  have hu : fiveForm 3 true (dv4 a b c d) (dv4 a b c d) ≠ 0 := by
    rw [← di]; exact form_ne hv hA hs i
  have hw' : dv4 ((qN a b c d * e + 3 * bN e f g k a b c d * a) % 5)
      ((qN a b c d * f + 3 * bN e f g k a b c d * b) % 5)
      ((qN a b c d * g + 3 * bN e f g k a b c d * c) % 5)
      ((qN a b c d * k + 3 * bN e f g k a b c d * d) % 5) =
      fiveForm 3 true (dv4 a b c d) (dv4 a b c d) • sg (dv4 a b c d) (dv4 e f g k) := by
    rw [dv4_lin, Nat.cast_mul, qN_cast, bN_cast]
    have hq : fiveForm 3 true (dv4 a b c d) (dv4 a b c d) *
        (fiveForm 3 true (dv4 a b c d) (dv4 a b c d))⁻¹ = 1 := zmul_inv' hu
    funext z
    simp only [sg, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    linear_combination (fiveForm 3 true (dv4 e f g k) (dv4 a b c d) * dv4 a b c d z) * h5 +
      (2 * fiveForm 3 true (dv4 e f g k) (dv4 a b c d) * dv4 a b c d z) * hq
  have hsw : sg (dv4 a b c d) (dv4 e f g k) =
      ((fiveForm 3 true (dv4 a b c d) (dv4 a b c d))⁻¹ * l) • dv4 p q r s := by
    rw [mul_smul, ← hw, hw', smul_smul, zinv_mul hu, one_smul]
  rw [dT, di, dj]
  apply mat_ext
  intro x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [reflMat_mulVec]
  have hne : (fiveForm 3 true (dv4 a b c d) (dv4 a b c d))⁻¹ * l ≠ 0 := by
    intro h0
    have h1 := congrArg (· * fiveForm 3 true (dv4 a b c d) (dv4 a b c d)) h0
    simp only [zero_mul] at h1
    have h2 : l = 0 := by
      linear_combination h1 - l * zinv_mul hu
    exact hl h2
  rw [sg_conj hu, hsw, sg_smul hne]

theorem matProp_of (hd : distOK (VSof A) = true) (hT : tabOK (VSof A) (VSof plusTable) = true)
    (hR : allL (fun r : List Nat => Nat.beq r.length 60) (VSof plusTable) = true)
    (hzR : plusTable.size = 60) :
    matProp ((List.ofFn fun i : Fin 60 => MA π i).toArray) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i j => ?_, fun i j hij => ?_⟩
  · rw [getElem_toArray_ofFn_MA]
    exact validA_MA hv hA hs i
  · rw [getElem_toArray_ofFn_MA]
    exact inv_MA hv hA hs i
  · rw [getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA]
    exact table_MA hv hA hs hT hR hzR i j
  · rw [getElem_toArray_ofFn_MA, getElem_toArray_ofFn_MA]
    exact distinct_MA hv hA hs hd hij

theorem coverProp_of (hc : covOK π (VSof A) = true) : coverProp π := by
  intro v hq hsq
  have hv' : v = dv4 (v 0).val (v 1).val (v 2).val (v 3).val := by
    funext k
    fin_cases k
    · exact (ZMod.natCast_zmod_val (v 0)).symm
    · exact (ZMod.natCast_zmod_val (v 1)).symm
    · exact (ZMod.natCast_zmod_val (v 2)).symm
    · exact (ZMod.natCast_zmod_val (v 3)).symm
  have ha := ZMod.val_lt (v 0)
  have hb := ZMod.val_lt (v 1)
  have hc' := ZMod.val_lt (v 2)
  have hd := ZMod.val_lt (v 3)
  have hcov := allN_iff.1 (allN_iff.1 (allN_iff.1 (allN_iff.1 hc _ ha) _ hb) _ hc') _ hd
  rw [hv', ← qN_cast] at hq hsq
  have hq5 : qN (v 0).val (v 1).val (v 2).val (v 3).val < 5 := Nat.mod_lt _ (by norm_num)
  have hq0 : 0 < qN (v 0).val (v 1).val (v 2).val (v 3).val :=
    Nat.pos_of_ne_zero fun e => hq (by rw [e]; rfl)
  have hX : (Nat.blt 0 (qN (v 0).val (v 1).val (v 2).val (v 3).val) &&
      signB π (qN (v 0).val (v 1).val (v 2).val (v 3).val)) = true := by
    rw [Bool.and_eq_true, Nat.blt_eq]
    exact ⟨hq0, signB_of hq0 hq5 hsq⟩
  have hY : anyL (fun x => normEq x (v 0).val (v 1).val (v 2).val (v 3).val) (VSof A) = true := by
    have h' : (!(Nat.blt 0 (qN (v 0).val (v 1).val (v 2).val (v 3).val) &&
        signB π (qN (v 0).val (v 1).val (v 2).val (v 3).val)) ||
        anyL (fun x => normEq x (v 0).val (v 1).val (v 2).val (v 3).val) (VSof A)) = true := hcov
    rw [hX, Bool.not_true, Bool.false_or] at h'
    exact h'
  obtain ⟨x, hx, hn⟩ := anyL_iff.1 hY
  obtain ⟨l, hl, p, q, r, s, hxe, hvl⟩ := normEq_spec ha hb hc' hd hn
  obtain ⟨n, hnl, hxn⟩ := List.mem_iff_getElem.1 hx
  have hn60 : n < 60 := by simpa [VSof, hA] using hnl
  have hvd : vecD π ⟨n, hn60⟩ = dv4 p q r s := by
    rw [vecD, hv]
    exact decode_of_toList ((vecA_toList A hA ⟨n, hn60⟩).trans (hxn.trans hxe))
  refine ⟨⟨n, hn60⟩, l, hl, ?_⟩
  rw [hvd]
  conv_lhs => rw [hv']
  exact hvl

end Sign

theorem realizeCheck_of (hzT : plusSquareVecs.size = 60) (hzF : plusNonsquareVecs.size = 60)
    (hzR : plusTable.size = 60)
    (hR : allL (fun r : List Nat => Nat.beq r.length 60) (VSof plusTable) = true)
    (hsT : signOK true (VSof plusSquareVecs) = true)
    (hsF : signOK false (VSof plusNonsquareVecs) = true)
    (htT : tabOK (VSof plusSquareVecs) (VSof plusTable) = true)
    (htF : tabOK (VSof plusNonsquareVecs) (VSof plusTable) = true)
    (hdT : distOK (VSof plusSquareVecs) = true) (hdF : distOK (VSof plusNonsquareVecs) = true)
    (hcT : covOK true (VSof plusSquareVecs) = true)
    (hcF : covOK false (VSof plusNonsquareVecs) = true) :
    realizeCheck () = true := by
  have hvT : ∀ i : Fin 60, vecA true i = plusSquareVecs[(i : Nat)]! := fun _ => rfl
  have hvF : ∀ i : Fin 60, vecA false i = plusNonsquareVecs[(i : Nat)]! := fun _ => rfl
  simp only [realizeCheck, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨signProp_of hvT hzT hsT, signProp_of hvF hzF hsF⟩,
    matProp_of hvT hzT hsT hdT htT hR hzR⟩, matProp_of hvF hzF hsF hdF htF hR hzR⟩,
    coverProp_of hvT hzT hsT hcT⟩, coverProp_of hvF hzF hsF hcF⟩

end CFSG.KC.PlusRealizeK
