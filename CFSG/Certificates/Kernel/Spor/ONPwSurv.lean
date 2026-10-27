module

public import CFSG.Certificates.Kernel.Spor.ONPwSound
public import Certificates.Data.Kernel.Spor.ONPwPathK
public import Mathlib.Data.Set.Card
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KS.ONPw

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.ONNQ CFSG.KS.ONPv CFSG.KS.Words

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem nbeq {a b : Nat} (h : Bool.not (Nat.beq a b) = true) : a ≠ b := by
  intro e
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

private theorem bIf_or' {a b c : Bool} (h : Bool.rec (motive := fun _ => Bool) b a c = true) :
    (c = true ∧ a = true) ∨ (c = false ∧ b = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

private theorem allBlk0 {f : Nat → Bool} {len : Nat} (h : allBlk 0 f len = true) :
    ∀ l < len, f l = true := by
  intro l hl
  have e := allBlk_spec h l hl
  have z : Nat.add 0 l = l := Nat.zero_add l
  rwa [z] at e

private theorem allBlk_intro {b : Nat} {f : Nat → Bool} : ∀ {len : Nat},
    (∀ l < len, f (Nat.add b l) = true) → allBlk b f len = true
  | 0, _ => rfl
  | len + 1, h => (bAnd_iff _ _).2 ⟨h len (by omega), allBlk_intro fun l hl => h l (by omega)⟩

private theorem allBlk_intro0 {f : Nat → Bool} {len : Nat} (h : ∀ l < len, f l = true) :
    allBlk 0 f len = true :=
  allBlk_intro fun l hl => by
    have z : Nat.add 0 l = l := Nat.zero_add l
    rw [z]
    exact h l hl

private theorem fldE (h o m : Nat) :
    Nat.land (Nat.shiftRight h o) (2 ^ m - 1) = h / 2 ^ o % 2 ^ m := by
  rw [← Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ m

private theorem lc_ok {c m : Nat} (h : c < 2 * m) :
    letterOfCode c ≠ 0 ∧ (letterOfCode c).natAbs ≤ m := by
  unfold letterOfCode
  split <;> refine ⟨by omega, ?_⟩ <;> simp only [Int.natAbs_neg, Int.natAbs_natCast] <;> omega

private theorem decW_Lm {W m : Nat} : ∀ {L : Nat}, (∀ i < L, (W >>> (4 * i)) % 16 < 2 * m) →
    Lm m (decW W L)
  | 0, _ => rfl
  | L + 1, h => by
    unfold Lm
    rw [decW, List.all_cons, Bool.and_eq_true]
    exact ⟨decide_eq_true (lc_ok (h L (by omega))), decW_Lm fun i hi => h i (by omega)⟩

theorem codes_Lm {v m : Nat} (h : codesLt v (2 * m) = true) : Lm m (wd v) := by
  unfold codesLt at h
  unfold wd
  refine decW_Lm fun i hi => ?_
  have e := Nat.blt_eq.mp (allBlk0 h i hi)
  have f : Nat.land (Nat.shiftRight (Nat.shiftRight v 8) (Nat.mul 4 i)) 15 =
      (Nat.shiftRight v 8 >>> (4 * i)) % 16 := Nat.and_two_pow_sub_one_eq_mod _ 4
  exact f.symm.trans_lt e

@[expose] def pV (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (pv : Nat) :
    Equiv.Perm (Fin 245520) :=
  wv (fun j => sI g D (3 + j)) (wd pv)

@[expose] def lP (g : Nat → Equiv.Perm (Fin 245520)) (D : Nat → Nat) (pv k : Nat) :
    Equiv.Perm (Fin 245520) :=
  pV g D pv * sI g D 5 ^ k

theorem fWP_congr {n : Nat} {a b k : Nat → Equiv.Perm (Fin n)} (h0 : a 0 = b 0) (h2 : a 2 = b 2) :
    fWP a k = fWP b k := by
  simp only [fWP, h0, h2]

section Rec

variable {TT UU : Nat → Nat → Nat} {D : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}
  {K : Subgroup (Equiv.Perm (Fin 245520))}

theorem hWU_eq (hR : Rp TT UU g 7) (hP : PwItems D) {v : Nat} (hv : Lm 3 (wd v))
    (x : Fin 245520) : hWU TT UU D v x = ((hV g D v)⁻¹ x : Nat) :=
  iU_eq (rp_s hR hP) (Lm_mono (by omega) hv) x

theorem rp_e (hR : Rp TT UU g 7) (hP : PwItems D) {e : Nat} (he : e < 16) :
    Rp (eH TT UU D e) (eHU TT UU D e) (bE g D e) 3 :=
  fun j _ x => ⟨hW_eq hR hP (pw_lm3 hP (13 + 3 * e + j)) x,
    hWU_eq hR hP (pw_lm3 hP (13 + 3 * e + j)) x⟩

theorem rp_l (hR : Rp TT UU g 7) (hP : PwItems D) :
    Rp (lT TT UU D) (lU TT UU D) (fun j => sI g D (3 + j)) 3 :=
  fun j _ x => rp_s hR hP (3 + j) (by omega) x

theorem lA_eq (hR : Rp TT UU g 7) (hP : PwItems D) {pv : Nat} (hv : Lm 2 (wd pv)) (k : Nat)
    (x : Fin 245520) : lA TT UU D pv k x = (lP g D pv k x : Nat) := by
  unfold lA
  simp only [sN]
  rw [pw_eq (fun y => (rp_s hR hP 5 (by omega) y).1) k x]
  exact iT_eq (rp_l hR hP) (Lm_mono (by omega) hv) _

theorem lAU_eq (hR : Rp TT UU g 7) (hP : PwItems D) {pv : Nat} (hv : Lm 2 (wd pv)) (k : Nat)
    (x : Fin 245520) : lAU TT UU D pv k x = ((lP g D pv k)⁻¹ x : Nat) := by
  unfold lAU
  simp only [sN]
  rw [iU_eq (rp_l hR hP) (Lm_mono (by omega) hv) x,
    pw_eq (σ := (sI g D 5)⁻¹) (fun y => (rp_s hR hP 5 (by omega) y).2) k]
  simp only [lP, pV, mul_inv_rev, inv_pow, Equiv.Perm.mul_apply]

theorem alA_eq (hR : Rp TT UU g 7) (hP : PwItems D) {pv : Nat} (hv : Lm 2 (wd pv)) (k : Nat)
    {e j : Nat} (he : e < 16) (hj : j < 3) (x : Fin 245520) :
    alA TT UU D pv k e j x = ((lP g D pv k * bE g D e j * (lP g D pv k)⁻¹) x : Nat) := by
  unfold alA
  simp only [sN]
  rw [lAU_eq hR hP hv k x, (rp_e hR hP he j hj _).1, lA_eq hR hP hv k]
  rfl

theorem lP_mem (hK : ∀ k < 7, g k ∈ K) (hP : PwItems D) {pv : Nat} (hv : Lm 2 (wd pv))
    (k : Nat) : lP g D pv k ∈ K :=
  mul_mem (wv_mem (fun j _ => sI_mem hK hP (j := 3 + j) (by omega)) hv)
    (pow_mem (sI_mem hK hP (by omega)) _)

private theorem at_pts {f : Nat → Bool} (h : allBlk 0 (fun s => strictB (bP s) f) 3 = true) :
    f 0 = true ∧ f 227759 = true ∧ f 100817 = true := by
  have h0 : strictB (bP 0) f = true := allBlk0 h 0 (by decide)
  have h1 : strictB (bP 1) f = true := allBlk0 h 1 (by decide)
  have h2 : strictB (bP 2) f = true := allBlk0 h 2 (by decide)
  rw [sB] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem mode0_sound (hR : Rp TT UU g 7) (hP : PwItems D) {pv k e v : Nat} (he : e < 16)
    (hv : Lm 2 (wd pv)) (h : mode0 TT UU D pv k e v = true) :
    lP g D pv k * bY g D e * (lP g D pv k)⁻¹ ≠ yp g D := by
  unfold mode0 at h
  obtain ⟨hlt, hne⟩ := (bAnd_iff _ _).1 h
  obtain ⟨p, rfl⟩ : ∃ p : Fin 245520, (p : Nat) = v := ⟨⟨v, Nat.blt_eq.mp hlt⟩, rfl⟩
  intro hc
  apply nbeq hne
  simp only [sN]
  change lA TT UU D pv k (iT (eH TT UU D e) (eHU TT UU D e) (D 61) p) =
    cjA TT UU D 6 (lA TT UU D pv k p)
  rw [iT_eq (rp_e hR hP he) (pw_lm3 hP 61) p, lA_eq hR hP hv k (wv (bE g D e) (wd (D 61)) p),
    lA_eq hR hP hv k p, cjA_eq hR hP (j := 6) (by omega)]
  have hc' : lP g D pv k * bY g D e = yp g D * lP g D pv k := by
    rw [← hc, inv_mul_cancel_right]
  exact congrArg (fun σ : Equiv.Perm (Fin 245520) => (σ p : Nat)) hc'

theorem mode1_sound (hR : Rp TT UU g 7) (hP : PwItems D) (hK : ∀ k < 7, g k ∈ K)
    (hS : Sep K ⟨0, by decide⟩ ⟨227759, by decide⟩ ⟨100817, by decide⟩)
    (hx7 : xp g D ^ 7 = 1) {pv k e v : Nat} (he : e < 16) (hv : Lm 2 (wd pv))
    (h : mode1 TT UU D pv k e v = true) :
    ∃ i < 7, ∀ j < 3, lP g D pv k * bE g D e j * (lP g D pv k)⁻¹ =
      xp g D ^ i * sI g D j * (xp g D ^ i)⁻¹ := by
  unfold mode1 at h
  obtain ⟨hlt, hall⟩ := (bAnd_iff _ _).1 h
  have hv7 : v < 7 := Nat.blt_eq.mp hlt
  have hxr : ∀ x : Fin 245520, xA TT UU D x = (xp g D x : Nat) :=
    fun x => cjA_eq hR hP (j := 7) (by omega) x
  have hinv : xp g D ^ (7 - v) = (xp g D ^ v)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_add, Nat.sub_add_cancel hv7.le, hx7])
  refine ⟨v, hv7, fun j hj => ?_⟩
  have key : ∀ p : Fin 245520, Nat.beq (alA TT UU D pv k e j p)
      (strictN (pw (xA TT UU D) (7 - v) p) fun a => strictN (sT TT UU D j a) (pw (xA TT UU D) v)) =
        true → (lP g D pv k * bE g D e j * (lP g D pv k)⁻¹) p =
          (xp g D ^ v * sI g D j * (xp g D ^ v)⁻¹) p := by
    intro p hb
    have e1 := Nat.eq_of_beq_eq_true hb
    simp only [sN] at e1
    rw [alA_eq hR hP hv k he hj p, pw_eq hxr (7 - v) p, (rp_s hR hP j (by omega) _).1,
      pw_eq hxr v] at e1
    apply Fin.ext
    rw [e1, ← hinv]
    rfl
  obtain ⟨q0, q1, q2⟩ := at_pts (allBlk0 hall j hj)
  have hxK : xp g D ∈ K := cj_mem hK hP (by omega)
  refine sep_eq hS (mul_mem (mul_mem (lP_mem hK hP hv k)
    (hV_mem hK hP (pw_lm3 hP (13 + 3 * e + j)))) (inv_mem (lP_mem hK hP hv k))) (mul_mem (mul_mem (pow_mem hxK _) (sI_mem hK hP (by omega)))
      (inv_mem (pow_mem hxK _))) fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [key _ q0, key _ q1, key _ q2]

theorem mode2_sound (hR : Rp TT UU g 7) (hP : PwItems D) (hK : ∀ k < 7, g k ∈ K)
    (hS : Sep K ⟨0, by decide⟩ ⟨227759, by decide⟩ ⟨100817, by decide⟩)
    {pv k e v u0 u2 : Nat} (he : e < 16) (hv : Lm 2 (wd pv)) (hu0 : codesLt u0 6 = true)
    (hu2 : codesLt u2 6 = true) (h : mode2 TT UU D pv k e v u0 u2 = true) :
    fWP (fun j => lP g D pv k * bE g D e j * (lP g D pv k)⁻¹) (kp g D) ^ 8 ≠ 1 := by
  unfold mode2 at h
  obtain ⟨hlt, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hall, hmv⟩ := (bAnd_iff _ _).1 h
  obtain ⟨p, rfl⟩ : ∃ p : Fin 245520, (p : Nat) = v := ⟨⟨v, Nat.blt_eq.mp hlt⟩, rfl⟩
  have L0 : Lm 3 (wd u0) := codes_Lm (m := 3) hu0
  have L2 : Lm 3 (wd u2) := codes_Lm (m := 3) hu2
  have key : ∀ q : Fin 245520, bAnd(Nat.beq (alA TT UU D pv k e 0 q) (hW TT UU D u0 q),
      Nat.beq (alA TT UU D pv k e 2 q) (hW TT UU D u2 q)) = true →
      (lP g D pv k * bE g D e 0 * (lP g D pv k)⁻¹) q = hV g D u0 q ∧
        (lP g D pv k * bE g D e 2 * (lP g D pv k)⁻¹) q = hV g D u2 q := by
    intro q hq
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 hq
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [← alA_eq hR hP hv k (j := 0) he (by omega) q, ← hW_eq hR hP L0 q]
      exact Nat.eq_of_beq_eq_true a
    · rw [← alA_eq hR hP hv k (j := 2) he (by omega) q, ← hW_eq hR hP L2 q]
      exact Nat.eq_of_beq_eq_true b
  obtain ⟨q0, q1, q2⟩ := at_pts hall
  have hm : ∀ j < 3, lP g D pv k * bE g D e j * (lP g D pv k)⁻¹ ∈ K := fun j _ =>
    mul_mem (mul_mem (lP_mem hK hP hv k) (hV_mem hK hP (pw_lm3 hP (13 + 3 * e + j))))
      (inv_mem (lP_mem hK hP hv k))
  have e0 : lP g D pv k * bE g D e 0 * (lP g D pv k)⁻¹ = hV g D u0 :=
    sep_eq hS (hm 0 (by omega)) (hV_mem hK hP L0) fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [(key _ q0).1, (key _ q1).1, (key _ q2).1]
  have e2 : lP g D pv k * bE g D e 2 * (lP g D pv k)⁻¹ = hV g D u2 :=
    sep_eq hS (hm 2 (by omega)) (hV_mem hK hP L2) fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl
      exacts [(key _ q0).2, (key _ q1).2, (key _ q2).2]
  intro h1
  have hA : ∀ j < 3, ∀ x : Fin 245520, hW TT UU D (nIf(Nat.beq j 0, u0, u2)) x =
      (hV g D (nIf(Nat.beq j 0, u0, u2)) x : Nat) := by
    intro j _ x
    cases Nat.beq j 0
    · exact hW_eq hR hP L2 x
    · exact hW_eq hR hP L0 x
  apply nbeq hmv
  refine (pw_eq (fun x => fW_eq (A := fun j => hW TT UU D (nIf(Nat.beq j 0, u0, u2)))
    (a := fun j => hV g D (nIf(Nat.beq j 0, u0, u2))) hA (fun j hj x => kA_eq hR hP hj x) x)
      8 p).trans ?_
  rw [fWP_congr (a := fun j => hV g D (nIf(Nat.beq j 0, u0, u2)))
    (b := fun j => lP g D pv k * bE g D e j * (lP g D pv k)⁻¹) e0.symm e2.symm, h1]
  rfl

theorem rec_sound (hR : Rp TT UU g 7) (hP : PwItems D) (hK : ∀ k < 7, g k ∈ K)
    (hS : Sep K ⟨0, by decide⟩ ⟨227759, by decide⟩ ⟨100817, by decide⟩)
    (hx7 : xp g D ^ 7 = 1) {s n e k : Nat} (h : recOK TT UU D s = true)
    (hn : fld(D (rB s), 0, 32767) = n) (he : fld(D (rB s), 15, 15) = e)
    (hk : fld(D (rB s), 19, 3) = k) (he16 : e < 16) :
    Lm 2 (wd (D (Nat.succ (rB s)))) ∧ pathOK D (D (Nat.succ (rB s))) n = true ∧
      (lP g D (D (Nat.succ (rB s))) k * bY g D e * (lP g D (D (Nat.succ (rB s))) k)⁻¹ = yp g D →
        (∃ i < 7, ∀ j < 3, lP g D (D (Nat.succ (rB s))) k * bE g D e j *
            (lP g D (D (Nat.succ (rB s))) k)⁻¹ = xp g D ^ i * sI g D j * (xp g D ^ i)⁻¹) ∨
          fWP (fun j => lP g D (D (Nat.succ (rB s))) k * bE g D e j *
            (lP g D (D (Nat.succ (rB s))) k)⁻¹) (kp g D) ^ 8 ≠ 1) := by
  subst hn he hk
  unfold recOK at h
  simp only [sB] at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hc, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hpo, h⟩ := (bAnd_iff _ _).1 h
  have hpv : Lm 2 (wd (D (Nat.succ (rB s)))) := codes_Lm (m := 2) hc
  refine ⟨hpv, hpo, fun hcj => ?_⟩
  rcases bIf_or' h with ⟨-, h⟩ | ⟨-, h⟩
  · exact absurd hcj (mode0_sound hR hP he16 hpv h)
  · rcases bIf_or' h with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (mode1_sound hR hP hK hS hx7 he16 hpv h)
    · obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨hu0, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨hu2, h⟩ := (bAnd_iff _ _).1 h
      exact Or.inr (mode2_sound hR hP hK hS he16 hpv hu0 hu2 h)

theorem pathEq_spec {r k : Nat} (h : pathEq D r = true) (hk : fld(D (rB r), 19, 3) = k) :
    k ≤ r ∧ D (Nat.succ (rB r)) = D (Nat.succ (rB (r - k))) := by
  subst hk
  unfold pathEq at h
  simp only [sB] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem xp_pow7 (h : sI g D 7 ^ 7 = 1) : xp g D ^ 7 = 1 := by
  have key : ∀ n : Nat, xp g D ^ n = (sI g D 12)⁻¹ * sI g D 7 ^ n * sI g D 12 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, pow_succ, xp, cj]
      simp only [mul_assoc, mul_inv_cancel_left]
  rw [key, h, mul_one, inv_mul_cancel]

end Rec

@[expose] def Tup (D : Nat → Nat) (σ : Equiv.Perm (Fin 120)) (T : Nat) : Prop :=
  ∀ t < 51, ∀ x : Fin 120, (x : Nat) = tE D t → tf T t = (σ x : Nat)

@[expose] def nSig (D : Nat → Nat) (i : Nat) : Nat := fld(D (80 + i), 373, 32767)

structure TreeH (TT UU : Nat → Nat → Nat) (D : Nat → Nat) (g : Nat → Equiv.Perm (Fin 245520))
    (Mg L : Subgroup (Equiv.Perm (Fin 245520)))
    (ρ : Equiv.Perm (Fin 245520) → Equiv.Perm (Fin 120)) : Prop where
  rp : Rp TT UU g 7
  items : PwItems D
  blk : Blocks D Mg ρ
  memM : ∀ j < 5, sI g D j ∈ Mg
  rho : rhoAll TT UU D = true
  le : L ≤ Mg
  memL3 : sI g D 3 ∈ L
  memL4 : sI g D 4 ∈ L
  card : (ρ '' (L : Set (Equiv.Perm (Fin 245520)))).ncard = 20160
  ker : ∀ l ∈ L, ρ l = 1 → ∃ k < 4, l = sI g D 5 ^ k
  nodes : ∀ i < 20160, nodeOK D i = true

private theorem tup_ext {m A B : Nat} (hA : A < 2 ^ (7 * m)) (hB : B < 2 ^ (7 * m))
    (h : ∀ t < m, tf A t = tf B t) : A = B := by
  apply Nat.eq_of_testBit_eq
  intro n
  rcases Nat.lt_or_ge n (7 * m) with hn | hn
  · have key : ∀ X : Nat, X.testBit n = (tf X (n / 7)).testBit (n % 7) := by
      intro X
      have e : tf X (n / 7) = (X >>> (7 * (n / 7))) &&& (2 ^ 7 - 1) := rfl
      have h7 : n % 7 < 7 := Nat.mod_lt n (by omega)
      rw [e, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
        Nat.div_add_mod]
      simp [h7]
    rw [key A, key B, h (n / 7) (by omega)]
  · have hp : 2 ^ (7 * m) ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hA hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hB hp)]

private theorem land_lt (x m : Nat) : Nat.land x (Nat.sub (Nat.shiftLeft 1 m) 1) < 2 ^ m := by
  have s : Nat.shiftLeft 1 m = 2 ^ m := (Nat.shiftLeft_eq 1 m).trans (Nat.one_mul _)
  rw [s]
  exact (Nat.and_two_pow_sub_one_eq_mod x m).trans_lt (Nat.mod_lt _ (Nat.two_pow_pos m))

private theorem tupOf_lt (D : Nat → Nat) (i : Nat) : tupOf D i < 2 ^ (7 * 51) :=
  land_lt (D (80 + i)) (7 * 51)

section Tree

variable {TT UU : Nat → Nat → Nat} {D : Nat → Nat} {g : Nat → Equiv.Perm (Fin 245520)}
  {Mg L K : Subgroup (Equiv.Perm (Fin 245520))}
  {ρ : Equiv.Perm (Fin 245520) → Equiv.Perm (Fin 120)}

theorem tE_lo {t : Nat} (h : t < 3) : tE D t = dB D t := by
  have hb : Nat.blt t (nat_lit 3) = true := Nat.blt_eq.mpr h
  unfold tE
  rw [hb]

theorem tE_hi {e j : Nat} (hj : j < 3) : tE D (3 + 3 * e + j) = aB D e (dB D j) := by
  have hb : Nat.blt (3 + 3 * e + j) (nat_lit 3) = false :=
    Bool.eq_false_iff.mpr fun h => by
      have h' : 3 + 3 * e + j < 3 := Nat.blt_eq.mp h
      omega
  have h2 : Nat.div (Nat.sub (3 + 3 * e + j) (nat_lit 3)) (nat_lit 3) = e := by
    change (3 + 3 * e + j - 3) / 3 = e
    omega
  have h3 : Nat.mod (Nat.sub (3 + 3 * e + j) (nat_lit 3)) (nat_lit 3) = j := by
    change (3 + 3 * e + j - 3) % 3 = j
    omega
  unfold tE
  rw [hb, h2, h3]

theorem tE_lt (H : TreeH TT UU D g Mg L ρ) {t : Nat} (ht : t < 51) : tE D t < 120 := by
  rcases Nat.lt_or_ge t 3 with h3 | h3
  · rw [tE_lo h3]
    exact dB_lt H.rho h3
  · obtain ⟨e, j, hj, rfl⟩ : ∃ e j, j < 3 ∧ t = 3 + 3 * e + j :=
      ⟨(t - 3) / 3, (t - 3) % 3, Nat.mod_lt _ (by omega), by omega⟩
    have ea : aB D e (dB D j) = _ :=
      aB_eq H.rp H.items H.blk H.memM H.rho (by omega) ⟨dB D j, dB_lt H.rho hj⟩
    rw [tE_hi hj, ea]
    exact Fin.isLt _

theorem node_parts {i : Nat} (h : nodeOK D i = true) :
    (i = 0 → ∀ t < 51, tf (tupOf D i) t = tE D t) ∧
      (0 < i → fld(D (80 + i), 357, 32767) < i ∧ fld(D (80 + i), 372, 1) < 2 ∧
        ∀ t < 51, tf (tupOf D i) t =
          rL D (fld(D (80 + i), 372, 1)) (tf (tupOf D (fld(D (80 + i), 357, 32767))) t)) ∧
      sigOK D i (nSig D i) = true ∧
      covOK D i (tupOf D i) (Nat.shiftRight (D (80 + i)) 388) = true := by
  unfold nodeOK at h
  simp only [sB] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  refine ⟨fun hi => ?_, fun hi => ?_, h2, h3⟩
  · rcases bIf_or' h1 with ⟨-, ha⟩ | ⟨hc, -⟩
    · have ha' : rootOK D (tupOf D i) = true := ha
      unfold rootOK at ha'
      exact fun t ht => Nat.eq_of_beq_eq_true (allBlk0 ha' t ht)
    · subst hi
      exact absurd hc (by decide)
  · rcases bIf_or' h1 with ⟨hc, -⟩ | ⟨-, ha⟩
    · have hc' : i = 0 := Nat.eq_of_beq_eq_true hc
      omega
    · obtain ⟨hp, ha⟩ := (bAnd_iff _ _).1 ha
      exact ⟨Nat.blt_eq.mp hp, Nat.lt_succ_of_le Nat.and_le_right,
        fun t ht => Nat.eq_of_beq_eq_true (allBlk0 ha t ht)⟩

theorem sig_parts {i : Nat} (h : sigOK D i (nSig D i) = true) :
    nSig D i < 20160 ∧ (i + 1 < 20160 → tupOf D (nSig D i) < tupOf D (nSig D (i + 1))) := by
  unfold sigOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.blt_eq.mp h1, fun hi => ?_⟩
  rcases bIf_or' h2 with ⟨hc, -⟩ | ⟨-, hb⟩
  · have hc' : i + 1 = 20160 := Nat.eq_of_beq_eq_true hc
    omega
  · have ei : 80 + (i + 1) = 81 + i := by omega
    have e : nSig D (i + 1) = fld(D (81 + i), 373, 32767) := by
      unfold nSig
      rw [ei]
    rw [e]
    exact Nat.blt_eq.mp hb

theorem tupOf_inj (H : TreeH TT UU D g Mg L ρ) {a b : Nat} (ha : a < 20160) (hb : b < 20160)
    (h : ∀ t < 51, tf (tupOf D a) t = tf (tupOf D b) t) : a = b := by
  have he : tupOf D a = tupOf D b := tup_ext (m := 51) (tupOf_lt D a) (tupOf_lt D b) h
  have hs : ∀ i < 20160, nSig D i < 20160 ∧
      (i + 1 < 20160 → tupOf D (nSig D i) < tupOf D (nSig D (i + 1))) :=
    fun i hi => sig_parts (node_parts (H.nodes i hi)).2.2.1
  have mono : ∀ d i, i + d + 1 < 20160 → tupOf D (nSig D i) < tupOf D (nSig D (i + d + 1)) := by
    intro d
    induction d with
    | zero => exact fun i hi => (hs i (by omega)).2 hi
    | succ d ih =>
      exact fun i hi => (ih i (by omega)).trans ((hs (i + d + 1) (by omega)).2 (by omega))
  have kinj : ∀ i j, i < 20160 → j < 20160 → tupOf D (nSig D i) = tupOf D (nSig D j) → i = j := by
    intro i j hi hj e
    rcases lt_trichotomy i j with hl | hl | hl
    · have hm := mono (j - i - 1) i (by omega)
      have ej : i + (j - i - 1) + 1 = j := by omega
      rw [ej, e] at hm
      exact absurd hm (lt_irrefl _)
    · exact hl
    · have hm := mono (i - j - 1) j (by omega)
      have ei : j + (i - j - 1) + 1 = i := by omega
      rw [ei, e] at hm
      exact absurd hm (lt_irrefl _)
  have finj : Function.Injective fun i : Fin 20160 => (⟨nSig D i, (hs i i.isLt).1⟩ : Fin 20160) :=
    fun i j e => Fin.ext (kinj i j i.isLt j.isLt (congrArg (fun k : Fin 20160 => tupOf D k) e))
  have fs := Finite.injective_iff_surjective.mp finj
  obtain ⟨i, hi⟩ := fs ⟨a, ha⟩
  obtain ⟨j, hj⟩ := fs ⟨b, hb⟩
  have ea : nSig D i = a := congrArg Fin.val hi
  have eb : nSig D j = b := congrArg Fin.val hj
  have hij : (i : Nat) = j := kinj i j i.isLt j.isLt (by rw [ea, eb]; exact he)
  rw [← ea, ← eb, hij]

theorem node_inv (H : TreeH TT UU D g Mg L ρ) : ∀ i < 20160, ∃ l ∈ L, Tup D (ρ l) (tupOf D i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hn := node_parts (H.nodes i hi)
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · refine ⟨1, one_mem L, fun t ht x hx => ?_⟩
      rw [hn.1 h0 t ht, H.blk.one]
      exact hx.symm
    · obtain ⟨hpar, hg, hT⟩ := hn.2.1 h0
      obtain ⟨lp, hlp, hTp⟩ := ih _ hpar (by omega)
      have hgL : sI g D (3 + fld(D (80 + i), 372, 1)) ∈ L := by
        rcases Nat.lt_or_ge (fld(D (80 + i), 372, 1)) 1 with h1 | h1
        · have z : fld(D (80 + i), 372, 1) = 0 := by omega
          rw [z]
          exact H.memL3
        · have z : fld(D (80 + i), 372, 1) = 1 := by omega
          rw [z]
          exact H.memL4
      refine ⟨_, mul_mem hgL hlp, fun t ht x hx => ?_⟩
      rw [hT t ht, hTp t ht x hx, H.blk.mul _ (H.le hgL) _ (H.le hlp), Equiv.Perm.mul_apply]
      exact (rp_blkL H.rp H.items H.blk H.memM H.rho _ hg _).1

theorem pw_tree (H : TreeH TT UU D g Mg L ρ) :
    ∃ x : Fin 20160 → Equiv.Perm (Fin 120), (∀ i, Tup D (x i) (tupOf D i)) ∧
      ∀ σ ∈ ρ '' (L : Set (Equiv.Perm (Fin 245520))), ∃ i, σ = x i := by
  have hn : ∀ i : Fin 20160, ∃ l, l ∈ L ∧ Tup D (ρ l) (tupOf D i) := fun i => node_inv H i i.isLt
  choose lf hlf hTf using hn
  have inj : Function.Injective fun i => ρ (lf i) := by
    intro a b e
    have e' : ρ (lf a) = ρ (lf b) := e
    apply Fin.ext
    refine tupOf_inj H a.isLt b.isLt fun t ht => ?_
    rw [hTf a t ht ⟨_, tE_lt H ht⟩ rfl, hTf b t ht ⟨_, tE_lt H ht⟩ rfl, e']
  have sub : Set.range (fun i => ρ (lf i)) ⊆ ρ '' (L : Set (Equiv.Perm (Fin 245520))) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨lf i, hlf i, rfl⟩
  have eq := Set.eq_of_subset_of_ncard_le sub (le_of_eq (by
    rw [H.card, ← Set.image_univ, Set.ncard_image_of_injective _ inj, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin])) (Set.toFinite _)
  refine ⟨fun i => ρ (lf i), hTf, fun σ hσ => ?_⟩
  rw [← eq] at hσ
  obtain ⟨i, rfl⟩ := hσ
  exact ⟨i, rfl⟩

theorem pw_tup_unique (H : TreeH TT UU D g Mg L ρ) {σ τ : Equiv.Perm (Fin 120)}
    (hσ : σ ∈ ρ '' (L : Set (Equiv.Perm (Fin 245520))))
    (hτ : τ ∈ ρ '' (L : Set (Equiv.Perm (Fin 245520)))) {T : Nat} (h1 : Tup D σ T)
    (h2 : Tup D τ T) : σ = τ := by
  obtain ⟨x, hx, hc⟩ := pw_tree H
  obtain ⟨a, rfl⟩ := hc σ hσ
  obtain ⟨b, rfl⟩ := hc τ hτ
  have hab : (a : Nat) = b := tupOf_inj H a.isLt b.isLt fun t ht => by
    rw [hx a t ht ⟨_, tE_lt H ht⟩ rfl, ← h1 t ht ⟨_, tE_lt H ht⟩ rfl, h2 t ht ⟨_, tE_lt H ht⟩ rfl,
      hx b t ht ⟨_, tE_lt H ht⟩ rfl]
  rw [Fin.ext hab]

theorem root_tf (H : TreeH TT UU D g Mg L ρ) : ∀ t < 51, tf (tupOf D 0) t = tE D t :=
  (node_parts (H.nodes 0 (by decide))).1 rfl

theorem path_tup (H : TreeH TT UU D g Mg L ρ) {pv n : Nat} (hv : Lm 2 (wd pv))
    (h : pathOK D pv n = true) : Tup D (ρ (pV g D pv)) (tupOf D n) := by
  intro t ht x hx
  unfold pathOK at h
  simp only [sB] at h
  have e := Nat.eq_of_beq_eq_true (allBlk0 h t ht)
  have r0 : tf (tupOf D 0) t = (x : Nat) := (root_tf H t ht).trans hx.symm
  refine e.symm.trans ((congrArg (iT (rL D) (rLU D) pv) r0).trans
    ((iT_eq (rp_blkL H.rp H.items H.blk H.memM H.rho) hv x).trans ?_))
  unfold pV
  rw [H.blk.wv (a := fun j => sI g D (3 + j)) (m := 2) (fun j _ => H.memM (3 + j) (by omega)) hv]

theorem condT_of (H : TreeH TT UU D g Mg L ρ) {e : Nat} (he : e < 16) {l : Equiv.Perm (Fin 245520)}
    (hl : l ∈ L) (hy : yp g D = hV g D (D 61)) (hc : l * bY g D e * l⁻¹ = yp g D) {T : Nat}
    (hT : Tup D (ρ l) T) : condT D T e = true := by
  have hbY : bY g D e ∈ Mg :=
    wv_mem (m := 3) (fun j _ => hV_memM H.memM (pw_lm3 H.items (13 + 3 * e + j)))
      (pw_lm3 H.items 61)
  have hYM : hV g D (D 61) ∈ Mg := hV_memM H.memM (pw_lm3 H.items 61)
  have hcm : l * bY g D e = hV g D (D 61) * l := by
    rw [← hy, ← hc, inv_mul_cancel_right]
  have hρ : ρ l * ρ (bY g D e) = ρ (hV g D (D 61)) * ρ l := by
    rw [← H.blk.mul _ (H.le hl) _ hbY, ← H.blk.mul _ hYM _ (H.le hl), hcm]
  unfold condT
  refine allBlk_intro0 fun j hj' => ?_
  have hj : j < 3 := hj'
  change Nat.beq (tf T (3 + 3 * e + j)) (rt (D 72) (tf T j)) = true
  have dj : dB D j < 120 := dB_lt H.rho hj
  have ea : aB D e (dB D j) = _ :=
    aB_eq H.rp H.items H.blk H.memM H.rho he ⟨dB D j, dj⟩
  have e1 : tf T (3 + 3 * e + j) = (ρ l (ρ (bY g D e) ⟨dB D j, dj⟩) : Nat) :=
    hT _ (by omega) _ (by rw [tE_hi hj, ea])
  have e2 : tf T j = (ρ l ⟨dB D j, dj⟩ : Nat) := hT _ (by omega) _ (tE_lo hj).symm
  rw [e1, e2, ry_eq H.rp H.items H.blk H.memM H.rho]
  have e3 := congrArg (fun σ : Equiv.Perm (Fin 120) => (σ ⟨dB D j, dj⟩ : Nat)) hρ
  simp only [Equiv.Perm.mul_apply] at e3
  rw [e3]
  exact Nat.beq_refl _

@[expose] noncomputable def covF (D : Nat → Nat) (i T cp m : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih e r => bIf(condT D T e, bAnd(recsAt D i e cp r, ih (Nat.succ e) (Nat.succ r)),
      ih (Nat.succ e) r)) m

theorem covF_succ (i T cp m e r : Nat) : covF D i T cp (m + 1) e r =
    bIf(condT D T e, bAnd(recsAt D i e cp r, covF D i T cp m (e + 1) (r + 1)),
      covF D i T cp m (e + 1) r) := rfl

private theorem cov_aux {i T cp : Nat} : ∀ m e0 r : Nat, covF D i T cp m e0 r = true →
    ∀ e, e0 ≤ e → e < e0 + m → condT D T e = true → ∃ r', recsAt D i e cp r' = true
  | 0, _, _, _, _, _, h2, _ => absurd h2 (by omega)
  | m + 1, e0, r, h, e, h1, h2, hc => by
    rw [covF_succ] at h
    rcases bIf_or' h with ⟨-, h⟩ | ⟨hc0, h⟩
    · obtain ⟨hr, h⟩ := (bAnd_iff _ _).1 h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact ⟨r, hr⟩
      · exact cov_aux m (e0 + 1) (r + 1) h e (by omega) (by omega) hc
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact absurd (hc.symm.trans hc0) (by decide)
      · exact cov_aux m (e0 + 1) r h e (by omega) (by omega) hc

theorem cov_spec {i T cp : Nat} (h : covOK D i T cp = true) :
    ∀ e < 16, condT D T e = true → ∃ r, recsAt D i e cp r = true :=
  fun e he hc => cov_aux (nat_lit 16) (nat_lit 0) (nat_lit 0) h e (Nat.zero_le _) (by exact he) hc

theorem recs_spec {i e cp r : Nat} (h : recsAt D i e cp r = true) : ∀ k < 4,
    cp + 4 * r + k < D 70 ∧
      Nat.land (D (rB (cp + 4 * r + k))) 2097151 = i + e * 32768 + k * 524288 := by
  intro k hk
  unfold recsAt at h
  have h' := allBlk0 h k hk
  simp only [sB] at h'
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  refine ⟨Nat.blt_eq.mp h1, (Nat.eq_of_beq_eq_true h2).trans ?_⟩
  have s15 : Nat.shiftLeft e 15 = e * 32768 := Nat.shiftLeft_eq e 15
  have s19 : Nat.shiftLeft k 19 = k * 524288 := Nat.shiftLeft_eq k 19
  change i + (Nat.shiftLeft e 15 + Nat.shiftLeft k 19) = _
  rw [s15, s19]
  omega

theorem hdr {h i e k : Nat} (hh : Nat.land h 2097151 = i + e * 32768 + k * 524288)
    (hi : i < 32768) (he : e < 16) (hk : k < 4) :
    fld(h, 0, 32767) = i ∧ fld(h, 15, 15) = e ∧ fld(h, 19, 3) = k := by
  have m : Nat.land h 2097151 = h % 2097152 := Nat.and_two_pow_sub_one_eq_mod h 21
  have f0 : fld(h, 0, 32767) = h / 1 % 32768 := fldE h 0 15
  have f1 : fld(h, 15, 15) = h / 32768 % 16 := fldE h 15 4
  have f2 : fld(h, 19, 3) = h / 524288 % 4 := fldE h 19 2
  rw [m] at hh
  rw [f0, f1, f2]
  refine ⟨by omega, by omega, by omega⟩

theorem pw_surv (H : TreeH TT UU D g Mg L ρ) (hK : ∀ k < 7, g k ∈ K)
    (hS : Sep K ⟨0, by decide⟩ ⟨227759, by decide⟩ ⟨100817, by decide⟩)
    (hy : yp g D = hV g D (D 61)) (hx7 : xp g D ^ 7 = 1)
    (hrec : ∀ r < D 70, recOK TT UU D r = true) (hpath : ∀ r < D 70, pathEq D r = true)
    {e : Nat} (he : e < 16) {l : Equiv.Perm (Fin 245520)} (hl : l ∈ L)
    (hc : l * bY g D e * l⁻¹ = yp g D) :
    (∃ i < 7, ∀ j < 3, l * bE g D e j * l⁻¹ = xp g D ^ i * sI g D j * (xp g D ^ i)⁻¹) ∨
      fWP (fun j => l * bE g D e j * l⁻¹) (kp g D) ^ 8 ≠ 1 := by
  obtain ⟨x, hx, hcov⟩ := pw_tree H
  obtain ⟨n, hn⟩ := hcov (ρ l) ⟨l, hl, rfl⟩
  have hT : Tup D (ρ l) (tupOf D n) := by
    rw [hn]
    exact hx n
  have hn32 : (n : Nat) < 32768 := Nat.lt_trans n.isLt (by decide)
  obtain ⟨r, hr⟩ := cov_spec (node_parts (H.nodes n n.isLt)).2.2.2 e he
    (condT_of H he hl hy hc hT)
  generalize Nat.shiftRight (D (80 + (n : Nat))) 388 = cp at hr
  have hrs := recs_spec hr
  have hh : ∀ k < 4, fld(D (rB (cp + 4 * r + k)), 0, 32767) = n ∧
      fld(D (rB (cp + 4 * r + k)), 15, 15) = e ∧ fld(D (rB (cp + 4 * r + k)), 19, 3) = k :=
    fun k hk => hdr (hrs k hk).2 hn32 he hk
  have hpv : ∀ k < 4, D (Nat.succ (rB (cp + 4 * r + k))) = D (Nat.succ (rB (cp + 4 * r + 0))) := by
    intro k hk
    have hq := (pathEq_spec (hpath _ (hrs k hk).1) (hh k hk).2.2).2
    have es : cp + 4 * r + k - k = cp + 4 * r + 0 := by omega
    rw [es] at hq
    exact hq
  obtain ⟨hL0, hpo, -⟩ := rec_sound H.rp H.items hK hS hx7 (hrec _ (hrs 0 (by omega)).1)
    (hh 0 (by omega)).1 (hh 0 (by omega)).2.1 (hh 0 (by omega)).2.2 he
  generalize D (Nat.succ (rB (cp + 4 * r + 0))) = pv at hpv hL0 hpo
  have hPL : pV g D pv ∈ L := by
    unfold pV
    refine wv_mem (m := 2) (fun j hj => ?_) hL0
    rcases Nat.lt_or_ge j 1 with h1 | h1
    · have z : j = 0 := by omega
      subst z
      exact H.memL3
    · have z : j = 1 := by omega
      subst z
      exact H.memL4
  have hρ : ρ (pV g D pv) = ρ l :=
    pw_tup_unique H ⟨_, hPL, rfl⟩ ⟨l, hl, rfl⟩ (path_tup H hL0 hpo) hT
  obtain ⟨c, hc4, hcq⟩ := H.ker _ (mul_mem (inv_mem hPL) hl) (by
    rw [H.blk.mul _ (H.le (inv_mem hPL)) _ (H.le hl), H.blk.inv (H.le hPL), hρ, inv_mul_cancel])
  have hl' : l = lP g D pv c := by
    rw [lP, ← hcq, mul_inv_cancel_left]
  obtain ⟨-, -, himp⟩ := rec_sound H.rp H.items hK hS hx7 (hrec _ (hrs c hc4).1)
    (hh c hc4).1 (hh c hc4).2.1 (hh c hc4).2.2 he
  rw [hpv c hc4] at himp
  subst hl'
  exact himp hc

end Tree

end CFSG.KS.ONPw

end
