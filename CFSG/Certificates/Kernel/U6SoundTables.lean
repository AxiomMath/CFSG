
module

public import CFSG.Certificates.Kernel.U6Sound3000
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraidInputs
import all CFSG.Certificates.Kernel.U6Sound3010S
import all CFSG.Certificates.Kernel.U6Sound3000

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Th.Native
  CFSG.Fischer.Native CFSG.Sporadic.Schreier

@[expose] def TabsOK (UP POS POSN MVT : Nat) (R : Nat → Nat) : Prop :=
  posnOK POS POSN = true ∧ mvOK UP MVT = true ∧ ∀ s < 21, rowsOK UP POSN MVT R (33 * s) 33 = true

@[expose] noncomputable def j1KC (LT : Nat) (R : Nat → Nat) (aW : List (List Nat)) : Bool :=
  CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq (List.length aW) (nat_lit 9)) (codesK (nat_lit 92) aW)) (j1K LT R aW)

end CFSG.KC.U6

end

namespace CFSG.KC.U6.Hk

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.F4M CFSG.KC.U6.Snd CFSG.KC.U6.Pk
open CFSG.KC.S23 (par)

def sh (k y : ℕ) : ℕ := y ^^^ (y >>> k)

theorem sh_xor (k a b : ℕ) : sh k (a ^^^ b) = sh k a ^^^ sh k b := by
  unfold sh
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]
  generalize a.testBit i = x
  generalize b.testBit i = y
  generalize a.testBit (k + i) = z
  generalize b.testBit (k + i) = u
  cases x <;> cases y <;> cases z <;> cases u <;> rfl

theorem par_eq (x : ℕ) : par x = sh 1 (sh 2 (sh 4 (sh 8 (sh 16 (x &&& 4294967295))))) &&& 1 := rfl

theorem par_xor (a b : ℕ) : par (a ^^^ b) = par a ^^^ par b := by
  rw [par_eq, par_eq, par_eq, Nat.and_xor_distrib_right, sh_xor, sh_xor, sh_xor, sh_xor, sh_xor,
    Nat.and_xor_distrib_right]

theorem par_le (a : ℕ) : par a ≤ 1 := by
  rw [par_eq]
  exact Nat.and_le_right

def q0 (a b c d : ℕ) : ℕ := (a &&& c) ^^^ (b &&& d)

def q1 (a b c d : ℕ) : ℕ := ((a &&& d) ^^^ (b &&& c)) ^^^ (b &&& d)

def lo (x : ℕ) : ℕ := x &&& 1365

def hi (x : ℕ) : ℕ := (x >>> 1) &&& 1365

def cj (v : ℕ) : ℕ := (v &&& 1365) ^^^ hi v

theorem hermB_eq' (x v : ℕ) :
    hermB x v = par (q0 (lo x) (hi x) (cj v) (hi v)) + 2 * par (q1 (lo x) (hi x) (cj v) (hi v)) :=
  rfl

theorem q0_l (a a' b b' c d : ℕ) : q0 (a ^^^ a') (b ^^^ b') c d = q0 a b c d ^^^ q0 a' b' c d := by
  unfold q0
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  generalize a.testBit i = A
  generalize a'.testBit i = A'
  generalize b.testBit i = B
  generalize b'.testBit i = B'
  generalize c.testBit i = C
  generalize d.testBit i = D
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> cases D <;> rfl

theorem q0_r (a b c c' d d' : ℕ) : q0 a b (c ^^^ c') (d ^^^ d') = q0 a b c d ^^^ q0 a b c' d' := by
  unfold q0
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  generalize a.testBit i = A
  generalize b.testBit i = B
  generalize c.testBit i = C
  generalize c'.testBit i = C'
  generalize d.testBit i = D
  generalize d'.testBit i = D'
  cases A <;> cases B <;> cases C <;> cases C' <;> cases D <;> cases D' <;> rfl

theorem q1_l (a a' b b' c d : ℕ) : q1 (a ^^^ a') (b ^^^ b') c d = q1 a b c d ^^^ q1 a' b' c d := by
  unfold q1
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  generalize a.testBit i = A
  generalize a'.testBit i = A'
  generalize b.testBit i = B
  generalize b'.testBit i = B'
  generalize c.testBit i = C
  generalize d.testBit i = D
  cases A <;> cases A' <;> cases B <;> cases B' <;> cases C <;> cases D <;> rfl

theorem q1_r (a b c c' d d' : ℕ) : q1 a b (c ^^^ c') (d ^^^ d') = q1 a b c d ^^^ q1 a b c' d' := by
  unfold q1
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_and]
  generalize a.testBit i = A
  generalize b.testBit i = B
  generalize c.testBit i = C
  generalize c'.testBit i = C'
  generalize d.testBit i = D
  generalize d'.testBit i = D'
  cases A <;> cases B <;> cases C <;> cases C' <;> cases D <;> cases D' <;> rfl

theorem xor4 (a b c d : ℕ) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  generalize a.testBit i = A
  generalize b.testBit i = B
  generalize c.testBit i = C
  generalize d.testBit i = D
  cases A <;> cases B <;> cases C <;> cases D <;> rfl

theorem lo_xor (x y : ℕ) : lo (x ^^^ y) = lo x ^^^ lo y := Nat.and_xor_distrib_right

theorem hi_xor (x y : ℕ) : hi (x ^^^ y) = hi x ^^^ hi y := by
  unfold hi
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

theorem cj_xor (x y : ℕ) : cj (x ^^^ y) = cj x ^^^ cj y := by
  unfold cj
  rw [hi_xor, Nat.and_xor_distrib_right, xor4]

theorem comb : ∀ a0 < 2, ∀ a1 < 2, ∀ b0 < 2, ∀ b1 < 2,
    (a0 ^^^ b0) + 2 * (a1 ^^^ b1) = (a0 + 2 * a1) ^^^ (b0 + 2 * b1) := by decide

theorem hermB_l (x y v : ℕ) : hermB (x ^^^ y) v = hermB x v ^^^ hermB y v := by
  rw [hermB_eq', hermB_eq', hermB_eq', lo_xor, hi_xor, q0_l, q1_l, par_xor, par_xor]
  exact comb _ (Nat.lt_succ_of_le (par_le _)) _ (Nat.lt_succ_of_le (par_le _)) _
    (Nat.lt_succ_of_le (par_le _)) _ (Nat.lt_succ_of_le (par_le _))

theorem hermB_r (x v w : ℕ) : hermB x (v ^^^ w) = hermB x v ^^^ hermB x w := by
  rw [hermB_eq', hermB_eq', hermB_eq', cj_xor, hi_xor, q0_r, q1_r, par_xor, par_xor]
  exact comb _ (Nat.lt_succ_of_le (par_le _)) _ (Nat.lt_succ_of_le (par_le _)) _
    (Nat.lt_succ_of_le (par_le _)) _ (Nat.lt_succ_of_le (par_le _))

theorem crd_xor (x y i : ℕ) : crd (x ^^^ y) i = crd x i ^^^ crd y i := by
  change ((x ^^^ y) >>> (i * 2)) &&& maskN 2 =
    ((x >>> (i * 2)) &&& maskN 2) ^^^ ((y >>> (i * 2)) &&& maskN 2)
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

theorem crd_lt (c i : ℕ) : crd c i < 4 := fget_lt c i 2

theorem fm_l' : ∀ a < 4, ∀ b < 4, ∀ c < 4, fm (a ^^^ b) c = fm a c ^^^ fm b c := by decide +kernel

theorem fm_r' : ∀ a < 4, ∀ b < 4, ∀ c < 4, fm a (b ^^^ c) = fm a b ^^^ fm a c := by decide +kernel

theorem sq_xor' : ∀ a < 4, ∀ b < 4, sqC (a ^^^ b) = sqC a ^^^ sqC b := by decide +kernel

theorem xorN_xor (f g : ℕ → ℕ) : ∀ n, xorN n (fun i => f i ^^^ g i) = xorN n f ^^^ xorN n g
  | 0 => (Nat.xor_self 0).symm
  | n + 1 => by
    change (f n ^^^ g n) ^^^ xorN n (fun i => f i ^^^ g i) = (f n ^^^ xorN n f) ^^^ (g n ^^^ xorN n g)
    rw [xorN_xor f g n, xor4]

theorem hermK_l (x y v : ℕ) : hermK (x ^^^ y) v = hermK x v ^^^ hermK y v := by
  change xorN 6 (fun i => fm (crd (x ^^^ y) i) (sqC (crd v i))) =
    xorN 6 (fun i => fm (crd x i) (sqC (crd v i))) ^^^ xorN 6 (fun i => fm (crd y i) (sqC (crd v i)))
  rw [← xorN_xor]
  exact congrArg (xorN 6) (funext fun i => by
    rw [crd_xor, fm_l' (crd x i) (crd_lt x i) (crd y i) (crd_lt y i) (sqC (crd v i)) (fm_lt _ _)])

theorem hermK_r (x v w : ℕ) : hermK x (v ^^^ w) = hermK x v ^^^ hermK x w := by
  change xorN 6 (fun i => fm (crd x i) (sqC (crd (v ^^^ w) i))) =
    xorN 6 (fun i => fm (crd x i) (sqC (crd v i))) ^^^ xorN 6 (fun i => fm (crd x i) (sqC (crd w i)))
  rw [← xorN_xor]
  exact congrArg (xorN 6) (funext fun i => by
    rw [crd_xor, sq_xor' _ (crd_lt v i) _ (crd_lt w i), fm_r' (crd x i) (crd_lt x i)
      (sqC (crd v i)) (fm_lt _ _) (sqC (crd w i)) (fm_lt _ _)])

theorem split_bit {x n : ℕ} (hx : x < 2 ^ (n + 1)) :
    x = (x % 2 ^ n) ^^^ (if x.testBit n then 2 ^ n else 0) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow]
  have hgt : n < j → x.testBit j = false := fun h =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) h))
  by_cases hb : x.testBit n = true
  · rw [ite_eq_left hb, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · simp [h, Nat.ne_of_gt h]
    · simp [hb]
    · simp [hgt h, Nat.not_lt.2 h.le, Nat.ne_of_lt h]
  · rw [ite_eq_right hb, Nat.zero_testBit]
    rcases Nat.lt_trichotomy j n with h | rfl | h
    · simp [h]
    · simpa using hb
    · simp [hgt h, Nat.not_lt.2 h.le]

theorem zero_of_add {D : ℕ → ℕ} (hD : ∀ a b, D (a ^^^ b) = D a ^^^ D b) : D 0 = 0 := by
  have h := hD 0 0
  rw [Nat.xor_self, Nat.xor_self] at h
  exact h

theorem ext_add {D E : ℕ → ℕ} (hD : ∀ a b, D (a ^^^ b) = D a ^^^ D b)
    (hE : ∀ a b, E (a ^^^ b) = E a ^^^ E b) :
    ∀ n, (∀ i < n, D (2 ^ i) = E (2 ^ i)) → ∀ x < 2 ^ n, D x = E x
  | 0, _, x, hx => by
    have : x = 0 := Nat.lt_one_iff.1 (by simpa using hx)
    rw [this, zero_of_add hD, zero_of_add hE]
  | n + 1, hb, x, hx => by
    rw [split_bit hx, hD, hE, ext_add hD hE n (fun i hi => hb i (by omega)) _
      (Nat.mod_lt _ (Nat.two_pow_pos n))]
    congr 1
    split
    · exact hb n (by omega)
    · rw [zero_of_add hD, zero_of_add hE]

theorem hermB_base : ∀ i < 12, ∀ j < 12, hermB (2 ^ i) (2 ^ j) = hermK (2 ^ i) (2 ^ j) := by
  decide +kernel

theorem hermB_eq_hermK {x v : ℕ} (hx : x < 4096) (hv : v < 4096) : hermB x v = hermK x v := by
  have h1 : ∀ i < 12, hermB (2 ^ i) v = hermK (2 ^ i) v := fun i hi =>
    ext_add (D := fun v => hermB (2 ^ i) v) (E := fun v => hermK (2 ^ i) v)
      (fun a b => hermB_r _ a b) (fun a b => hermK_r _ a b) 12 (hermB_base i hi) v hv
  exact ext_add (D := fun x => hermB x v) (E := fun x => hermK x v) (fun a b => hermB_l a b v)
    (fun a b => hermK_l a b v) 12 h1 x hx

theorem bit_eq (X i : ℕ) : bit X i = X.testBit i := by
  have e : bit X i = Nat.beq (fget X i 1) 1 := by
    unfold bit fget
    change _ = Nat.beq (Nat.land (Nat.shiftRight X (i * 1)) 1) 1
    rw [Nat.mul_one]
  rw [e, beq_fget1]

theorem bit_maskL (l : List ℕ) (p : ℕ) : bit (maskL l) p = decide (p ∈ l) := by
  rw [bit_eq, testBit_maskL]

end CFSG.KC.U6.Hk

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.EvenSmallLie.UnitarySix CFSG.Sporadic.Th.Native CFSG.Fischer.Native
  CFSG.Sporadic.Schreier

theorem tables_sound {UP POS POSN MVT : Nat} {R : Nat → Nat} {pts pos : Array ℕ}
    (hu : decA UP 12 693 = pts) (hp : decA POS 10 4096 = pos) (h : TabsOK UP POS POSN MVT R) :
    ∀ m < 693, ((tvTabsG pts pos)[m]!).size = 693 ∧ Nat.shiftRight (R m) 6930 = 0 ∧
      ∀ q < 693, ap (tvTabsG pts pos)[m]! q = fget (R m) q 10 := by
  open Pk Snd Tk Hk in
  obtain ⟨hposn, hmv, hrows⟩ := h
  have HP := allBelow_spec hposn (by norm_num)
  have HM := allBelow_spec hmv (by norm_num)
  intro m hm
  have hr := hrows (m / 33) (by omega)
  unfold rowsOK at hr
  rw [allN_iff] at hr
  have hr' := hr (m % 33) (Nat.mod_lt _ (by norm_num))
  rw [show Nat.add (33 * (m / 33)) (m % 33) = m by change 33 * (m / 33) + m % 33 = m; omega] at hr'
  unfold rowOK at hr'
  rw [strictB_eq, strictB_eq, andB_iff, beq_iff] at hr'
  obtain ⟨hsh, hq⟩ := hr'
  have HQ := allBelow_spec hq (by norm_num)
  refine ⟨(tab_ap hu hp hm (by norm_num : 0 < 693)).1, hsh, fun q hqlt => ?_⟩
  rw [(tab_ap hu hp hm hqlt).2]
  have h1 := HQ q hqlt
  dsimp only at h1
  rw [strictB_eq, beq_iff] at h1
  rw [h1]
  have hx : up UP q < 4096 := fget_lt _ _ 12
  have hv : up UP m < 4096 := fget_lt _ _ 12
  rw [hermB_eq_hermK hx hv]
  have ha := hermK_lt (up UP q) (up UP m)
  have h2 := HM m hm
  dsimp only at h2
  rw [allN_iff] at h2
  have h3 := h2 _ ha
  try dsimp only at h3
  rw [beq_iff] at h3
  rw [h3]
  have hc : Nat.xor (up UP q) (scaleK (hermK (up UP q) (up UP m)) (up UP m)) < 4096 :=
    Nat.xor_lt_two_pow (n := 12) hx (by rw [(scaleK_eq _ _ ha).1]; exact (scaleK_eq _ _ ha).2)
  have h4 := HP _ hc
  try dsimp only at h4
  rw [beq_iff] at h4
  rw [h4]
  rfl

theorem swap_rows {R : Nat → Nat} (hs : ∀ s < 21, swapK R (33 * s) 33 = true) :
    ∀ p < 693, ∀ q < 693, fget (R p) q 10 = q ∨ fget (R p) q 10 = fget (R q) p 10 := by
  open Pk Snd Tk Hk in
  intro p hp q hq
  have h1 := hs (p / 33) (by omega)
  unfold swapK at h1
  rw [allN_iff] at h1
  have h2 := h1 (p % 33) (Nat.mod_lt _ (by norm_num))
  rw [show Nat.add (33 * (p / 33)) (p % 33) = p by change 33 * (p / 33) + p % 33 = p; omega] at h2
  try dsimp only at h2
  rw [strictB_eq] at h2
  have h3 := allBelow_spec h2 (by norm_num) q hq
  try dsimp only at h3
  rw [strictB_eq, orB_iff, beq_iff, beq_iff] at h3
  exact h3

theorem sound3145 {UP POS POSN MVT : Nat} {R : Nat → Nat} {fa : List ℕ} {pts pos : Array ℕ}
    (hu : decA UP 12 693 = pts) (hp : decA POS 10 4096 = pos) (h : TabsOK UP POS POSN MVT R)
    (hs : ∀ s < 21, swapK R (33 * s) 33 = true) (_hfa : ∀ x ∈ fa, x < 693)
    (hf : fixAK R (maskL fa) = true) :
    (swapOKG pts pos = true) ∧ (fixOKG fa pts pos = true) := by
  open Pk Snd Tk Hk in
  have T := tables_sound hu hp h
  have S := swap_rows hs
  refine ⟨?_, ?_⟩
  · simp only [swapOKG, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq]
    intro p hp q hq
    rw [(T p hp).2.2 q hq, (T q hq).2.2 p hp]
    exact S p hp q hq
  · simp only [fixOKG, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
      List.contains_iff_mem, Bool.not_eq_true', Bool.eq_false_iff, Ne]
    intro m hm
    unfold fixAK at hf
    have h1 := allBelow_spec hf (by norm_num) m hm
    dsimp only at h1
    rw [orB_iff, bit_maskL, decide_eq_true_iff, strictB_eq, anyN_iff] at h1
    rcases h1 with h1 | ⟨q, hq, e⟩
    · exact Or.inl h1
    · rw [andB_iff, notB_iff, bit_maskL, bit_maskL, decide_eq_true_iff, decide_eq_false_iff_not] at e
      refine Or.inr ⟨q, e.1, ?_⟩
      rw [(T m hm).2.2 q hq]
      exact e.2

theorem sound3181 {UP POS LT POSN MVT : Nat} {R : Nat → Nat} {L : List (Equiv.Perm (Fin 693))}
    {aw : List (List ℤ)} {aW : List (List Nat)} {pts pos : Array ℕ} (hu : decA UP 12 693 = pts)
    (hp : decA POS 10 4096 = pos) (hL : LetsBind L LT) (h : TabsOK UP POS POSN MVT R)
    (hs : ∀ s < 21, swapK R (33 * s) 33 = true)
    (haW : aw = aW.map (List.map decZ)) (hj : j1KC LT R aW = true) :
    (Hunt.braidOK (tvTabsG pts pos) = true) ∧
      (toTable (j1G L aw) = (tvTabsG pts pos)[(0 : Fin 693).val]!) := by
  open Pk Snd Tk Hk in
  have T := tables_sound hu hp h
  have S := swap_rows hs
  unfold j1KC j1K at hj
  simp only [strictB_eq, andB_iff, beq_iff, codesK_iff] at hj
  obtain ⟨⟨h9, hc⟩, hj⟩ := hj
  obtain ⟨-, -, hj1, -, -⟩ := rep_A hL haW h9 hc
  rw [hj] at hj1
  refine ⟨?_, ?_⟩
  · unfold Hunt.braidOK
    simp only [allIn_iff, Bool.or_eq_true, beq_iff_eq]
    intro p hp q hq
    rw [(T p hp).2.2 q hq, (T q hq).2.2 p hp]
    exact S p hp q hq
  · have h0 : (tvTabsG pts pos)[(0 : Fin 693).val]! = (tvTabsG pts pos)[0]! := rfl
    rw [h0]
    have hsz : (toTable (j1G L aw)).size = 693 := by simp [toTable]
    have hsz' : ((tvTabsG pts pos)[0]!).size = 693 := (T 0 (by norm_num)).1
    have key : ∀ i < 693, ap (toTable (j1G L aw)) i = ap (tvTabsG pts pos)[0]! i := by
      intro i hi
      rw [ap_toTable _ hi, (T 0 (by norm_num)).2.2 i hi, ← ap10_eq hj1 hi]
      rfl
    generalize toTable (j1G L aw) = A at hsz key
    generalize (tvTabsG pts pos)[0]! = B at hsz' key
    refine Array.ext (hsz.trans hsz'.symm) fun i h1 h2 => ?_
    have k := key i (hsz ▸ h1)
    unfold ap at k
    rw [getElem!_pos A i h1, getElem!_pos B i h2] at k
    exact UInt32.toNat_inj.1 k

end CFSG.KC.U6

end
