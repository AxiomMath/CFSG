module

public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public import Certificates.Data.Kernel.MonsterB.Sp8Span
public import CFSG.Certificates.Kernel.MonsterB.Rep4371RowEq

public section

namespace CFSG.KC.Sp8Span

open CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.KC.Rep4371Row

theorem bxor_pair (A B a b : Bool) : ((A ^^ B) ^^ (a ^^ b)) = ((A ^^ a) ^^ (B ^^ b)) := by
  cases A <;> cases B <;> cases a <;> cases b <;> rfl

theorem nxor_cancel_left (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

theorem nxor_left_comm (a b c : ℕ) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← Nat.xor_assoc, Nat.xor_comm a b, Nat.xor_assoc]

theorem bxor_cancel_left (a b : Bool) : (a ^^ (a ^^ b)) = b := by
  cases a <;> cases b <;> rfl

@[expose] def Lin (g : ℕ → ℕ) : Prop := ∀ x y, g (x ^^^ y) = g x ^^^ g y

@[expose] def Aff (g : ℕ → ℕ) : Prop := ∀ x y, g (x ^^^ y) = g x ^^^ g y ^^^ g 0

@[expose] def BLin (f : ℕ → Bool) : Prop := ∀ x y, f (x ^^^ y) = (f x ^^ f y)

@[expose] def BAff (f : ℕ → Bool) : Prop := ∀ x y, f (x ^^^ y) = (f x ^^ f y ^^ f 0)

@[expose] def cube (f : ℕ → Bool) (x a b c : ℕ) : Bool :=
  f x ^^ f (x ^^^ a) ^^ f (x ^^^ b) ^^ f (x ^^^ c) ^^ f (x ^^^ a ^^^ b) ^^ f (x ^^^ a ^^^ c) ^^
    f (x ^^^ b ^^^ c) ^^ f (x ^^^ a ^^^ b ^^^ c)

@[expose] def Quad (f : ℕ → Bool) : Prop := ∀ x a b c, cube f x a b c = false

theorem Lin.zero {g : ℕ → ℕ} (h : Lin g) : g 0 = 0 := by
  simpa using h 0 0

theorem Lin.aff {g : ℕ → ℕ} (h : Lin g) : Aff g := fun x y => by
  rw [h, h.zero, Nat.xor_zero]

theorem Lin.comp {g h : ℕ → ℕ} (hg : Lin g) (hh : Lin h) : Lin fun x => g (h x) := fun x y => by
  dsimp only
  rw [hh, hg]

theorem BLin.zero {f : ℕ → Bool} (h : BLin f) : f 0 = false := by
  simpa using h 0 0

theorem BLin.baff {f : ℕ → Bool} (h : BLin f) : BAff f := fun x y => by
  rw [h, h.zero, Bool.xor_false]

theorem BLin.comp {f : ℕ → Bool} {g : ℕ → ℕ} (hf : BLin f) (hg : Lin g) : BLin fun x => f (g x) :=
  fun x y => by
    dsimp only
    rw [hg, hf]

theorem aff_comp {g h : ℕ → ℕ} (hg : Aff g) (hh : Aff h) : Aff fun x => g (h x) := fun x y => by
  dsimp only
  rw [hh, hg, hg (h x) (h y)]
  generalize g (h x) = p₁
  generalize g (h y) = p₂
  generalize g (h 0) = p₃
  generalize g 0 = p₄
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases p₁.testBit i <;> cases p₂.testBit i <;> cases p₃.testBit i <;> cases p₄.testBit i <;> rfl

theorem quad_of_polar {f : ℕ → Bool} (B : ℕ → ℕ → Bool)
    (h : ∀ x y, f (x ^^^ y) = (f x ^^ f y ^^ f 0 ^^ B x y))
    (hB : ∀ x x' y, B (x ^^^ x') y = (B x y ^^ B x' y)) : Quad f := by
  intro x a b c
  unfold cube
  rw [h (x ^^^ a ^^^ b) c, h (x ^^^ a) c, h (x ^^^ b) c, h x c, hB (x ^^^ a) b c, hB x a c,
    hB x b c]
  generalize f x = p₀
  generalize f (x ^^^ a) = p₁
  generalize f (x ^^^ b) = p₂
  generalize f (x ^^^ a ^^^ b) = p₃
  generalize f c = p₄
  generalize f 0 = p₅
  generalize B x c = q₀
  generalize B a c = q₁
  generalize B b c = q₂
  revert p₀ p₁ p₂ p₃ p₄ p₅ q₀ q₁ q₂
  decide

theorem BAff.quad {f : ℕ → Bool} (h : BAff f) : Quad f :=
  quad_of_polar (fun _ _ => false) (fun x y => by rw [h, Bool.xor_false]) fun _ _ _ => rfl

theorem quad_const (b : Bool) : Quad fun _ => b :=
  BAff.quad fun _ _ => by cases b <;> rfl

theorem quad_xor {f g : ℕ → Bool} (hf : Quad f) (hg : Quad g) : Quad fun x => f x ^^ g x := by
  intro x a b c
  have h1 := hf x a b c
  have h2 := hg x a b c
  unfold cube at h1 h2 ⊢
  dsimp only
  generalize f x = p₀ at h1 ⊢
  generalize f (x ^^^ a) = p₁ at h1 ⊢
  generalize f (x ^^^ b) = p₂ at h1 ⊢
  generalize f (x ^^^ c) = p₃ at h1 ⊢
  generalize f (x ^^^ a ^^^ b) = p₄ at h1 ⊢
  generalize f (x ^^^ a ^^^ c) = p₅ at h1 ⊢
  generalize f (x ^^^ b ^^^ c) = p₆ at h1 ⊢
  generalize f (x ^^^ a ^^^ b ^^^ c) = p₇ at h1 ⊢
  generalize g x = r₀ at h2 ⊢
  generalize g (x ^^^ a) = r₁ at h2 ⊢
  generalize g (x ^^^ b) = r₂ at h2 ⊢
  generalize g (x ^^^ c) = r₃ at h2 ⊢
  generalize g (x ^^^ a ^^^ b) = r₄ at h2 ⊢
  generalize g (x ^^^ a ^^^ c) = r₅ at h2 ⊢
  generalize g (x ^^^ b ^^^ c) = r₆ at h2 ⊢
  generalize g (x ^^^ a ^^^ b ^^^ c) = r₇ at h2 ⊢
  rw [bxor_pair p₀ r₀ p₁ r₁, bxor_pair (p₀ ^^ p₁) (r₀ ^^ r₁) p₂ r₂,
    bxor_pair (p₀ ^^ p₁ ^^ p₂) (r₀ ^^ r₁ ^^ r₂) p₃ r₃,
    bxor_pair (p₀ ^^ p₁ ^^ p₂ ^^ p₃) (r₀ ^^ r₁ ^^ r₂ ^^ r₃) p₄ r₄,
    bxor_pair (p₀ ^^ p₁ ^^ p₂ ^^ p₃ ^^ p₄) (r₀ ^^ r₁ ^^ r₂ ^^ r₃ ^^ r₄) p₅ r₅,
    bxor_pair (p₀ ^^ p₁ ^^ p₂ ^^ p₃ ^^ p₄ ^^ p₅) (r₀ ^^ r₁ ^^ r₂ ^^ r₃ ^^ r₄ ^^ r₅) p₆ r₆,
    bxor_pair (p₀ ^^ p₁ ^^ p₂ ^^ p₃ ^^ p₄ ^^ p₅ ^^ p₆) (r₀ ^^ r₁ ^^ r₂ ^^ r₃ ^^ r₄ ^^ r₅ ^^ r₆)
      p₇ r₇, h1, h2]
  rfl

theorem quad_comp {f : ℕ → Bool} {g : ℕ → ℕ} (hf : Quad f) (hg : Aff g) : Quad fun x => f (g x) := by
  intro x a b c
  have h1 : ∀ u v, g (u ^^^ v) = g u ^^^ (g v ^^^ g 0) := fun u v => by
    rw [hg u v, Nat.xor_assoc]
  unfold cube
  dsimp only
  rw [h1 (x ^^^ a ^^^ b) c, h1 (x ^^^ a) b, h1 (x ^^^ a) c, h1 (x ^^^ b) c, h1 x a, h1 x b, h1 x c]
  exact hf (g x) _ _ _

theorem popcN_zero : ∀ k, Model.popcN k 0 = 0
  | 0 => rfl
  | k + 1 => by
    rw [Model.popcN, popcN_zero k]

theorem popcN_xor_and : ∀ k x y : ℕ,
    Model.popcN k (x ^^^ y) + 2 * Model.popcN k (x &&& y) = Model.popcN k x + Model.popcN k y
  | 0, _, _ => rfl
  | k + 1, x, y => by
    rw [Model.popcN, Model.popcN, Model.popcN, Model.popcN, Nat.xor_div_two, Nat.and_div_two]
    have ih := popcN_xor_and k (x / 2) (y / 2)
    have h1 := Nat.xor_mod_two_eq_one (a := x) (b := y)
    have h2 := Nat.and_mod_two_eq_one (a := x) (b := y)
    omega

theorem parN_xor (k x y : ℕ) : Model.parN k (x ^^^ y) = (Model.parN k x ^^ Model.parN k y) := by
  have h := popcN_xor_and k x y
  unfold Model.parN
  rcases Nat.mod_two_eq_zero_or_one (Model.popcN k x) with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one (Model.popcN k y) with hy | hy <;>
    rcases Nat.mod_two_eq_zero_or_one (Model.popcN k (x ^^^ y)) with hz | hz <;>
    simp only [hx, hy, hz] <;> first | rfl | (exfalso; omega)

theorem parN_zero (k : ℕ) : Model.parN k 0 = false := by
  rw [Model.parN, popcN_zero]
  rfl

theorem testBit_packN (f : ℕ → Bool) :
    ∀ n i, (Model.packN f n).testBit i = (decide (i < n) && f i)
  | 0, i => by
    rw [Model.packN, Nat.zero_testBit]
    simp
  | n + 1, i => by
    rw [Model.packN, Nat.testBit_or, testBit_packN f n i]
    rcases Nat.lt_trichotomy i n with h | rfl | h
    · have h' : i < n + 1 := by omega
      have hne : n ≠ i := by omega
      cases f n <;> simp [h, h', hne, Nat.testBit_two_pow]
    · cases hf : f i <;> simp [hf, Nat.testBit_two_pow]
    · have h1 : ¬ i < n := by omega
      have h2 : ¬ i < n + 1 := by omega
      have hne : n ≠ i := by omega
      cases f n <;> simp [h1, h2, hne, Nat.testBit_two_pow]

theorem packN_xor (f g : ℕ → Bool) (n : ℕ) :
    Model.packN (fun i => f i ^^ g i) n = Model.packN f n ^^^ Model.packN g n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_packN, testBit_packN, testBit_packN]
  cases decide (i < n) <;> simp

theorem packN_lt (f : ℕ → Bool) (n : ℕ) : Model.packN f n < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_packN]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left
  omega

theorem combN_xor (m : ℕ → ℕ) : ∀ n x y : ℕ,
    Model.combN m n (x ^^^ y) = Model.combN m n x ^^^ Model.combN m n y
  | 0, _, _ => by rw [Model.combN, Model.combN, Model.combN, Nat.xor_zero]
  | n + 1, x, y => by
    rw [Model.combN, Model.combN, Model.combN, combN_xor m n x y, Nat.testBit_xor]
    generalize Model.combN m n x = u
    generalize Model.combN m n y = v
    cases x.testBit n <;> cases y.testBit n <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, if_false, if_true, Nat.xor_zero] <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor] <;>
      cases u.testBit i <;> cases v.testBit i <;> cases (m n).testBit i <;> rfl

theorem combN_lin (m : ℕ → ℕ) (n : ℕ) : Lin (Model.combN m n) := combN_xor m n

theorem pi0N_xor (x y : ℕ) : Model.pi0N (x ^^^ y) = Model.pi0N x ^^^ Model.pi0N y := by
  unfold Model.pi0N
  rw [Nat.testBit_xor]
  cases x.testBit 0 <;> cases y.testBit 0 <;>
    simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_false, if_true, Nat.xor_zero] <;>
    apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor] <;>
    cases x.testBit i <;> cases y.testBit i <;> cases (63 : ℕ).testBit i <;> rfl

theorem pi0N_lin : Lin Model.pi0N := pi0N_xor

theorem and_lin (m : ℕ) : Lin fun x => x &&& m := fun _ _ => Nat.and_xor_distrib_right

theorem parN_lin (k : ℕ) : BLin (Model.parN k) := parN_xor k

theorem packPar_lin (k : ℕ) (m : ℕ → ℕ) (n : ℕ) :
    Lin fun w => Model.packN (fun j => Model.parN k (w &&& m j)) n := fun x y => by
  dsimp only
  have e : (fun j => Model.parN k ((x ^^^ y) &&& m j)) =
      fun j => (Model.parN k (x &&& m j) ^^ Model.parN k (y &&& m j)) := by
    funext j
    rw [Nat.and_xor_distrib_right, parN_xor]
  rw [e, packN_xor]

theorem wordN_lin : Lin Model.wordN := combN_lin _ _

theorem repN_lin : Lin Model.repN := combN_lin _ _

theorem dualN_lin : Lin Model.dualN := packPar_lin 24 Model.bmaskN 12

theorem coeffN_lin : Lin Model.coeffN := packPar_lin 24 Model.umaskN 12

theorem permWordN_lin (p : Array ℕ) : Lin (Model.permWordN p) := combN_lin _ _

theorem permCN_lin (p : Array ℕ) : Lin (Model.permCN p) :=
  coeffN_lin.comp ((permWordN_lin p).comp wordN_lin)

theorem pairN_xor_left (x y d : ℕ) : Model.pairN (x ^^^ y) d = (Model.pairN x d ^^ Model.pairN y d) := by
  unfold Model.pairN
  rw [Nat.and_xor_distrib_right, parN_xor]

theorem pairN_xor_right (a x y : ℕ) : Model.pairN a (x ^^^ y) = (Model.pairN a x ^^ Model.pairN a y) := by
  unfold Model.pairN
  rw [Nat.and_xor_distrib_left, parN_xor]

theorem pairN_left (d : ℕ) : BLin fun a => Model.pairN a d := fun x y => pairN_xor_left x y d

theorem mu0N_lin : BLin Model.mu0N := fun x y => by
  unfold Model.mu0N
  rw [Nat.testBit_xor]

theorem wordN_xor (x y : ℕ) : Model.wordN (x ^^^ y) = Model.wordN x ^^^ Model.wordN y :=
  wordN_lin x y

theorem shiftN_aff (a : ℕ) : Aff (Model.shiftN a) := fun x y => by
  unfold Model.shiftN
  rw [pi0N_xor (x ^^^ y) a, pi0N_xor x y, pi0N_xor x a, pi0N_xor y a, pi0N_xor 0 a,
    pi0N_lin.zero]
  generalize Model.pi0N x = p₁
  generalize Model.pi0N y = p₂
  generalize Model.pi0N a = p₃
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.zero_testBit]
  cases p₁.testBit i <;> cases p₂.testBit i <;> cases p₃.testBit i <;> rfl

theorem and_const_lin {f : ℕ → Bool} (hf : BLin f) (b : Bool) : BLin fun x => (b && f x) :=
  fun x y => by
    dsimp only
    rw [hf]
    cases b <;> simp

theorem e2_xor (v w : ℕ) :
    (Model.popcN 24 (v ^^^ w) / 2 % 2 == 1) =
      ((Model.popcN 24 v / 2 % 2 == 1) ^^ (Model.popcN 24 w / 2 % 2 == 1) ^^
        (Model.parN 24 v && Model.parN 24 w) ^^ Model.parN 24 (v &&& w)) := by
  have h := popcN_xor_and 24 v w
  unfold Model.parN
  generalize Model.popcN 24 (v ^^^ w) = n at h ⊢
  generalize Model.popcN 24 (v &&& w) = m at h ⊢
  generalize Model.popcN 24 v = a at h ⊢
  generalize Model.popcN 24 w = b at h ⊢
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
    rcases Nat.mod_two_eq_zero_or_one (a / 2) with ha2 | ha2 <;>
    rcases Nat.mod_two_eq_zero_or_one (b / 2) with hb2 | hb2 <;>
    rcases Nat.mod_two_eq_zero_or_one (n / 2) with hn2 | hn2 <;>
    simp only [ha, hb, hm, ha2, hb2, hn2] <;> first | rfl | (exfalso; omega)

theorem kN_quad (a : ℕ) : Quad fun c => Model.kN a c := by
  have hv : ∀ x y, Model.wordN a &&& Model.wordN (x ^^^ y) =
      (Model.wordN a &&& Model.wordN x) ^^^ (Model.wordN a &&& Model.wordN y) := fun x y => by
    rw [wordN_xor, Nat.and_xor_distrib_left]
  have h0 : Model.kN a 0 = false := by
    rw [Model.kN, Lin.zero wordN_lin, Nat.and_zero, popcN_zero]
    rfl
  refine quad_of_polar (fun x y => (Model.parN 24 (Model.wordN a &&& Model.wordN x) &&
      Model.parN 24 (Model.wordN a &&& Model.wordN y)) ^^
      Model.parN 24 ((Model.wordN a &&& Model.wordN x) &&& (Model.wordN a &&& Model.wordN y)))
    (fun x y => ?_) (fun x x' y => ?_)
  · rw [h0, Bool.xor_false]
    unfold Model.kN
    rw [hv x y, e2_xor]
    simp only [Bool.xor_assoc]
  · rw [hv x x', parN_xor, Nat.and_xor_distrib_right, parN_xor]
    generalize Model.parN 24 (Model.wordN a &&& Model.wordN x) = p₁
    generalize Model.parN 24 (Model.wordN a &&& Model.wordN x') = p₂
    generalize Model.parN 24 (Model.wordN a &&& Model.wordN y) = p₃
    generalize Model.parN 24 ((Model.wordN a &&& Model.wordN x) &&&
      (Model.wordN a &&& Model.wordN y)) = p₄
    generalize Model.parN 24 ((Model.wordN a &&& Model.wordN x') &&&
      (Model.wordN a &&& Model.wordN y)) = p₅
    revert p₁ p₂ p₃ p₄ p₅
    decide

@[expose] def thD (n x : ℕ) : ℕ := Model.dualN (Model.combN Model.bmaskN n x &&& Model.bmaskN n)

theorem thD_lin (n : ℕ) : Lin (thD n) :=
  dualN_lin.comp ((and_lin _).comp (combN_lin _ _))

@[expose] def thB : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, x, y =>
    thB n x y ^^^ (if x.testBit n then thD n y else 0) ^^^ (if y.testBit n then thD n x else 0)

theorem thetaRec_xor : ∀ n x y : ℕ,
    Model.thetaRec n (x ^^^ y) = Model.thetaRec n x ^^^ Model.thetaRec n y ^^^ thB n x y
  | 0, _, _ => by simp only [Model.thetaRec, thB, Nat.xor_zero]
  | n + 1, x, y => by
    have ih := thetaRec_xor n x y
    have hD := thD_lin n x y
    unfold thD at hD
    rw [Model.thetaRec, Model.thetaRec, Model.thetaRec, thB, Nat.testBit_xor, ih, hD]
    unfold thD
    generalize Model.thetaRec n x = t₁
    generalize Model.thetaRec n y = t₂
    generalize thB n x y = t₃
    generalize Model.packN (Model.betaN n) 12 = t₄
    generalize Model.dualN (Model.combN Model.bmaskN n x &&& Model.bmaskN n) = t₅
    generalize Model.dualN (Model.combN Model.bmaskN n y &&& Model.bmaskN n) = t₆
    cases x.testBit n <;> cases y.testBit n <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_true, ite_false, ↓reduceIte] <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor, Nat.zero_testBit] <;>
      cases t₁.testBit i <;> cases t₂.testBit i <;> cases t₃.testBit i <;> cases t₄.testBit i <;>
      cases t₅.testBit i <;> cases t₆.testBit i <;> rfl

theorem thB_add : ∀ n x x' y : ℕ, thB n (x ^^^ x') y = thB n x y ^^^ thB n x' y
  | 0, _, _, _ => by simp only [thB, Nat.xor_zero]
  | n + 1, x, x', y => by
    have ih := thB_add n x x' y
    have hD := thD_lin n x x'
    rw [thB, thB, thB, ih, hD, Nat.testBit_xor]
    generalize thB n x y = t₁
    generalize thB n x' y = t₂
    generalize thD n x = t₃
    generalize thD n x' = t₄
    generalize thD n y = t₅
    cases x.testBit n <;> cases x'.testBit n <;> cases y.testBit n <;>
      simp only [Bool.false_xor, Bool.xor_false, Bool.true_xor, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ite_true, ite_false, ↓reduceIte] <;>
      apply Nat.eq_of_testBit_eq <;> intro i <;> simp only [Nat.testBit_xor, Nat.zero_testBit] <;>
      cases t₁.testBit i <;> cases t₂.testBit i <;> cases t₃.testBit i <;> cases t₄.testBit i <;>
      cases t₅.testBit i <;> rfl

theorem thetaRec_zero : ∀ n, Model.thetaRec n 0 = 0
  | 0 => by simp only [Model.thetaRec]
  | n + 1 => by
    rw [Model.thetaRec, Nat.zero_testBit, thetaRec_zero n]
    simp

theorem pairN_zero_right' (a : ℕ) : Model.pairN a 0 = false := by
  rw [Model.pairN, Nat.and_zero, parN_zero]

theorem thetaBit_quad (a : ℕ) : Quad fun c => Model.thetaBit c a := by
  have h0 : Model.thetaBit 0 a = false := by
    rw [Model.thetaBit, Model.thetaN, thetaRec_zero, pairN_zero_right']
  refine quad_of_polar (fun x y => Model.pairN a (thB 12 x y)) (fun x y => ?_) (fun x x' y => ?_)
  · rw [h0, Bool.xor_false]
    unfold Model.thetaBit Model.thetaN
    rw [thetaRec_xor, pairN_xor_right, pairN_xor_right]
  · rw [thB_add, pairN_xor_right]

theorem xorSum_xor (f g : ℕ → Bool) : ∀ n,
    Model.xorSum (fun i => f i ^^ g i) n = (Model.xorSum f n ^^ Model.xorSum g n)
  | 0 => rfl
  | n + 1 => by
    rw [Model.xorSum, Model.xorSum, Model.xorSum, xorSum_xor f g n]
    exact bxor_pair _ _ _ _

theorem xorSum_false : ∀ n, Model.xorSum (fun _ => false) n = false
  | 0 => rfl
  | n + 1 => by
    rw [Model.xorSum, xorSum_false n]
    rfl

@[expose] def qform (g : ℕ → ℕ → Bool) (n m a : ℕ) : Bool :=
  Model.xorSum (fun i => Model.xorSum (fun j => decide (i < j) && a.testBit i && a.testBit j &&
    g i j) m) n

@[expose] def qpolar (g : ℕ → ℕ → Bool) (n m x y : ℕ) : Bool :=
  Model.xorSum (fun i => Model.xorSum (fun j =>
    (decide (i < j) && x.testBit i && y.testBit j && g i j) ^^
      (decide (i < j) && y.testBit i && x.testBit j && g i j)) m) n

theorem qform_quad (g : ℕ → ℕ → Bool) (n m : ℕ) : Quad (qform g n m) := by
  have h0 : qform g n m 0 = false := by
    unfold qform
    simp only [Nat.zero_testBit, Bool.and_false, Bool.false_and, xorSum_false]
  refine quad_of_polar (qpolar g n m) (fun x y => ?_) (fun x x' y => ?_)
  · rw [h0, Bool.xor_false]
    unfold qform qpolar
    rw [← xorSum_xor, ← xorSum_xor]
    congr 1
    funext i
    rw [← xorSum_xor, ← xorSum_xor]
    congr 1
    funext j
    rw [Nat.testBit_xor, Nat.testBit_xor]
    generalize decide (i < j) = p₀
    generalize x.testBit i = p₁
    generalize x.testBit j = p₂
    generalize y.testBit i = p₃
    generalize y.testBit j = p₄
    generalize g i j = p₅
    revert p₀ p₁ p₂ p₃ p₄ p₅
    decide
  · unfold qpolar
    rw [← xorSum_xor]
    congr 1
    funext i
    rw [← xorSum_xor]
    congr 1
    funext j
    rw [Nat.testBit_xor, Nat.testBit_xor]
    generalize decide (i < j) = p₀
    generalize x.testBit i = p₁
    generalize x.testBit j = p₂
    generalize x'.testBit i = p₃
    generalize x'.testBit j = p₄
    generalize y.testBit i = p₆
    generalize y.testBit j = p₇
    generalize g i j = p₅
    revert p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇
    decide

theorem kappaN_quad (p : Array ℕ) : Quad (Model.kappaN p) :=
  qform_quad (Model.betaPN p) 12 12

structure SAff (f : Bool → ℕ → Bool × Bool × ℕ) : Prop where
  eta : ∀ η c, (f η c).2.1 = (f η 0).2.1
  aff : ∀ η, Aff fun c => (f η c).2.2
  quad : ∀ η, Quad fun c => (f η c).1

theorem eYN_true (a c : ℕ) :
    Model.eYN a true c = (Model.kN a (Model.pi0N c), true, Model.pi0N c) := rfl

theorem eYN_false (a c : ℕ) :
    Model.eYN a false c = (Model.thetaBit (Model.pi0N c) a, false, Model.shiftN a (Model.pi0N c)) :=
  rfl

theorem sAff_eYN (a : ℕ) : SAff (Model.eYN a) where
  eta η c := by cases η <;> rfl
  aff η := by
    cases η
    · simp only [eYN_false]
      exact aff_comp (shiftN_aff a) pi0N_lin.aff
    · simp only [eYN_true]
      exact pi0N_lin.aff
  quad η := by
    cases η
    · simp only [eYN_false]
      exact quad_comp (f := fun c => Model.thetaBit c a) (thetaBit_quad a) pi0N_lin.aff
    · simp only [eYN_true]
      exact quad_comp (f := fun c => Model.kN a c) (kN_quad a) pi0N_lin.aff

theorem ePauliN_eq (q : Model.Pauli) (η : Bool) (c : ℕ) : Model.ePauliN q η c =
    (q.s ^^ (η && Model.mu0N q.a) ^^ Model.pairN (Model.shiftN q.a (Model.pi0N c)) q.d,
      η ^^ Model.pairN 63 q.d, Model.shiftN q.a (Model.pi0N c)) := rfl

theorem sAff_ePauliN (q : Model.Pauli) : SAff (Model.ePauliN q) where
  eta _ _ := rfl
  aff η := by
    simp only [ePauliN_eq]
    exact aff_comp (shiftN_aff q.a) pi0N_lin.aff
  quad η := by
    simp only [ePauliN_eq]
    exact quad_xor (f := fun _ => (q.s ^^ (η && Model.mu0N q.a))) (quad_const _)
      (quad_comp (f := fun a => Model.pairN a q.d) (pairN_left q.d).baff.quad
        (aff_comp (shiftN_aff q.a) pi0N_lin.aff))

theorem ePermN_eq (p : Array ℕ) (η : Bool) (c : ℕ) : Model.ePermN p η c =
    (Model.kappaN p (Model.pi0N c) ^^
      ((η ^^ Model.kappaN p 63) && Model.mu0N (Model.permCN p (Model.pi0N c))),
      η ^^ Model.kappaN p 63, Model.pi0N (Model.permCN p (Model.pi0N c))) := rfl

theorem sAff_ePermN (p : Array ℕ) : SAff (Model.ePermN p) where
  eta _ _ := rfl
  aff η := by
    simp only [ePermN_eq]
    exact (pi0N_lin.comp ((permCN_lin p).comp pi0N_lin)).aff
  quad η := by
    simp only [ePermN_eq]
    exact quad_xor (quad_comp (kappaN_quad p) pi0N_lin.aff)
      (and_const_lin (mu0N_lin.comp ((permCN_lin p).comp pi0N_lin)) _).baff.quad

theorem rowChain_cons (f : Bool → ℕ → Bool × Bool × ℕ) (fs : List (Bool → ℕ → Bool × Bool × ℕ))
    (η : Bool) (c : ℕ) : Native.Sp8.rowChain (f :: fs) η c =
      ((f η c).1 ^^ (Native.Sp8.rowChain fs (f η c).2.1 (f η c).2.2).1,
        (Native.Sp8.rowChain fs (f η c).2.1 (f η c).2.2).2.1,
        (Native.Sp8.rowChain fs (f η c).2.1 (f η c).2.2).2.2) := rfl

theorem sAff_rowChain : ∀ fs : List (Bool → ℕ → Bool × Bool × ℕ), (∀ f ∈ fs, SAff f) →
    SAff (Native.Sp8.rowChain fs)
  | [], _ => ⟨fun _ _ => rfl, fun _ x y => by simp only [Native.Sp8.rowChain, Nat.xor_zero],
      fun _ => quad_const false⟩
  | f :: fs, h => by
    have hf := h f List.mem_cons_self
    have ih := sAff_rowChain fs fun g hg => h g (List.mem_cons_of_mem _ hg)
    have e : ∀ η c, Native.Sp8.rowChain fs (f η c).2.1 (f η c).2.2 =
        Native.Sp8.rowChain fs (f η 0).2.1 (f η c).2.2 := fun η c => by rw [hf.eta η c]
    refine ⟨fun η c => ?_, fun η => ?_, fun η => ?_⟩
    · rw [rowChain_cons, rowChain_cons, e, e η 0, ih.eta, ih.eta _ (f η 0).2.2]
    · have h1 : (fun c => (Native.Sp8.rowChain (f :: fs) η c).2.2) =
          fun c => (Native.Sp8.rowChain fs (f η 0).2.1 (f η c).2.2).2.2 := by
        funext c
        rw [rowChain_cons, e]
      rw [h1]
      exact aff_comp (g := fun c => (Native.Sp8.rowChain fs (f η 0).2.1 c).2.2)
        (h := fun c => (f η c).2.2) (ih.aff (f η 0).2.1) (hf.aff η)
    · have h1 : (fun c => (Native.Sp8.rowChain (f :: fs) η c).1) =
          fun c => ((f η c).1 ^^ (Native.Sp8.rowChain fs (f η 0).2.1 (f η c).2.2).1) := by
        funext c
        rw [rowChain_cons, e]
      rw [h1]
      exact quad_xor (f := fun c => (f η c).1)
        (g := fun c => (Native.Sp8.rowChain fs (f η 0).2.1 (f η c).2.2).1) (hf.quad η)
        (quad_comp (f := fun c => (Native.Sp8.rowChain fs (f η 0).2.1 c).1)
          (g := fun c => (f η c).2.2) (ih.quad (f η 0).2.1) (hf.aff η))

theorem xor_two_pow_of_lt {y n : ℕ} (hy : y < 2 ^ n) : y ^^^ 2 ^ n = y + 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.add_comm, Nat.testBit_two_pow]
  rcases Nat.lt_trichotomy i n with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]
    simp [Nat.ne_of_gt h]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]
    simp
  · have h1 : y < 2 ^ i := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : 2 ^ n + y < 2 ^ i := by
      have : 2 ^ (n + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at this
      omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [Nat.ne_of_lt h]

theorem lt_succ_cases {x n : ℕ} (hx : x < 2 ^ (n + 1)) :
    x < 2 ^ n ∨ ∃ y < 2 ^ n, x = y ^^^ 2 ^ n := by
  by_cases h : x < 2 ^ n
  · exact Or.inl h
  · refine Or.inr ⟨x - 2 ^ n, ?_, ?_⟩
    · rw [Nat.pow_succ] at hx
      omega
    · rw [xor_two_pow_of_lt (by rw [Nat.pow_succ] at hx; omega)]
      omega

theorem baff_zero {f : ℕ → Bool} (hf : BAff f) (h0 : f 0 = false) {n : ℕ}
    (hb : ∀ i < n, f (2 ^ i) = false) : ∀ x < 2 ^ n, f x = false := by
  induction n with
  | zero =>
    intro x hx
    rw [Nat.pow_zero] at hx
    rw [Nat.lt_one_iff.1 hx, h0]
  | succ n ih =>
    intro x hx
    rcases lt_succ_cases hx with h | ⟨y, hy, rfl⟩
    · exact ih (fun i hi => hb i (by omega)) x h
    · rw [hf, ih (fun i hi => hb i (by omega)) y hy, hb n (by omega), h0]
      rfl

theorem aff_eq {g h : ℕ → ℕ} (hg : Aff g) (hh : Aff h) (h0 : g 0 = h 0) {n : ℕ}
    (hb : ∀ i < n, g (2 ^ i) = h (2 ^ i)) : ∀ x < 2 ^ n, g x = h x := by
  induction n with
  | zero =>
    intro x hx
    rw [Nat.pow_zero] at hx
    rw [Nat.lt_one_iff.1 hx, h0]
  | succ n ih =>
    intro x hx
    rcases lt_succ_cases hx with h | ⟨y, hy, rfl⟩
    · exact ih (fun i hi => hb i (by omega)) x h
    · rw [hg, hh, ih (fun i hi => hb i (by omega)) y hy, hb n (by omega), h0]

theorem cube_zero_left (f : ℕ → Bool) (y z e : ℕ) : cube f 0 y z e =
    (f 0 ^^ f y ^^ f z ^^ f e ^^ f (y ^^^ z) ^^ f (y ^^^ e) ^^ f (z ^^^ e) ^^ f (y ^^^ z ^^^ e)) := by
  simp only [cube, Nat.zero_xor]

theorem quad_diff {f : ℕ → Bool} (hf : Quad f) (e : ℕ) : BAff fun y => (f (y ^^^ e) ^^ f y) := by
  intro y z
  have h := hf 0 y z e
  rw [cube_zero_left] at h
  dsimp only
  rw [Nat.zero_xor]
  revert h
  generalize f 0 = p₀
  generalize f y = p₁
  generalize f z = p₂
  generalize f e = p₃
  generalize f (y ^^^ z) = p₄
  generalize f (y ^^^ e) = p₅
  generalize f (z ^^^ e) = p₆
  generalize f (y ^^^ z ^^^ e) = p₇
  revert p₀ p₁ p₂ p₃ p₄ p₅ p₆ p₇
  decide

theorem two_pow_mem_spanRows_aux : ∀ i, i < 12 → 2 ^ i ∈ spanRows := by
  decide +kernel

theorem two_pow_mem_spanRows {i : ℕ} (hi : i < 12) : 2 ^ i ∈ spanRows :=
  two_pow_mem_spanRows_aux i hi

theorem two_pow_add_mem_spanRows_aux : ∀ j, j < 12 → ∀ i, i < j → 2 ^ i + 2 ^ j ∈ spanRows := by
  decide +kernel

theorem two_pow_add_mem_spanRows {i j : ℕ} (hij : i < j) (hj : j < 12) :
    2 ^ i + 2 ^ j ∈ spanRows :=
  two_pow_add_mem_spanRows_aux j hj i hij

theorem quad_eq_false {f : ℕ → Bool} (hf : Quad f) (hs : ∀ x ∈ spanRows, f x = false) :
    ∀ n ≤ 12, ∀ x < 2 ^ n, f x = false := by
  intro n
  induction n with
  | zero =>
    intro _ x hx
    rw [Nat.pow_zero] at hx
    rw [Nat.lt_one_iff.1 hx]
    exact hs 0 List.mem_cons_self
  | succ n ih =>
    intro hn x hx
    rcases lt_succ_cases hx with h | ⟨y, hy, rfl⟩
    · exact ih (by omega) x h
    · have hd := quad_diff hf (2 ^ n)
      have hz : ∀ y < 2 ^ n, (f (y ^^^ 2 ^ n) ^^ f y) = false := by
        refine baff_zero hd ?_ fun i hi => ?_
        · rw [Nat.zero_xor, hs _ (two_pow_mem_spanRows (by omega)),
            hs 0 List.mem_cons_self]
          rfl
        · have hi' : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by decide) hi
          rw [xor_two_pow_of_lt hi', hs _ (two_pow_add_mem_spanRows hi (by omega)),
            hs _ (two_pow_mem_spanRows (by omega))]
          rfl
      have h1 := hz y hy
      rw [ih (by omega) y hy, Bool.xor_false] at h1
      exact h1

theorem eq_of_span {F G : Bool → ℕ → Bool × Bool × ℕ} (hF : SAff F) (hG : SAff G)
    (h : ∀ c ∈ spanRows, ∀ η, F η c = G η c) : ∀ η, ∀ c < 4096, F η c = G η c := by
  intro η c hc
  have h0 := h 0 List.mem_cons_self η
  have hc' : c < 2 ^ 12 := hc
  have e1 : (F η c).2.1 = (G η c).2.1 := by
    rw [hF.eta, hG.eta, h0]
  have e2 : (F η c).2.2 = (G η c).2.2 :=
    aff_eq (g := fun c => (F η c).2.2) (h := fun c => (G η c).2.2) (hF.aff η) (hG.aff η)
      (by rw [h0]) (fun i hi => by rw [h _ (two_pow_mem_spanRows hi)]) c hc'
  have e3 : ((F η c).1 ^^ (G η c).1) = false :=
    quad_eq_false (f := fun c => ((F η c).1 ^^ (G η c).1)) (quad_xor (hF.quad η) (hG.quad η))
      (fun x hx => by rw [h x hx, Bool.xor_self]) 12 le_rfl c hc'
  have e4 : (F η c).1 = (G η c).1 := by
    revert e3
    cases (F η c).1 <;> cases (G η c).1 <;> decide
  exact Prod.ext e4 (Prod.ext e1 e2)

theorem rowChainEq_of_spanEq {fs gs : List (Bool → ℕ → Bool × Bool × ℕ)}
    (hf : ∀ f ∈ fs, SAff f) (hg : ∀ g ∈ gs, SAff g)
    (h : ∀ c ∈ spanRows, ∀ η, Native.Sp8.rowChain fs η c = Native.Sp8.rowChain gs η c) :
    Native.Sp8.rowChainEq fs gs = true := by
  have e := eq_of_span (sAff_rowChain fs hf) (sAff_rowChain gs hg) h
  unfold Native.Sp8.rowChainEq
  rw [List.all_eq_true]
  intro c hc
  rw [List.all_eq_true]
  intro η _
  rw [e η c (List.mem_range.1 hc), beq_self_eq_true]

@[expose] def Twin (t : ℕ → ℕ → ℕ) (f : Bool → ℕ → Bool × Bool × ℕ) : Prop :=
  ∀ η c, t η.toNat c = encB (f η c)

@[expose] def thenRest (fs : List (Bool → ℕ → Bool × Bool × ℕ)) (r : Bool × Bool × ℕ) :
    Bool × Bool × ℕ :=
  (r.1 ^^ (Native.Sp8.rowChain fs r.2.1 r.2.2).1, (Native.Sp8.rowChain fs r.2.1 r.2.2).2.1,
    (Native.Sp8.rowChain fs r.2.1 r.2.2).2.2)

theorem thenRest_cons (f : Bool → ℕ → Bool × Bool × ℕ) (fs : List (Bool → ℕ → Bool × Bool × ℕ))
    (r : Bool × Bool × ℕ) : thenRest (f :: fs) r = thenRest fs (thenB f r) := by
  unfold thenRest thenB
  rw [rowChain_cons, Bool.xor_assoc]

theorem foldl_thenT : ∀ {ts : List (ℕ → ℕ → ℕ)} {fs : List (Bool → ℕ → Bool × Bool × ℕ)},
    List.Forall₂ Twin ts fs → ∀ r : Bool × Bool × ℕ,
      ts.foldl (fun r f => thenT f r) (encB r) = encB (thenRest fs r)
  | _, _, .nil, r => by
    unfold thenRest
    rw [List.foldl_nil, Native.Sp8.rowChain, Bool.xor_false]
  | t :: ts, f :: fs, .cons ht h, r => by
    rw [List.foldl_cons, thenT_eq t f ht, foldl_thenT h, thenRest_cons]

theorem chainT_eq {ts : List (ℕ → ℕ → ℕ)} {fs : List (Bool → ℕ → Bool × Bool × ℕ)}
    (h : List.Forall₂ Twin ts fs) (η : Bool) (c : ℕ) :
    chainT ts η.toNat c = encB (Native.Sp8.rowChain fs η c) := by
  cases h with
  | nil => rfl
  | cons ht h =>
    rename_i t f ts fs
    rw [chainT, ht, foldl_thenT h, rowChain_cons]
    rfl

theorem rowChainEq_of_spanEqT {L R : List (ℕ → ℕ → ℕ)} {fs gs : List (Bool → ℕ → Bool × Bool × ℕ)}
    (hL : List.Forall₂ Twin L fs) (hR : List.Forall₂ Twin R gs)
    (hf : ∀ f ∈ fs, SAff f) (hg : ∀ g ∈ gs, SAff g) (h : spanEqT L R = true) :
    Native.Sp8.rowChainEq fs gs = true := by
  refine rowChainEq_of_spanEq hf hg fun c hc η => ?_
  unfold spanEqT at h
  have h1 := List.all_eq_true.1 h c hc
  rw [Bool.and_eq_true] at h1
  apply encB_inj
  rw [← chainT_eq hL, ← chainT_eq hR]
  cases η
  · exact Nat.eq_of_beq_eq_true h1.1
  · exact Nat.eq_of_beq_eq_true h1.2

theorem twin_eYT (a : ℕ) : Twin (eYT a) (Model.eYN a) := eYT_eq a

theorem twin_ePauliT (s : Bool) (a d : ℕ) : Twin (ePauliT s.toNat a d) (Model.ePauliN (s, a, d)) :=
  ePauliT_eq s a d

theorem twin_ePermT {P : ℕ} {p : Array ℕ} (hP : ∀ i < 24, KDense.pe P i = p[i]!) {BT K : ℕ}
    (hBT : KDense.betaTabT P = BT) (hK : (Model.kappaN p 63).toNat = K) :
    Twin (ePermT P BT K) (Model.ePermN p) :=
  ePermT_eq hP hBT hK

end CFSG.KC.Sp8Span

end
