module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseGam

public section

namespace CFSG.OddStandard.AltStdSec.SylowSn

@[expose] def Wc : ℕ → Type
  | 0 => Unit
  | a + 1 => Wc a × Wc a × Bool

instance instFintypeWc : (a : ℕ) → Fintype (Wc a)
  | 0 => inferInstanceAs (Fintype Unit)
  | a + 1 => haveI := instFintypeWc a; inferInstanceAs (Fintype (Wc a × Wc a × Bool))

instance instDecidableEqWc : (a : ℕ) → DecidableEq (Wc a)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | a + 1 => haveI := instDecidableEqWc a; inferInstanceAs (DecidableEq (Wc a × Wc a × Bool))

def Wc.mul : (a : ℕ) → Wc a → Wc a → Wc a
  | 0, _, _ => ()
  | a + 1, (u, v, false), (u', v', q') => (Wc.mul a u u', Wc.mul a v v', q')
  | a + 1, (u, v, true), (u', v', q') => (Wc.mul a u v', Wc.mul a v u', !q')

def Wc.one : (a : ℕ) → Wc a
  | 0 => ()
  | a + 1 => (Wc.one a, Wc.one a, false)

def Wc.fix : (a : ℕ) → Wc a → ℕ
  | 0, _ => 1
  | a + 1, (u, v, q) => if q then 0 else Wc.fix a u + Wc.fix a v

def Wc.sg : (a : ℕ) → Wc a → Bool
  | 0, _ => false
  | a + 1, (u, v, q) => xor (xor (Wc.sg a u) (Wc.sg a v)) (q && decide (a = 0))

def zq (q : Bool) : Z2 := if q then z2 else 1

@[simp] theorem zq_false : zq false = 1 := by simp [zq]

@[simp] theorem zq_true : zq true = z2 := by simp [zq]

def toW : (a : ℕ) → Wc a → W a
  | 0, _ => 1
  | a + 1, (u, v, q) => wr (toW a u) (toW a v) (zq q)

theorem z2_mul_zq (q : Bool) : z2 * zq q = zq (!q) := by
  cases q
  · simp
  · simp [z2_mul_self]

theorem toW_mul : ∀ (a : ℕ) (x y : Wc a), toW a (Wc.mul a x y) = toW a x * toW a y
  | 0, _, _ => Subsingleton.elim _ _
  | a + 1, (u, v, false), (u', v', q') => by
    show wr (toW a (Wc.mul a u u')) (toW a (Wc.mul a v v')) (zq q') =
      wr (toW a u) (toW a v) (zq false) * wr (toW a u') (toW a v') (zq q')
    rw [zq_false, wr_mul_one, toW_mul a u u', toW_mul a v v']
  | a + 1, (u, v, true), (u', v', q') => by
    show wr (toW a (Wc.mul a u v')) (toW a (Wc.mul a v u')) (zq (!q')) =
      wr (toW a u) (toW a v) (zq true) * wr (toW a u') (toW a v') (zq q')
    rw [zq_true, wr_mul_z2, toW_mul a u v', toW_mul a v u', z2_mul_zq]

theorem toW_one : ∀ a : ℕ, toW a (Wc.one a) = 1
  | 0 => Subsingleton.elim _ _
  | a + 1 => by
    show wr (toW a (Wc.one a)) (toW a (Wc.one a)) (zq false) = 1
    rw [zq_false, toW_one a]
    exact wr_one

theorem toW_injective : ∀ a : ℕ, Function.Injective (toW a)
  | 0 => fun x y _ => Subsingleton.elim (α := Unit) x y
  | a + 1 => by
    rintro ⟨u, v, q⟩ ⟨u', v', q'⟩ h
    have h' : wr (toW a u) (toW a v) (zq q) = wr (toW a u') (toW a v') (zq q') := h
    obtain ⟨h1, h2, h3⟩ := wr_inj.1 h'
    have h4 : q = q' := by
      cases q <;> cases q' <;> simp_all [z2_ne_one, z2_ne_one.symm]
    rw [toW_injective a h1, toW_injective a h2, h4]

theorem toW_surjective : ∀ a : ℕ, Function.Surjective (toW a)
  | 0 => fun w => ⟨(), Subsingleton.elim _ _⟩
  | a + 1 => by
    intro w
    obtain ⟨u, hu⟩ := toW_surjective a (w.left 1)
    obtain ⟨v, hv⟩ := toW_surjective a (w.left z2)
    rcases z2_cases w.right with h | h
    · refine ⟨(u, v, false), ?_⟩
      show wr (toW a u) (toW a v) 1 = w
      rw [hu, hv]
      exact (congrArg (wr (w.left 1) (w.left z2)) h.symm).trans (wr_eta w)
    · refine ⟨(u, v, true), ?_⟩
      show wr (toW a u) (toW a v) z2 = w
      rw [hu, hv]
      exact (congrArg (wr (w.left 1) (w.left z2)) h.symm).trans (wr_eta w)

theorem fixW_toW : ∀ (a : ℕ) (x : Wc a), fixW a (toW a x) = Wc.fix a x
  | 0, _ => fixW_zero _
  | a + 1, (u, v, q) => by
    show fixW (a + 1) (wr (toW a u) (toW a v) (zq q)) = Wc.fix (a + 1) (u, v, q)
    rw [fixW_wr, fixW_toW a u, fixW_toW a v]
    cases q
    · simp [Wc.fix]
    · simp [Wc.fix, z2_ne_one]

theorem sgW_toW : ∀ (a : ℕ) (x : Wc a), sgW a (toW a x) = if Wc.sg a x then -1 else 1
  | 0, _ => by
    rw [sgW_zero]
    rfl
  | a + 1, (u, v, q) => by
    show sgW (a + 1) (wr (toW a u) (toW a v) (zq q)) =
      if Wc.sg (a + 1) (u, v, q) then -1 else 1
    rw [sgW_succ, wr_left_one, wr_left_z2, wr_right, sgW_toW a u, sgW_toW a v]
    have e : (if zq q = 1 then (1 : ℤˣ) else (-1) ^ (2 ^ a)) =
        if (q && decide (a = 0)) then -1 else 1 := by
      cases q
      · simp
      · rcases Nat.eq_zero_or_pos a with rfl | ha
        · simp [z2_ne_one]
        · have h2 : Even (2 ^ a) := Nat.even_pow.2 ⟨even_two, by omega⟩
          have h3 : a ≠ 0 := by omega
          simp [z2_ne_one, h2.neg_one_pow, h3]
    rw [e]
    show _ = if xor (xor (Wc.sg a u) (Wc.sg a v)) (q && decide (a = 0)) = true then -1 else 1
    generalize Wc.sg a u = s1
    generalize Wc.sg a v = s2
    generalize (q && decide (a = 0)) = s3
    cases s1 <;> cases s2 <;> cases s3 <;> decide

@[expose] def nearModel (l : List ℕ) : Set (Gam l) :=
  {γ | sgG l γ = 1 ∧ (γ = 1 ∨ (γ * γ = 1 ∧ γ ≠ 1 ∧ 4 ≤ fixG l γ))}

theorem nearModel_sq {l : List ℕ} {γ : Gam l} (h : γ ∈ nearModel l) : γ * γ = 1 := by
  rcases h.2 with rfl | h
  · exact one_mul _
  · exact h.1

abbrev Gc := Wc 2 × Wc 3

def Gc.mul (x y : Gc) : Gc := (Wc.mul 2 x.1 y.1, Wc.mul 3 x.2 y.2)

def Gc.one : Gc := (Wc.one 2, Wc.one 3)

def Gc.fix (x : Gc) : ℕ := Wc.fix 2 x.1 + Wc.fix 3 x.2

def Gc.sg (x : Gc) : Bool := xor (Wc.sg 2 x.1) (Wc.sg 3 x.2)

def Gc.near (x : Gc) : Bool :=
  decide (Gc.sg x = false ∧ (x = Gc.one ∨ (Gc.mul x x = Gc.one ∧ x ≠ Gc.one ∧ 4 ≤ Gc.fix x)))

def toG (x : Gc) : Gam [2, 3] := Gam.cons (toW 2 x.1) (Gam.cons (toW 3 x.2) 1)

theorem toG_mul (x y : Gc) : toG (Gc.mul x y) = toG x * toG y :=
  Prod.ext (toW_mul 2 x.1 y.1) (Prod.ext (toW_mul 3 x.2 y.2) (Subsingleton.elim _ _))

theorem toG_one : toG Gc.one = 1 :=
  Prod.ext (toW_one 2) (Prod.ext (toW_one 3) (Subsingleton.elim _ _))

theorem toG_injective : Function.Injective toG := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  have h1 := (Prod.ext_iff.1 h).1
  have h2 := (Prod.ext_iff.1 (Prod.ext_iff.1 h).2).1
  rw [toW_injective 2 h1, toW_injective 3 h2]

theorem toG_surjective : Function.Surjective toG := by
  rintro ⟨w₂, w₃, u⟩
  obtain ⟨x₂, rfl⟩ := toW_surjective 2 w₂
  obtain ⟨x₃, rfl⟩ := toW_surjective 3 w₃
  exact ⟨(x₂, x₃), Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _))⟩

theorem fixG_toG (x : Gc) : fixG [2, 3] (toG x) = Gc.fix x := by
  show fixW 2 (toW 2 x.1) + (fixW 3 (toW 3 x.2) + 0) = Wc.fix 2 x.1 + Wc.fix 3 x.2
  rw [fixW_toW, fixW_toW, add_zero]

theorem sgG_toG (x : Gc) : sgG [2, 3] (toG x) = 1 ↔ Gc.sg x = false := by
  have h : sgG [2, 3] (toG x) = sgW 2 (toW 2 x.1) * (sgW 3 (toW 3 x.2) * 1) := by
    show sgG (2 :: [3]) (Gam.cons (toW 2 x.1) (Gam.cons (toW 3 x.2) 1)) = _
    rw [sgG_cons, sgG_cons, map_one]
  rw [h, sgW_toW, sgW_toW, Gc.sg]
  generalize Wc.sg 2 x.1 = s1
  generalize Wc.sg 3 x.2 = s2
  cases s1 <;> cases s2 <;> decide

theorem toG_mem_nearModel_iff (x : Gc) : toG x ∈ nearModel [2, 3] ↔ Gc.near x = true := by
  have h1 : toG x = 1 ↔ x = Gc.one := by
    rw [← toG_one]
    exact toG_injective.eq_iff
  have h2 : toG x * toG x = 1 ↔ Gc.mul x x = Gc.one := by
    rw [← toG_mul, ← toG_one]
    exact toG_injective.eq_iff
  rw [Gc.near, decide_eq_true_iff]
  show (sgG [2, 3] (toG x) = 1 ∧ (toG x = 1 ∨ (toG x * toG x = 1 ∧ toG x ≠ 1 ∧
    4 ≤ fixG [2, 3] (toG x)))) ↔ _
  rw [sgG_toG, fixG_toG, ne_eq, ne_eq, h1, h2]

theorem prodCnt_eq_card_pairs {H : Type*} [Group H] {Ω : Set H} (hΩ : ∀ w ∈ Ω, w * w = 1)
    (g : H) :
    prodCnt Ω g = Nat.card {p : H × H // p.1 ∈ Ω ∧ p.2 ∈ Ω ∧ p.2 * p.1 * g ∈ Ω} := by
  have hsq : ∀ a b c : H, a * a = 1 → b * b = 1 → a * b * c = g → c = b * a * g := by
    intro a b c ha hb h
    rw [← h]
    symm
    calc b * a * (a * b * c) = b * (a * a) * (b * c) := by simp only [mul_assoc]
      _ = c := by rw [ha, mul_one, ← mul_assoc, hb, one_mul]
  have hback : ∀ a b : H, a * a = 1 → b * b = 1 → a * b * (b * a * g) = g := by
    intro a b ha hb
    calc a * b * (b * a * g) = a * (b * b) * a * g := by simp only [mul_assoc]
      _ = g := by rw [hb, mul_one, ha, one_mul]
  unfold prodCnt
  refine Nat.card_congr
    { toFun := fun t => ⟨(t.1.1, t.1.2.1), t.2.1, t.2.2.1, by
        rw [← hsq _ _ _ (hΩ _ t.2.1) (hΩ _ t.2.2.1) t.2.2.2.2]
        exact t.2.2.2.1⟩
      invFun := fun p => ⟨(p.1.1, p.1.2, p.1.2 * p.1.1 * g), p.2.1, p.2.2.1, p.2.2.2,
        hback _ _ (hΩ _ p.2.1) (hΩ _ p.2.2.1)⟩
      left_inv := fun t => by
        obtain ⟨⟨a, b, c⟩, ha, hb, hc, habc⟩ := t
        exact Subtype.ext (Prod.ext rfl (Prod.ext rfl (hsq a b c (hΩ _ ha) (hΩ _ hb) habc).symm))
      right_inv := fun p => rfl }

def Gc.omega : Finset Gc := Finset.univ.filter (fun x => Gc.near x = true)

def Gc.cnt (g : Gc) : ℕ :=
  ∑ a ∈ Gc.omega, ∑ b ∈ Gc.omega, if Gc.near (Gc.mul (Gc.mul b a) g) = true then 1 else 0

theorem card_pairs_Gc (g : Gc) :
    Nat.card {p : Gc × Gc // Gc.near p.1 = true ∧ Gc.near p.2 = true ∧
      Gc.near (Gc.mul (Gc.mul p.2 p.1) g) = true} = Gc.cnt g := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  unfold Gc.cnt Gc.omega
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter]
  by_cases ha : Gc.near a = true
  · simp only [ha, ↓reduceIte]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : Gc.near b = true <;> simp [hb]
  · simp [ha]

theorem prodCnt_nearModel_toG (g : Gc) : prodCnt (nearModel [2, 3]) (toG g) = Gc.cnt g := by
  rw [prodCnt_eq_card_pairs (fun w hw => nearModel_sq hw), ← card_pairs_Gc g]
  symm
  refine Nat.card_congr
    ((Equiv.prodCongr (Equiv.ofBijective toG ⟨toG_injective, toG_surjective⟩)
      (Equiv.ofBijective toG ⟨toG_injective, toG_surjective⟩)).subtypeEquiv fun p => ?_)
  show _ ↔ (toG p.1 ∈ nearModel [2, 3] ∧ toG p.2 ∈ nearModel [2, 3] ∧
    toG p.2 * toG p.1 * toG g ∈ nearModel [2, 3])
  rw [← toG_mul, ← toG_mul, toG_mem_nearModel_iff, toG_mem_nearModel_iff,
    toG_mem_nearModel_iff]

theorem cnt_one : Gc.cnt Gc.one = 3283 := by decide +kernel

theorem cnt_central : ∀ γ : Gc, Gc.near γ = true → γ ≠ Gc.one →
    (∀ δ : Gc, Gc.sg δ = false → Gc.mul δ γ = Gc.mul γ δ) →
    Gc.cnt γ = 3205 ∨ Gc.cnt γ = 3175 := by
  decide +kernel

theorem nearFinite (γ : Gam [2, 3]) (hγ : γ ∈ nearModel [2, 3]) (hγ1 : γ ≠ 1)
    (hc : ∀ δ : Gam [2, 3], sgG [2, 3] δ = 1 → δ * γ = γ * δ) :
    prodCnt (nearModel [2, 3]) 1 ≠ prodCnt (nearModel [2, 3]) γ := by
  obtain ⟨g, rfl⟩ := toG_surjective γ
  rw [← toG_one, prodCnt_nearModel_toG, prodCnt_nearModel_toG, cnt_one]
  have h := cnt_central g ((toG_mem_nearModel_iff g).1 hγ)
    (fun h => hγ1 (by rw [h, toG_one])) (fun δ hδ => by
      apply toG_injective
      rw [toG_mul, toG_mul]
      exact hc (toG δ) ((sgG_toG δ).2 hδ))
  omega

end CFSG.OddStandard.AltStdSec.SylowSn
