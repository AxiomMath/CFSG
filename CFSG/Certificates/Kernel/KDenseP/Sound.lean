module

public import Certificates.Data.Kernel.KDenseP.Init
public import CFSG.Certificates.Kernel.KDense.Sound

public section

namespace CFSG.KC.KDenseP

open CFSG.KC.KDense CFSG.Monster.AxisCount

@[expose] noncomputable def resN (n : ℕ) (v : Native.DVec) (k : ℕ) : ZMod (2 ^ n - 1) :=
  (v.D.getD k 0 : ZMod (2 ^ n - 1)) * (2 ^ (n - 1)) ^ v.e

@[expose] noncomputable def resPN (n S x p : ℕ) : ZMod (2 ^ n - 1) :=
  ((∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2) : ℕ) : ZMod (2 ^ n - 1))

@[expose] def RepN (n : ℕ) (v : Native.DVec) (s : St) : Prop :=
  (∀ q < 98280, resPN n SX s.2.1 (xposK q) = resN n v (300 + q)) ∧
  (∀ p < SX, (∀ q < 98280, xposK q ≠ p) → resPN n SX s.2.1 p = 0) ∧ s.2.1 < 2 ^ (n * SX) ∧
  (∀ i < 24, ∀ j < 24, resPN n SA s.2.2.1 (32 * i + j) = resN n v (Native.aIdx i j)) ∧
  (∀ p < SA, (24 ≤ p % 32 ∨ 24 ≤ p / 32) → resPN n SA s.2.2.1 p = 0) ∧ s.2.2.1 < 2 ^ (n * SA) ∧
  (∀ r < 4096, ∀ j < 24, resPN n SX s.2.2.2 (32 * r + j) = resN n v (98580 + 24 * r + j)) ∧
  (∀ p < SX, 24 ≤ p % 32 → resPN n SX s.2.2.2 p = 0) ∧ s.2.2.2 < 2 ^ (n * SX)

namespace ListAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense.InitAux

@[expose] noncomputable def stepPl (n lo k r : ℕ) (R : Bool × ℕ × ℕ × ℕ) : Bool × ℕ × ℕ × ℕ :=
  Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun ok rest =>
    Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun X rest2 =>
      Prod.rec (motive := fun _ => Bool × Nat × Nat × Nat) (fun A W =>
        Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
          (Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
            (andB ok (andB (Nat.ble lo k) (Nat.blt k (nat_lit 196884))), X, A,
              Nat.lor W (putR SX n r ((fun u => Nat.add (Nat.mul (nat_lit 32) (Nat.div u (nat_lit 24)))
                (Nat.mod u (nat_lit 24))) (Nat.sub k (nat_lit 98580)))))
            (andB ok (Nat.ble lo k), Nat.lor X (putR SX n r (xposT (Nat.sub k (nat_lit 300)))), A, W)
            (Nat.blt k (nat_lit 98580)))
          (Bool.rec (motive := fun _ => Bool × Nat × Nat × Nat)
            ((fun p => (andB ok (Nat.ble lo k), X,
                Nat.lor A (Nat.lor (putR SA n r p)
                  (putR SA n r (Nat.add (Nat.mul (nat_lit 32) (Nat.mod p (nat_lit 32)))
                    (Nat.div p (nat_lit 32))))), W))
              (pairPos k))
            (andB ok (Nat.ble lo k), X, Nat.lor A (putR SA n r (Nat.mul (nat_lit 33) k)), W)
            (Nat.blt k (nat_lit 24)))
          (Nat.blt k (nat_lit 300))) rest2) rest) R

theorem listPl_cons (n lo k : ℕ) (z : ℤ) (L : List (ℕ × ℤ)) :
    listPl n ((k, z) :: L) lo =
      stepPl n lo k (resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z) (listPl n L (k + 1)) := rfl

theorem blt_f {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
  omega

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem stepPl_W {n lo k r : ℕ} (ok : Bool) (X A W : ℕ) (h : 98580 ≤ k) :
    stepPl n lo k r (ok, X, A, W) = (andB ok (andB (Nat.ble lo k) (Nat.blt k 196884)), X, A,
      Nat.lor W (put SX n r (32 * ((k - 98580) / 24) + (k - 98580) % 24))) := by
  have h1 : Nat.blt k (nat_lit 300) = false := blt_f (b := 300) (by omega)
  have h2 : Nat.blt k (nat_lit 98580) = false := blt_f (b := 98580) h
  unfold stepPl
  rw [h1, h2]
  rfl

theorem stepPl_X {n lo k r : ℕ} (ok : Bool) (X A W : ℕ) (h1 : 300 ≤ k) (h2 : k < 98580) :
    stepPl n lo k r (ok, X, A, W) =
      (andB ok (Nat.ble lo k), Nat.lor X (put SX n r (xposT (k - 300))), A, W) := by
  have e1 : Nat.blt k (nat_lit 300) = false := blt_f (b := 300) h1
  have e2 : Nat.blt k (nat_lit 98580) = true := blt_t (b := 98580) h2
  unfold stepPl
  rw [e1, e2]
  rfl

theorem stepPl_D {n lo k r : ℕ} (ok : Bool) (X A W : ℕ) (h : k < 24) :
    stepPl n lo k r (ok, X, A, W) =
      (andB ok (Nat.ble lo k), X, Nat.lor A (put SA n r (33 * k)), W) := by
  have e1 : Nat.blt k (nat_lit 300) = true := blt_t (b := 300) (by omega)
  have e2 : Nat.blt k (nat_lit 24) = true := blt_t (b := 24) h
  unfold stepPl
  rw [e1, e2]
  rfl

theorem stepPl_P {n lo k r : ℕ} (ok : Bool) (X A W : ℕ) (h1 : 24 ≤ k) (h2 : k < 300) :
    stepPl n lo k r (ok, X, A, W) = (andB ok (Nat.ble lo k), X,
      Nat.lor A (Nat.lor (put SA n r (pairPos k))
        (put SA n r (32 * (pairPos k % 32) + pairPos k / 32))), W) := by
  have e1 : Nat.blt k (nat_lit 300) = true := blt_t (b := 300) h2
  have e2 : Nat.blt k (nat_lit 24) = false := blt_f (b := 24) h1
  unfold stepPl
  rw [e1, e2]
  rfl

@[expose] def PlaneChar (n S : ℕ) (Q : ℕ → ℕ → Prop) (r : ℤ → ℕ) (L : List (ℕ × ℤ)) (x : ℕ) : Prop :=
  ∀ y, x.testBit y = true ↔
    ∃ e ∈ L, ∃ q, Q e.1 q ∧ ∃ b < n, y = q + b * S ∧ (r e.2).testBit b = true

theorem planeChar_nil (n S : ℕ) (Q : ℕ → ℕ → Prop) (r : ℤ → ℕ) : PlaneChar n S Q r [] 0 :=
  fun y => by simp

theorem planeChar_cons {n S : ℕ} {Q : ℕ → ℕ → Prop} {r : ℤ → ℕ} {L : List (ℕ × ℤ)} {k : ℕ}
    {z : ℤ} {x x' : ℕ} (hx : PlaneChar n S Q r L x)
    (h : ∀ y, x'.testBit y = true ↔ x.testBit y = true ∨
      ∃ q, Q k q ∧ ∃ b < n, y = q + b * S ∧ (r z).testBit b = true) :
    PlaneChar n S Q r ((k, z) :: L) x' := fun y => by
  rw [h, hx]
  constructor
  · rintro (⟨e, he, hh⟩ | hh)
    · exact ⟨e, List.mem_cons_of_mem _ he, hh⟩
    · exact ⟨(k, z), List.mem_cons_self, hh⟩
  · rintro ⟨e, he, hh⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact Or.inr hh
    · exact Or.inl ⟨e, he, hh⟩

theorem testBit_lor (a b y : ℕ) :
    (Nat.lor a b).testBit y = true ↔ a.testBit y = true ∨ b.testBit y = true := by
  rw [lor_eq, Nat.testBit_or, Bool.or_eq_true]

theorem upd_none {x S n r : ℕ} {Q : ℕ → Prop} (hQ : ∀ q, ¬ Q q) (y : ℕ) :
    x.testBit y = true ↔ x.testBit y = true ∨
      ∃ q, Q q ∧ ∃ b < n, y = q + b * S ∧ r.testBit b = true :=
  (or_iff_left fun ⟨q, hq, _⟩ => hQ q hq).symm

theorem upd_one {x : ℕ} {S n r q₀ : ℕ} {Q : ℕ → Prop} (hQ : ∀ q, Q q ↔ q = q₀) (y : ℕ) :
    (Nat.lor x (put S n r q₀)).testBit y = true ↔ x.testBit y = true ∨
      ∃ q, Q q ∧ ∃ b < n, y = q + b * S ∧ r.testBit b = true := by
  rw [testBit_lor, testBit_put]
  simp only [hQ, exists_eq_left]

theorem upd_two {x : ℕ} {S n r q₀ q₁ : ℕ} {Q : ℕ → Prop} (hQ : ∀ q, Q q ↔ q = q₀ ∨ q = q₁)
    (y : ℕ) :
    (Nat.lor x (Nat.lor (put S n r q₀) (put S n r q₁))).testBit y = true ↔ x.testBit y = true ∨
      ∃ q, Q q ∧ ∃ b < n, y = q + b * S ∧ r.testBit b = true := by
  rw [testBit_lor, testBit_lor, testBit_put, testBit_put]
  simp only [hQ, or_and_right, exists_or, exists_eq_left]

@[expose] def QX (k q : ℕ) : Prop := 300 ≤ k ∧ k < 98580 ∧ q = xposT (k - 300)

@[expose] def QA (k q : ℕ) : Prop := (k < 24 ∧ q = 33 * k) ∨
  (24 ≤ k ∧ k < 300 ∧ (q = pairPos k ∨ q = 32 * (pairPos k % 32) + pairPos k / 32))

@[expose] def QW (k q : ℕ) : Prop := 98580 ≤ k ∧ q = 32 * ((k - 98580) / 24) + (k - 98580) % 24

theorem listPl_spec (n : ℕ) (L : List (ℕ × ℤ)) : ∀ lo, (listPl n L lo).1 = true →
    (∀ e ∈ L, lo ≤ e.1 ∧ e.1 < 196884) ∧ L.Pairwise (fun a b => a.1 < b.1) ∧
    PlaneChar n SX QX (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) L (listPl n L lo).2.1 ∧
    PlaneChar n SA QA (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) L (listPl n L lo).2.2.1 ∧
    PlaneChar n SX QW (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) L (listPl n L lo).2.2.2 := by
  induction L with
  | nil =>
    intro lo _
    exact ⟨by simp, List.Pairwise.nil, planeChar_nil _ _ _ _, planeChar_nil _ _ _ _,
      planeChar_nil _ _ _ _⟩
  | cons e L ih =>
    obtain ⟨k, z⟩ := e
    intro lo h
    rw [listPl_cons] at h ⊢
    have IH := ih (k + 1)
    generalize listPl n L (k + 1) = R at IH h ⊢
    obtain ⟨ok, X, A, W⟩ := R
    have hb : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
    have fin : ∀ X' A' W' : ℕ, ok = true → lo ≤ k → k < 196884 →
        (∀ y, X'.testBit y = true ↔ X.testBit y = true ∨ ∃ q, QX k q ∧ ∃ b < n,
          y = q + b * SX ∧ (resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z).testBit b = true) →
        (∀ y, A'.testBit y = true ↔ A.testBit y = true ∨ ∃ q, QA k q ∧ ∃ b < n,
          y = q + b * SA ∧ (resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z).testBit b = true) →
        (∀ y, W'.testBit y = true ↔ W.testBit y = true ∨ ∃ q, QW k q ∧ ∃ b < n,
          y = q + b * SX ∧ (resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z).testBit b = true) →
        (∀ e ∈ (k, z) :: L, lo ≤ e.1 ∧ e.1 < 196884) ∧
          ((k, z) :: L).Pairwise (fun a b => a.1 < b.1) ∧
          PlaneChar n SX QX (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) ((k, z) :: L) X' ∧
          PlaneChar n SA QA (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) ((k, z) :: L) A' ∧
          PlaneChar n SX QW (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) ((k, z) :: L) W' := by
      intro X' A' W' hok hlo hk hX hA hW
      obtain ⟨h1, h2, h3, h4, h5⟩ := IH hok
      refine ⟨?_, List.pairwise_cons.2 ⟨fun e he => (h1 e he).1, h2⟩, planeChar_cons h3 hX,
        planeChar_cons h4 hA, planeChar_cons h5 hW⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact ⟨hlo, hk⟩
      · exact ⟨by have := (h1 e he).1; omega, (h1 e he).2⟩
    rcases Nat.lt_or_ge k 300 with h300 | h300
    · rcases Nat.lt_or_ge k 24 with h24 | h24
      · rw [stepPl_D ok X A W h24] at h ⊢
        dsimp only
        simp only [hb, Bool.and_eq_true, Nat.ble_eq] at h
        refine fin _ _ _ h.1 h.2 (by omega)
          (upd_none (Q := QX k) (fun q hq => by unfold QX at hq; omega))
          (upd_one fun q => by unfold QA; omega)
          (upd_none (Q := QW k) (fun q hq => by unfold QW at hq; omega))
      · rw [stepPl_P ok X A W h24 h300] at h ⊢
        dsimp only
        simp only [hb, Bool.and_eq_true, Nat.ble_eq] at h
        refine fin _ _ _ h.1 h.2 (by omega)
          (upd_none (Q := QX k) (fun q hq => by unfold QX at hq; omega))
          (upd_two fun q => by unfold QA; omega)
          (upd_none (Q := QW k) (fun q hq => by unfold QW at hq; omega))
    · rcases Nat.lt_or_ge k 98580 with h98 | h98
      · rw [stepPl_X ok X A W h300 h98] at h ⊢
        dsimp only
        simp only [hb, Bool.and_eq_true, Nat.ble_eq] at h
        refine fin _ _ _ h.1 h.2 (by omega)
          (upd_one fun q => by unfold QX; omega)
          (upd_none (Q := QA k) (fun q hq => by unfold QA at hq; omega))
          (upd_none (Q := QW k) (fun q hq => by unfold QW at hq; omega))
      · rw [stepPl_W ok X A W h98] at h ⊢
        dsimp only
        simp only [hb, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
        refine fin _ _ _ h.1 h.2.1 h.2.2
          (upd_none (Q := QX k) (fun q hq => by unfold QX at hq; omega))
          (upd_none (Q := QA k) (fun q hq => by unfold QA at hq; omega))
          (upd_one fun q => by unfold QW; omega)

theorem split_pos {S p q b b' : ℕ} (hp : p < S) (hq : q < S) (e : b * S + p = q + b' * S) :
    p = q ∧ b = b' := by
  have hS : 0 < S := by omega
  have e' : p + b * S = q + b' * S := by rw [Nat.add_comm]; exact e
  have h1 := congrArg (· % S) e'
  have h2 := congrArg (· / S) e'
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hq] at h1
  simp only [Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hq,
    Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem pairwise_eq {L : List (ℕ × ℤ)} (h : L.Pairwise (fun a b => a.1 < b.1)) {e e' : ℕ × ℤ}
    (he : e ∈ L) (he' : e' ∈ L) (hk : e.1 = e'.1) : e = e' := by
  induction L with
  | nil => simp at he
  | cons a L ih =>
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 he with h1 | he <;> rcases List.mem_cons.1 he' with h2 | he'
    · rw [h1, h2]
    · have := h.1 _ he'
      rw [h1] at hk
      omega
    · have := h.1 _ he
      rw [h2] at hk
      omega
    · exact ih h.2 he he'

theorem planeChar_read {n S : ℕ} {Q : ℕ → ℕ → Prop} {r : ℤ → ℕ} {L : List (ℕ × ℤ)} {x : ℕ}
    (hc : PlaneChar n S Q r L x) (hQ : ∀ e ∈ L, ∀ q, Q e.1 q → q < S) (hr : ∀ z, r z < 2 ^ n)
    (hpw : L.Pairwise (fun a b => a.1 < b.1)) {p : ℕ} (hp : p < S) :
    (∀ e₀ ∈ L, Q e₀.1 p → (∀ e ∈ L, Q e.1 p → e.1 = e₀.1) →
      ∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2) = r e₀.2) ∧
    ((∀ e ∈ L, ¬ Q e.1 p) → ∑ b ∈ Finset.range n, 2 ^ b * (x / 2 ^ (b * S + p) % 2) = 0) := by
  have key : ∀ b < n, x.testBit (b * S + p) = true ↔
      ∃ e ∈ L, Q e.1 p ∧ (r e.2).testBit b = true := by
    intro b hb
    rw [hc]
    constructor
    · rintro ⟨e, he, q, hq, b', hb', h1, h2⟩
      obtain ⟨e1, e2⟩ := split_pos hp (hQ e he q hq) h1
      subst e1 e2
      exact ⟨e, he, hq, h2⟩
    · rintro ⟨e, he, hq, h2⟩
      exact ⟨e, he, p, hq, b, hb, Nat.add_comm _ _, h2⟩
  refine ⟨fun e₀ he₀ hq₀ huniq => digit_eq (hr _) fun b hb => ?_,
    fun hno => digit_eq (r := 0) (Nat.two_pow_pos n) fun b hb => ?_⟩
  · rw [Bool.eq_iff_iff, key b hb]
    constructor
    · rintro ⟨e, he, hq, h2⟩
      rwa [pairwise_eq hpw he he₀ (huniq e he hq)] at h2
    · exact fun h2 => ⟨e₀, he₀, hq₀, h2⟩
  · rw [Nat.zero_testBit, ← Bool.not_eq_true, key b hb]
    rintro ⟨e, he, hq, -⟩
    exact hno e he hq

theorem planeChar_lt {n S : ℕ} {Q : ℕ → ℕ → Prop} {r : ℤ → ℕ} {L : List (ℕ × ℤ)} {x : ℕ}
    (hc : PlaneChar n S Q r L x) (hQ : ∀ e ∈ L, ∀ q, Q e.1 q → q < S) : x < 2 ^ (n * S) :=
  Nat.lt_pow_two_of_testBit _ fun y hy => by
    rw [← Bool.not_eq_true, hc]
    rintro ⟨e, he, q, hq, b, hb, rfl, -⟩
    have h1 := hQ e he q hq
    have h2 : (b + 1) * S ≤ n * S := Nat.mul_le_mul_right S hb
    rw [Nat.succ_mul] at h2
    omega

theorem foldl_getD (L : List (ℕ × ℤ)) : ∀ (D : Array ℤ), D.size = 196884 → ∀ k < 196884,
    (L.foldl (fun D t => if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D) D)[k]?.getD 0
      = D[k]?.getD 0 + (L.map fun t => if t.1 = k then t.2 else 0).sum := by
  induction L with
  | nil =>
    intro D _ k _
    simp
  | cons t L ih =>
    intro D hD k hk
    rw [List.foldl_cons, List.map_cons, List.sum_cons]
    have hD' : (if t.1 < 196884 then D.modify t.1 (fun y => y + t.2) else D).size = 196884 := by
      split_ifs <;> simp [hD]
    rw [ih _ hD' k hk]
    have hget : D[k]? = some (D[k]?.getD 0) := by
      rw [Array.getElem?_eq_getElem (by omega)]
      rfl
    by_cases h1 : t.1 < 196884
    · rw [ite_eq_left h1, Array.getElem?_modify]
      by_cases h2 : t.1 = k
      · rw [ite_eq_left h2, ite_eq_left h2, hget]
        simp only [Option.map_some, Option.getD_some]
        omega
      · rw [ite_eq_right h2, ite_eq_right h2]
        omega
    · have h2 : ¬ t.1 = k := by omega
      rw [ite_eq_right h1, ite_eq_right h2]
      omega

theorem sum_key_none {L : List (ℕ × ℤ)} {k : ℕ} (h : ∀ e ∈ L, e.1 ≠ k) :
    (L.map fun t => if t.1 = k then t.2 else 0).sum = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.map_cons, List.sum_cons, ite_eq_right (h a List.mem_cons_self),
      ih fun e he => h e (List.mem_cons_of_mem _ he), Int.zero_add]

theorem sum_key_mem {L : List (ℕ × ℤ)} (hpw : L.Pairwise (fun a b => a.1 < b.1)) {k : ℕ} {z : ℤ}
    (h : (k, z) ∈ L) : (L.map fun t => if t.1 = k then t.2 else 0).sum = z := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [ite_eq_left rfl, sum_key_none fun e he => by have := hpw.1 e he; simp at this ⊢; omega,
        Int.add_zero]
    · have := hpw.1 _ h
      rw [ite_eq_right (by simp at this ⊢; omega), ih hpw.2 h, Int.zero_add]

theorem resN_ofList (n : ℕ) (L : List (ℕ × ℤ)) {k : ℕ} (hk : k < 196884) :
    resN n (Native.DVec.ofList L) k =
      (((L.map fun t => if t.1 = k then t.2 else 0).sum : ℤ) : ZMod (2 ^ n - 1)) := by
  unfold resN Native.DVec.ofList Native.DVec.ofListE
  simp only [Array.getD_eq_getD_getElem?, pow_zero, mul_one]
  rw [foldl_getD L _ (by simp) k hk, Array.getElem?_replicate, ite_eq_left hk]
  simp

theorem resMI_lt {M : ℕ} (hM : 0 < M) (z : ℤ) : resMI M z < M := by
  cases z with
  | ofNat a => exact Nat.mod_lt _ hM
  | negSucc a => exact Nat.mod_lt _ hM

theorem resMI_cast {M : ℕ} (hM : 0 < M) (z : ℤ) : (resMI M z : ZMod M) = (z : ZMod M) := by
  cases z with
  | ofNat a =>
    change ((a % M : ℕ) : ZMod M) = _
    rw [ZMod.natCast_mod]
    simp
  | negSucc a =>
    change (((M - (a + 1) % M) % M : ℕ) : ZMod M) = _
    have hl : (a + 1) % M ≤ M := (Nat.mod_lt _ hM).le
    rw [ZMod.natCast_mod, Nat.cast_sub hl, ZMod.natCast_mod, ZMod.natCast_self, zero_sub,
      Int.cast_negSucc]

theorem M_eq (n : ℕ) : Nat.sub (Nat.shiftLeft 1 n) 1 = 2 ^ n - 1 := by
  change 1 <<< n - 1 = _
  rw [Nat.one_shiftLeft]

theorem rep_read {n S : ℕ} (hn : 2 ≤ n) {Q : ℕ → ℕ → Prop} {L : List (ℕ × ℤ)} {x p k₀ : ℕ}
    (hc : PlaneChar n S Q (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) L x)
    (hQ : ∀ e ∈ L, ∀ q, Q e.1 q → q < S) (hpw : L.Pairwise (fun a b => a.1 < b.1)) (hp : p < S)
    (hk₀ : k₀ < 196884) (hQk : ∀ k, Q k p ↔ k = k₀) :
    resPN n S x p = resN n (Native.DVec.ofList L) k₀ := by
  have hM := M_eq n
  have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hMpos : 0 < Nat.sub (Nat.shiftLeft 1 n) 1 := by
    rw [hM]
    change 4 ≤ 2 ^ n at h2
    omega
  have hr : ∀ z, resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z < 2 ^ n := fun z =>
    lt_of_lt_of_le (resMI_lt hMpos z) (by rw [hM]; omega)
  have hR := planeChar_read hc hQ hr hpw hp
  rw [resN_ofList n L hk₀]
  unfold resPN
  by_cases hex : ∃ z, (k₀, z) ∈ L
  · obtain ⟨z, hz⟩ := hex
    rw [hR.1 (k₀, z) hz ((hQk k₀).2 rfl) fun e _ he => (hQk e.1).1 he, sum_key_mem hpw hz]
    have hc' := resMI_cast hMpos z
    rw [hM] at hc' ⊢
    exact hc'
  · have hno : ∀ e ∈ L, e.1 ≠ k₀ := fun e he h => hex ⟨e.2, by rw [← h]; exact he⟩
    rw [hR.2 fun e he hq => hno e he ((hQk e.1).1 hq), sum_key_none hno]
    simp

theorem rep_zero {n S : ℕ} (hn : 2 ≤ n) {Q : ℕ → ℕ → Prop} {L : List (ℕ × ℤ)} {x p : ℕ}
    (hc : PlaneChar n S Q (resMI (Nat.sub (Nat.shiftLeft 1 n) 1)) L x)
    (hQ : ∀ e ∈ L, ∀ q, Q e.1 q → q < S) (hpw : L.Pairwise (fun a b => a.1 < b.1)) (hp : p < S)
    (hno : ∀ k, ¬ Q k p) : resPN n S x p = 0 := by
  have hM := M_eq n
  have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hMpos : 0 < Nat.sub (Nat.shiftLeft 1 n) 1 := by
    rw [hM]
    change 4 ≤ 2 ^ n at h2
    omega
  have hr : ∀ z, resMI (Nat.sub (Nat.shiftLeft 1 n) 1) z < 2 ^ n := fun z =>
    lt_of_lt_of_le (resMI_lt hMpos z) (by rw [hM]; omega)
  unfold resPN
  rw [(planeChar_read hc hQ hr hpw hp).2 fun e _ hq => hno e.1 hq]
  simp

theorem xposT_small : ∀ q < 552, xposT q = xposK q := by decide +kernel

theorem xposT_eq (q : ℕ) : xposT q = xposK q := by
  rcases Nat.lt_or_ge q 552 with h1 | h1
  · exact xposT_small q h1
  · have e1 : Nat.blt q (nat_lit 552) = false := blt_f (b := 552) h1
    unfold xposT xposK
    rw [e1, ite_eq_right (Nat.not_lt.2 h1)]
    rcases Nat.lt_or_ge q 49704 with h2 | h2
    · have e2 : Nat.blt q (nat_lit 49704) = true := blt_t (b := 49704) h2
      rw [e2, ite_eq_left h2]
      rfl
    · have e2 : Nat.blt q (nat_lit 49704) = false := blt_f (b := 49704) h2
      rw [e2, ite_eq_right (Nat.not_lt.2 h2)]
      rfl

theorem pairPos_spec : ∀ k < 300, 24 ≤ k → pairPos k / 32 < pairPos k % 32 ∧
    pairPos k % 32 < 24 ∧ Native.aIdx (pairPos k / 32) (pairPos k % 32) = k := by
  decide +kernel

theorem aPos_aIdx : ∀ i < 24, ∀ j < 24, Native.aPos (Native.aIdx i j) = (min i j, max i j) := by
  decide +kernel

theorem aIdx_comm : ∀ i < 24, ∀ j < 24, Native.aIdx i j = Native.aIdx j i := by decide +kernel

theorem aIdx_ge {i j : ℕ} (h : i ≠ j) : 24 ≤ Native.aIdx i j := by
  unfold Native.aIdx
  rw [ite_eq_right h]
  omega

theorem diag_bound : ∀ k < 24, 33 * k < 1024 ∧ 33 * k % 32 < 24 ∧ 33 * k / 32 < 24 := by
  decide

theorem tr_bound {a c : ℕ} (h1 : a < c) (h2 : c < 24) :
    32 * c + a < 1024 ∧ (32 * c + a) % 32 < 24 ∧ (32 * c + a) / 32 < 24 := by
  omega

theorem QA_bound {k q : ℕ} (h : QA k q) : q < 1024 ∧ q % 32 < 24 ∧ q / 32 < 24 := by
  rcases h with ⟨h1, rfl⟩ | ⟨h1, h2, h3 | h3⟩
  · exact diag_bound k h1
  · have := pairPos_spec k h2 h1
    omega
  · obtain ⟨s1, s2, -⟩ := pairPos_spec k h2 h1
    rw [h3]
    exact tr_bound s1 s2

theorem QA_iff {i j : ℕ} (hi : i < 24) (hj : j < 24) (k : ℕ) :
    QA k (32 * i + j) ↔ k = Native.aIdx i j := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3 | h3⟩)
    · obtain ⟨rfl, rfl⟩ : i = k ∧ j = k := by omega
      simp [Native.aIdx]
    · obtain ⟨s1, s2, s3⟩ := pairPos_spec k h2 h1
      have ei : i = pairPos k / 32 := by omega
      have ej : j = pairPos k % 32 := by omega
      rw [ei, ej, s3]
    · obtain ⟨s1, s2, s3⟩ := pairPos_spec k h2 h1
      have ei : i = pairPos k % 32 := by omega
      have ej : j = pairPos k / 32 := by omega
      rw [ei, ej, aIdx_comm _ s2 _ (by omega), s3]
  · rintro rfl
    by_cases hij : i = j
    · subst hij
      left
      have e : Native.aIdx i i = i := by simp [Native.aIdx]
      rw [e]
      omega
    · have hk := aIdx_ge hij
      have hk' := aIdx_lt i hi j hj
      right
      refine ⟨hk, hk', ?_⟩
      obtain ⟨s1, s2, s3⟩ := pairPos_spec _ hk' hk
      have p1 := aPos_aIdx i hi j hj
      have p2 := aPos_aIdx (pairPos (Native.aIdx i j) / 32) (by omega)
        (pairPos (Native.aIdx i j) % 32) s2
      rw [s3, p1, Prod.mk.injEq, min_eq_left s1.le, max_eq_right s1.le] at p2
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · rw [min_eq_left h.le, max_eq_right h.le] at p2
        left
        omega
      · rw [min_eq_right h.le, max_eq_left h.le] at p2
        right
        omega

end ListAux

open ListAux CFSG.KC.KDense.InitAux in
theorem listInit_sound {n : ℕ} (hn : 2 ≤ n) (L : List (ℕ × ℤ)) (s : St)
    (h : listInitOK n L s = true) : RepN n (Native.DVec.ofList L) s := by
  obtain ⟨f, X', A', W'⟩ := s
  have hspec := listPl_spec n L 0
  unfold listInitOK at h
  generalize listPl n L 0 = R at h hspec
  obtain ⟨ok, X, A, W⟩ := R
  change andB ok (andB f (andB (Nat.beq X X') (andB (Nat.beq A A') (Nat.beq W W')))) = true at h
  have hb : ∀ a b : Bool, andB a b = (a && b) := fun a b => by cases a <;> rfl
  simp only [hb, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hok, -, rfl, rfl, rfl⟩ := h
  obtain ⟨hbd, hpw, hcX, hcA, hcW⟩ := hspec hok
  have hQX : ∀ e ∈ L, ∀ q, QX e.1 q → q < SX := fun e _ q ⟨h1, h2, h3⟩ => by
    rw [h3, xposT_eq]
    exact xposK_lt' (by omega)
  have hQA : ∀ e ∈ L, ∀ q, QA e.1 q → q < SA := fun e _ q hq => (QA_bound hq).1
  have hQW : ∀ e ∈ L, ∀ q, QW e.1 q → q < SX := fun e he q ⟨h1, h2⟩ => by
    have := (hbd e he).2
    change q < 131072
    omega
  have SXe : SX = 131072 := rfl
  have SAe : SA = 1024 := rfl
  refine ⟨fun q hq => ?_, fun p hp hq => ?_, planeChar_lt hcX hQX, fun i hi j hj => ?_,
    fun p hp hq => ?_, planeChar_lt hcA hQA, fun r hr j hj => ?_, fun p hp hq => ?_,
    planeChar_lt hcW hQW⟩
  · refine rep_read hn hcX hQX hpw (xposK_lt' hq) (by omega) fun k => ⟨fun ⟨h1, h2, h3⟩ => ?_, ?_⟩
    · rw [xposT_eq] at h3
      have := xposK_inj hq (by omega) h3
      omega
    · rintro rfl
      exact ⟨by omega, by omega, by rw [Nat.add_sub_cancel_left, xposT_eq]⟩
  · refine rep_zero hn hcX hQX hpw hp fun k ⟨h1, h2, h3⟩ => hq (k - 300) (by omega) ?_
    rw [h3, xposT_eq]
  · exact rep_read hn hcA hQA hpw (by rw [SAe]; omega)
      (by have := aIdx_lt i hi j hj; omega) (QA_iff hi hj)
  · exact rep_zero hn hcA hQA hpw hp fun k hk => by
      have := QA_bound hk
      omega
  · refine rep_read hn hcW hQW hpw (by rw [SXe]; omega) (by omega) fun k => ?_
    unfold QW
    omega
  · exact rep_zero hn hcW hQW hpw hp fun k hk => by
      unfold QW at hk
      omega

end CFSG.KC.KDenseP

end
