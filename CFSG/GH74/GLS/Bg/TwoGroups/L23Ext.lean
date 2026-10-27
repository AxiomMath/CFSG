module

public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L23

abbrev Vec : Type := ZMod 4 × ZMod 4

@[expose] def pw {G : Type} [Group G] (g : G) (b : Bool) : G := if b then g else 1

structure ExtData (P Q : Vec →+ Vec) (G : Type) [Group G] where
  emb : Vec → G
  emb_add : ∀ v w, emb (v + w) = emb v * emb w
  emb_inj : Function.Injective emb
  p : G
  q : G
  α : Vec
  β : Vec
  γ : Vec
  hp : ∀ v, p * emb v = emb (P v) * p
  hq : ∀ v, q * emb v = emb (Q v) * q
  hpp : p * p = emb α
  hqq : q * q = emb β
  hqp : q * p = p * q * emb γ

variable {P Q : Vec →+ Vec} {G : Type} [Group G] (D : ExtData P Q G)

namespace ExtData

@[expose] def nf (u : Vec × Bool × Bool) : G := D.emb u.1 * pw D.p u.2.1 * pw D.q u.2.2

end ExtData

@[expose] def Mop (P Q : Vec →+ Vec) (i j : Bool) (w : Vec) : Vec :=
  (if i then P else AddMonoidHom.id _) ((if j then Q else AddMonoidHom.id _) w)

@[expose] def rA (P Q : Vec →+ Vec) (u : Vec × Bool × Bool) (w : Vec) : Vec × Bool × Bool :=
  (u.1 + Mop P Q u.2.1 u.2.2 w, u.2.1, u.2.2)

@[expose] def rP (P Q : Vec →+ Vec) (α γ : Vec) (u : Vec × Bool × Bool) : Vec × Bool × Bool :=
  match u with
  | (v, false, false) => (v, true, false)
  | (v, true, false) => (v + α, false, false)
  | (v, false, true) => (v + P (Q γ), true, true)
  | (v, true, true) => (v + α + Q γ, false, true)

@[expose] def rQ (P : Vec →+ Vec) (β : Vec) (u : Vec × Bool × Bool) : Vec × Bool × Bool :=
  match u with
  | (v, false, false) => (v, false, true)
  | (v, true, false) => (v, true, true)
  | (v, false, true) => (v + β, false, false)
  | (v, true, true) => (v + P β, true, false)

@[expose] def mulC (P Q : Vec →+ Vec) (α β γ : Vec) (u u' : Vec × Bool × Bool) :
    Vec × Bool × Bool :=
  let r1 := rA P Q u u'.1
  let r2 := if u'.2.1 then rP P Q α γ r1 else r1
  if u'.2.2 then rQ P β r2 else r2

namespace ExtData

theorem nf_rA (u : Vec × Bool × Bool) (w : Vec) : D.nf u * D.emb w = D.nf (rA P Q u w) := by
  obtain ⟨v, i, j⟩ := u
  cases i <;> cases j
  · simp [nf, rA, Mop, pw, D.emb_add]
  · simp [nf, rA, Mop, pw, D.emb_add]
    rw [mul_assoc, D.hq, mul_assoc]
  · simp [nf, rA, Mop, pw, D.emb_add]
    rw [mul_assoc, D.hp, mul_assoc]
  · show D.emb v * D.p * D.q * D.emb w = D.emb (v + P (Q w)) * D.p * D.q
    calc D.emb v * D.p * D.q * D.emb w = D.emb v * D.p * (D.q * D.emb w) := by
          simp only [mul_assoc]
      _ = D.emb v * D.p * (D.emb (Q w) * D.q) := by rw [D.hq]
      _ = D.emb v * (D.p * D.emb (Q w)) * D.q := by simp only [mul_assoc]
      _ = D.emb v * (D.emb (P (Q w)) * D.p) * D.q := by rw [D.hp]
      _ = D.emb (v + P (Q w)) * D.p * D.q := by rw [D.emb_add]; simp only [mul_assoc]

theorem nf_rP (u : Vec × Bool × Bool) : D.nf u * D.p = D.nf (rP P Q D.α D.γ u) := by
  obtain ⟨v, i, j⟩ := u
  cases i <;> cases j
  · simp [nf, rP, pw]
  · simp only [nf, rP, pw, ite_true, ite_false, Bool.false_eq_true, mul_one]
    calc D.emb v * D.q * D.p = D.emb v * (D.q * D.p) := by rw [mul_assoc]
      _ = D.emb v * (D.p * D.q * D.emb D.γ) := by rw [D.hqp]
      _ = D.emb v * (D.p * (D.emb (Q D.γ) * D.q)) := by rw [mul_assoc, D.hq]
      _ = D.emb v * (D.emb (P (Q D.γ)) * D.p * D.q) := by rw [← mul_assoc D.p, D.hp, mul_assoc]
      _ = D.emb (v + P (Q D.γ)) * D.p * D.q := by rw [← mul_assoc, ← mul_assoc, ← D.emb_add]
  · simp only [nf, rP, pw, ite_true, ite_false, Bool.false_eq_true, mul_one]
    rw [mul_assoc, D.hpp, ← D.emb_add]
  · simp only [nf, rP, pw, ite_true, ite_false, Bool.false_eq_true, mul_one]
    calc D.emb v * D.p * D.q * D.p = D.emb v * D.p * (D.q * D.p) := by rw [mul_assoc _ D.q]
      _ = D.emb v * D.p * (D.p * D.q * D.emb D.γ) := by rw [D.hqp]
      _ = D.emb v * (D.p * D.p) * (D.q * D.emb D.γ) := by simp only [mul_assoc]
      _ = D.emb v * D.emb D.α * (D.emb (Q D.γ) * D.q) := by rw [D.hpp, D.hq]
      _ = D.emb (v + D.α + Q D.γ) * D.q := by
        rw [D.emb_add, D.emb_add, mul_assoc, mul_assoc, mul_assoc]

theorem nf_rQ (u : Vec × Bool × Bool) : D.nf u * D.q = D.nf (rQ P D.β u) := by
  obtain ⟨v, i, j⟩ := u
  cases i <;> cases j
  · simp [nf, rQ, pw]
  · simp only [nf, rQ, pw, ite_true, ite_false, Bool.false_eq_true, mul_one]
    rw [mul_assoc, D.hqq, ← D.emb_add]
  · simp [nf, rQ, pw]
  · simp only [nf, rQ, pw, ite_true, ite_false, Bool.false_eq_true, mul_one]
    calc D.emb v * D.p * D.q * D.q = D.emb v * D.p * (D.q * D.q) := by rw [mul_assoc _ D.q]
      _ = D.emb v * D.p * D.emb D.β := by rw [D.hqq]
      _ = D.emb v * (D.emb (P D.β) * D.p) := by rw [mul_assoc, D.hp]
      _ = D.emb (v + P D.β) * D.p := by rw [← mul_assoc, ← D.emb_add]

theorem nf_mul (u u' : Vec × Bool × Bool) :
    D.nf u * D.nf u' = D.nf (mulC P Q D.α D.β D.γ u u') := by
  obtain ⟨v', i', j'⟩ := u'
  have h1 : D.nf u * D.nf (v', i', j') = ((D.nf u * D.emb v') * pw D.p i') * pw D.q j' := by
    simp only [nf, mul_assoc]
  rw [h1, nf_rA]
  cases i' <;> cases j' <;> simp [mulC, pw, nf_rP, nf_rQ]

theorem nf_conj (u : Vec × Bool × Bool) (w : Vec) :
    D.nf u * D.emb w = D.emb (Mop P Q u.2.1 u.2.2 w) * D.nf u := by
  rw [nf_rA]
  obtain ⟨v, i, j⟩ := u
  simp only [rA, nf]
  rw [add_comm, D.emb_add]
  simp only [mul_assoc]

theorem nf_injective
    (hdist : ∀ i j i' j' : Bool, (∀ w, Mop P Q i j w = Mop P Q i' j' w) → i = i' ∧ j = j') :
    Function.Injective D.nf := by
  rintro ⟨v, i, j⟩ ⟨v', i', j'⟩ h
  have hM : ∀ w, Mop P Q i j w = Mop P Q i' j' w := by
    intro w
    have h1 := nf_conj D (v, i, j) w
    have h2 := nf_conj D (v', i', j') w
    rw [h] at h1
    have h3 : D.emb (Mop P Q i j w) * D.nf (v', i', j') =
        D.emb (Mop P Q i' j' w) * D.nf (v', i', j') := by
      rw [← h1, h2]
    exact D.emb_inj (mul_right_cancel h3)
  obtain ⟨rfl, rfl⟩ := hdist i j i' j' hM
  have h4 : D.emb v * (pw D.p i * pw D.q j) = D.emb v' * (pw D.p i * pw D.q j) := by
    simpa only [nf, mul_assoc] using h
  have := D.emb_inj (mul_right_cancel h4)
  rw [this]

theorem card_coords : Nat.card (Vec × Bool × Bool) = 64 := by
  simp

theorem nf_bijective [Finite G] (hG : Nat.card G = 64)
    (hdist : ∀ i j i' j' : Bool, (∀ w, Mop P Q i j w = Mop P Q i' j' w) → i = i' ∧ j = j') :
    Function.Bijective D.nf :=
  (nf_injective D hdist).bijective_of_nat_card_le (by rw [hG, card_coords])

end ExtData

theorem ext_equiv {G' : Type} [Group G'] [Finite G] [Finite G'] (hG : Nat.card G = 64)
    (hG' : Nat.card G' = 64) (D' : ExtData P Q G')
    (hdist : ∀ i j i' j' : Bool, (∀ w, Mop P Q i j w = Mop P Q i' j' w) → i = i' ∧ j = j')
    (hα : D.α = D'.α) (hβ : D.β = D'.β) (hγ : D.γ = D'.γ) : Nonempty (G ≃* G') := by
  let e := Equiv.ofBijective D.nf (D.nf_bijective hG hdist)
  let e' := Equiv.ofBijective D'.nf (D'.nf_bijective hG' hdist)
  refine ⟨{ e.symm.trans e' with map_mul' := ?_ }⟩
  intro g h
  obtain ⟨u, rfl⟩ := e.surjective g
  obtain ⟨u', rfl⟩ := e.surjective h
  have h1 : D.nf u * D.nf u' = D.nf (mulC P Q D.α D.β D.γ u u') := D.nf_mul u u'
  have h2 : D'.nf u * D'.nf u' = D'.nf (mulC P Q D.α D.β D.γ u u') := by
    rw [D'.nf_mul, hα, hβ, hγ]
  show e' (e.symm (D.nf u * D.nf u')) = e' (e.symm (D.nf u)) * e' (e.symm (D.nf u'))
  have h3 : ∀ w, e.symm (D.nf w) = w := fun w => e.symm_apply_apply w
  rw [h1, h3, h3, h3]
  exact h2.symm

end L23

end CFSG.GH74.GLS.Bg.TwoGroups
