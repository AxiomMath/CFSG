module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf28Aut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out

open QuaternionGroup

@[expose] def q8Ev (p q : Q8) : Q8 → Q8
  | QuaternionGroup.a n => p ^ n.val
  | QuaternionGroup.xa n => q * p ^ n.val

@[expose] def q8ConjEv (p q g z : Q8) : Q8 := q8Ev p q (g * z * g⁻¹)

theorem q8Ev_gen : ∀ p q : Q8, p * p = a 2 → q * q = a 2 → q * p = p⁻¹ * q →
    ∀ i : Fin 4, ∀ j : Fin 2,
    q8Ev p q ((a 1 : Q8) ^ (i : ℕ) * (xa 0 : Q8) ^ (j : ℕ)) = p ^ (i : ℕ) * q ^ (j : ℕ) := by
  decide +kernel

theorem q8_finite : ∀ p q g : Q8, p * p = a 2 → q * q = a 2 → q * p = p⁻¹ * q →
    (∀ z, q8Ev p q (q8Ev p q (q8Ev p q (q8Ev p q z))) = z) →
    (∃ z, q8Ev p q (q8Ev p q z) ≠ z) →
    (∃ z, q8ConjEv p q g (q8ConjEv p q g z) ≠ z) →
    ∀ z, q8Ev p q (q8Ev p q z) = q8ConjEv p q g (q8ConjEv p q g z) := by
  decide +kernel

theorem q8_a2_sq : (a 2 : Q8) * a 2 = 1 := by decide

theorem q8_a1_sq : (a 1 : Q8) * a 1 = a 2 := by decide

theorem q8_xa0_sq : (xa 0 : Q8) * xa 0 = a 2 := by decide

theorem q8_xa0_a1 : (xa 0 : Q8) * a 1 = (a 1 : Q8)⁻¹ * xa 0 := by decide

theorem q8_eq_a2_of_invol : ∀ z : Q8, z * z = 1 → z ≠ 1 → z = a 2 := by
  decide +kernel

theorem q8_map_a2 (α : MulAut Q8) : α (a 2) = a 2 := by
  have hsq : α (a 2) * α (a 2) = 1 := by
    rw [← map_mul, q8_a2_sq, map_one]
  have hne : α (a 2) ≠ 1 := by
    intro h0
    apply a2_ne_one
    apply α.injective
    rw [h0, map_one]
  exact q8_eq_a2_of_invol _ hsq hne

theorem q8_core_aux (α : MulAut Q8) (g p q : Q8) (β : Q8 → Q8)
    (hα : ∀ z, α z = q8Ev p q z) (hp : p * p = a 2) (hq : q * q = a 2)
    (hqp : q * p = p⁻¹ * q) (hβ : ∀ z, β z = α (g * z * g⁻¹))
    (h4 : ∀ z, α (α (α (α z))) = z) (h2 : ∃ z, α (α z) ≠ z)
    (h2' : ∃ z, β (β z) ≠ z) : ∀ z, α (α z) = β (β z) := by
  have hβ' : ∀ z, β z = q8ConjEv p q g z := fun z => (hβ z).trans (hα _)
  simp only [hα] at h4 h2 ⊢
  simp only [hβ'] at h2' ⊢
  exact q8_finite p q g hp hq hqp h4 h2 h2'

theorem q8_core (α : MulAut Q8) (g : Q8) (β : Q8 → Q8)
    (hβ : ∀ z, β z = α (g * z * g⁻¹))
    (h4 : ∀ z, α (α (α (α z))) = z) (h2 : ∃ z, α (α z) ≠ z)
    (h2' : ∃ z, β (β z) ≠ z) : ∀ z, α (α z) = β (β z) := by
  have ha2 : α (a 2) = a 2 := q8_map_a2 α
  have hp : α (a 1) * α (a 1) = a 2 := by
    rw [← map_mul, q8_a1_sq, ha2]
  have hq : α (xa 0) * α (xa 0) = a 2 := by
    rw [← map_mul, q8_xa0_sq, ha2]
  have hqp : α (xa 0) * α (a 1) = (α (a 1))⁻¹ * α (xa 0) := by
    rw [← map_inv, ← map_mul, ← map_mul, q8_xa0_a1]
  have hα : ∀ z, α z = q8Ev (α (a 1)) (α (xa 0)) z := by
    intro z
    obtain ⟨i, j, rfl⟩ := q8_gen z
    rw [q8Ev_gen _ _ hp hq hqp, map_mul, map_pow, map_pow]
  exact q8_core_aux α g _ _ β hα hp hq hqp hβ h4 h2 h2'

@[expose] def q8Transport {A : Type} [Group A] (e : A ≃* Q8) (α : MulAut A) : MulAut Q8 :=
  e.symm.trans (α.trans e)

theorem q8Transport_apply {A : Type} [Group A] (e : A ≃* Q8) (α : MulAut A) (z : Q8) :
    q8Transport e α z = e (α (e.symm z)) :=
  rfl

theorem mulAut_pow_two_apply {A : Type} [Group A] (α : MulAut A) (y : A) :
    (α ^ 2) y = α (α y) := by
  rw [pow_two, MulAut.mul_apply]

theorem mulAut_pow_four_apply {A : Type} [Group A] (α : MulAut A) (y : A) :
    (α ^ 4) y = α (α (α (α y))) := by
  simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]

theorem exists_ne_of_sq_ne_one {A : Type} [Group A] (e : A ≃* Q8) (α : MulAut A)
    (h : α ^ 2 ≠ 1) : ∃ z, q8Transport e α (q8Transport e α z) ≠ z := by
  by_contra hcon
  push_neg at hcon
  apply h
  refine MulEquiv.ext fun y => ?_
  rw [mulAut_pow_two_apply]
  apply e.injective
  have := hcon (e y)
  simpa [q8Transport_apply] using this

theorem sq_eq_of_act_eq_of_equiv {A : Type} [Group A] (e : A ≃* Q8) (α β : MulAut A)
    (hact : Idx2.act α = Idx2.act β) (h4 : α ^ 4 = 1) (h2 : α ^ 2 ≠ 1) (h2' : β ^ 2 ≠ 1) :
    α ^ 2 = β ^ 2 := by
  have hinv : Idx2.act (α⁻¹ * β) = 1 := by
    rw [map_mul, map_inv, ← hact, inv_mul_cancel]
  obtain ⟨g, hg⟩ := exists_inner_of_act_eq_one_of_equiv e (α⁻¹ * β) hinv
  have hβ : ∀ y, β y = α (g * y * g⁻¹) := by
    intro y
    rw [← hg y, MulAut.mul_apply, MulAut.apply_inv_self]
  have hβ' : ∀ z, q8Transport e β z = q8Transport e α (e g * z * (e g)⁻¹) := by
    intro z
    simp only [q8Transport_apply, hβ, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hα4 : ∀ y, α (α (α (α y))) = y := fun y => by
    have h := mulAut_pow_four_apply α y
    rw [h4] at h
    exact h.symm
  have h4' : ∀ z, q8Transport e α (q8Transport e α (q8Transport e α (q8Transport e α z)))
      = z := by
    intro z
    simp only [q8Transport_apply, MulEquiv.symm_apply_apply, hα4, MulEquiv.apply_symm_apply]
  have key := q8_core (q8Transport e α) (e g) (q8Transport e β) hβ' h4'
    (exists_ne_of_sq_ne_one e α h2) (exists_ne_of_sq_ne_one e β h2')
  refine MulEquiv.ext fun y => ?_
  rw [mulAut_pow_two_apply, mulAut_pow_two_apply]
  apply e.injective
  have := key (e y)
  simpa [q8Transport_apply] using this

theorem fin3Perm_dihedral : ∀ p q : Equiv.Perm (Fin 3), p * p = 1 → p ≠ 1 → q * q = 1 →
    q ≠ 1 → (q * p) * q * (q * p)⁻¹ = p := by
  decide +kernel

theorem fin3Perm_sq_of_pow_four : ∀ x : Equiv.Perm (Fin 3), x ^ 4 = 1 → x * x = 1 := by
  decide +kernel

noncomputable def idx2EquivFin3 {A : Type} [Group A] (hc : Nat.card (Idx2 A) = 3) :
    Idx2 A ≃ Fin 3 :=
  haveI : Finite (Idx2 A) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  Finite.equivFinOfCardEq hc

theorem dihedral_idx2 {A : Type} [Group A] (hc : Nat.card (Idx2 A) = 3)
    (p q : Equiv.Perm (Idx2 A)) (hp : p * p = 1) (hp1 : p ≠ 1) (hq : q * q = 1) (hq1 : q ≠ 1) :
    (q * p) * q * (q * p)⁻¹ = p := by
  let φ := (idx2EquivFin3 hc).permCongrHom
  have hp' : φ p * φ p = 1 := by rw [← map_mul, hp, map_one]
  have hq' : φ q * φ q = 1 := by rw [← map_mul, hq, map_one]
  have hp1' : φ p ≠ 1 := fun h => hp1 (φ.injective (h.trans (map_one φ).symm))
  have hq1' : φ q ≠ 1 := fun h => hq1 (φ.injective (h.trans (map_one φ).symm))
  apply φ.injective
  simp only [map_mul, map_inv]
  exact fin3Perm_dihedral (φ p) (φ q) hp' hp1' hq' hq1'

theorem pow_four_sq_eq_one {A : Type} [Group A] (hc : Nat.card (Idx2 A) = 3)
    (σ : Equiv.Perm (Idx2 A)) (h : σ ^ 4 = 1) : σ * σ = 1 := by
  let φ := (idx2EquivFin3 hc).permCongrHom
  apply φ.injective
  rw [map_mul, map_one]
  apply fin3Perm_sq_of_pow_four
  rw [← map_pow, h, map_one]

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Out
