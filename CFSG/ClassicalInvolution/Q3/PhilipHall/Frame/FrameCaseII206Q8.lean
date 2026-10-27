module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf28Aut

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

namespace Out

open QuaternionGroup

@[expose] def q8i : Q8 → ℕ
  | a i => i.val
  | xa i => (-i).val

@[expose] def q8j : Q8 → ℕ
  | a _ => 0
  | xa _ => 1

theorem q8_normal_form : ∀ y : Q8, y = a 1 ^ q8i y * xa 0 ^ q8j y := by decide

theorem q8_inv_aut_core : ∀ p q w : Q8, w * w ≠ 1 → p * p ≠ 1 → q * q ≠ 1 → p * q ≠ q * p →
    p ^ q8i w * q ^ q8j w = w → p ^ q8i p * q ^ q8j p = a 1 → p ^ q8i q * q ^ q8j q = xa 0 →
    ∃ g : Q8, p = g * a 1 * g⁻¹ ∧ q = g * xa 0 * g⁻¹ := by decide +kernel

theorem q8_comm_order_four : ∀ r : Q8, ∃ w : Q8, w * w ≠ 1 ∧ w * r = r * w := by decide

theorem q8_eq_or_eq_inv_of_comm :
    ∀ p q : Q8, p * p ≠ 1 → q * q ≠ 1 → p * q = q * p → q = p ∨ q = p⁻¹ := by decide

theorem q8_mul_central :
    ∀ p c : Q8, p * p ≠ 1 → (c = 1 ∨ c = a 2) → p * c = p ∨ p * c = p⁻¹ := by decide

theorem q8_pow_four : ∀ p : Q8, p * p ≠ 1 → p ^ 4 = 1 ∧ ¬ p ^ 2 = 1 := by decide

theorem perm3_eq_of_fixed : ∀ σ : Equiv.Perm (Fin 3), σ * σ = 1 → σ ≠ 1 → ∀ i j : Fin 3,
    σ i = i → σ j = j → i = j := by decide

theorem q8_aut_inner_of_invol (α : MulAut Q8) (h2 : ∀ y, α (α y) = y) {w : Q8} (hw : w * w ≠ 1)
    (hαw : α w = w) : ∃ g : Q8, ∀ y, α y = g * y * g⁻¹ := by
  set p := α (a 1) with hp
  set q := α (xa 0) with hq
  have hev : ∀ y, α y = p ^ q8i y * q ^ q8j y := by
    intro y
    calc α y = α (a 1 ^ q8i y * xa 0 ^ q8j y) := congrArg α (q8_normal_form y)
      _ = p ^ q8i y * q ^ q8j y := by rw [map_mul, map_pow, map_pow]
  have h2ne : α (a 2) ≠ 1 := fun h0 => a2_ne_one (α.injective (h0.trans (map_one α).symm))
  have hp2 : p * p ≠ 1 := by
    rw [hp, ← map_mul, show (a 1 : Q8) * a 1 = a 2 by decide]
    exact h2ne
  have hq2 : q * q ≠ 1 := by
    rw [hq, ← map_mul, show (xa 0 : Q8) * xa 0 = a 2 by decide]
    exact h2ne
  have hpq : p * q ≠ q * p := by
    intro h
    apply (show (a 1 : Q8) * xa 0 ≠ xa 0 * a 1 by decide)
    apply α.injective
    rw [map_mul, map_mul]
    exact h
  obtain ⟨g, hg1, hg2⟩ := q8_inv_aut_core p q w hw hp2 hq2 hpq ((hev w).symm.trans hαw)
    ((hev p).symm.trans (h2 _)) ((hev q).symm.trans (h2 _))
  refine ⟨g, fun y => ?_⟩
  calc α y = p ^ q8i y * q ^ q8j y := hev y
    _ = g * (a 1 ^ q8i y * xa 0 ^ q8j y) * g⁻¹ := by
        rw [hg1, hg2, conj_pow, conj_pow]
        group
    _ = g * y * g⁻¹ := by rw [← q8_normal_form y]

theorem mul_self_ne_one_map {A : Type} [Group A] (e : A ≃* Q8) {w : A} (hw : w * w ≠ 1) :
    e w * e w ≠ 1 := by
  rw [← map_mul]
  exact fun h => hw (e.injective (h.trans (map_one e).symm))

theorem aut_inner_of_invol {A : Type} [Group A] (e : A ≃* Q8) (α : MulAut A)
    (h2 : ∀ y, α (α y) = y) {w : A} (hw : w * w ≠ 1) (hαw : α w = w) :
    ∃ g : A, ∀ y, α y = g * y * g⁻¹ := by
  let β : MulAut Q8 := e.symm.trans (α.trans e)
  have hβ : ∀ y, β y = e (α (e.symm y)) := fun y => rfl
  obtain ⟨g, hg⟩ := q8_aut_inner_of_invol β (fun y => by simp [hβ, h2])
    (mul_self_ne_one_map e hw) (by simp [hβ, hαw])
  refine ⟨e.symm g, fun y => ?_⟩
  have h3 : e (α y) = g * e y * g⁻¹ := by simpa [hβ] using hg (e y)
  rw [← e.symm_apply_apply (α y), h3, map_mul, map_mul, map_inv, e.symm_apply_apply]

end Out

open Out

theorem eq_of_fixed_of_invol {α : Type} [Finite α] (hc : Nat.card α = 3) (σ : Equiv.Perm α)
    (h1 : σ ≠ 1) (h2 : σ * σ = 1) {i j : α} (hi : σ i = i) (hj : σ j = j) : i = j := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  have hf : Fintype.card α = 3 := by rw [← Nat.card_eq_fintype_card]; exact hc
  let eT : α ≃ Fin 3 := Fintype.equivFinOfCardEq hf
  have h3 : eT.permCongr σ ≠ 1 := fun h => h1 ((map_eq_one_iff _ eT.permCongrHom.injective).mp h)
  have h4 : eT.permCongr σ * eT.permCongr σ = 1 := by
    have h5 : eT.permCongr (σ * σ) = eT.permCongr σ * eT.permCongr σ :=
      map_mul eT.permCongrHom σ σ
    have h6 : eT.permCongr (1 : Equiv.Perm α) = 1 := map_one eT.permCongrHom
    rw [← h5, h2, h6]
  refine eT.injective (perm3_eq_of_fixed _ h4 h3 (eT i) (eT j) ?_ ?_)
  · simp [Equiv.permCongr_apply, hi]
  · simp [Equiv.permCongr_apply, hj]

theorem card_eq_two_mul_zpowers {A : Type} [Group A] (e : A ≃* Q8) {y : A} (hy : y * y ≠ 1) :
    Nat.card A = 2 * Nat.card (Subgroup.zpowers y) := by
  obtain ⟨h4, h2⟩ := q8_pow_four _ (mul_self_ne_one_map e hy)
  have ho : orderOf (e y) = 2 ^ 2 :=
    orderOf_eq_prime_pow (by simpa using h2) (by simpa using h4)
  rw [Nat.card_zpowers, ← MulEquiv.orderOf_eq e y, ho, Nat.card_congr e.toEquiv, card_q8]
  norm_num

theorem idx2_act_zpowers {A : Type} [Group A] (φ : MulAut A) {g : A}
    (hg : φ g = g ∨ φ g = g⁻¹) (H : Idx2 A) (hH : H.1 = Subgroup.zpowers g) :
    Idx2.act φ H = H := by
  have hmem : ∀ (ψ : MulAut A), (ψ g = g ∨ ψ g = g⁻¹) → ∀ n : ℤ,
      ψ (g ^ n) ∈ Subgroup.zpowers g := by
    intro ψ hψ n
    rw [map_zpow]
    rcases hψ with h | h <;> rw [h]
    · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) n
    · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers g)) n
  have hg' : φ.symm g = g ∨ φ.symm g = g⁻¹ := by
    rcases hg with h | h
    · left
      calc φ.symm g = φ.symm (φ g) := by rw [h]
        _ = g := φ.symm_apply_apply g
    · right
      calc φ.symm g = φ.symm (φ g⁻¹) := by rw [map_inv, h, inv_inv]
        _ = g⁻¹ := φ.symm_apply_apply _
  apply Subtype.ext
  apply Subgroup.ext
  intro y
  rw [Idx2.act_apply, hH]
  constructor
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    have := hmem φ hg n
    rwa [hn, MulEquiv.apply_symm_apply] at this
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact hmem φ.symm hg' n

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
