module

public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest

theorem t2H_zmodProd {A : Type} [CommGroup A] [Finite A] (n : ℕ) [NeZero n] (e₁ e₂ : A)
    (h₁ : orderOf e₁ = n) (h₂ : orderOf e₂ = n)
    (hint : ∀ x, x ∈ Subgroup.zpowers e₁ → x ∈ Subgroup.zpowers e₂ → x = 1)
    (hcard : Nat.card A = n * n) :
    Nonempty (A ≃* Multiplicative (ZMod n) × Multiplicative (ZMod n)) := by
  have key : ∀ e : A, orderOf e = n → ∀ i j : ZMod n,
      e ^ (i + j).val = e ^ i.val * e ^ j.val := by
    intro e he i j
    have hm := pow_mod_orderOf e (i.val + j.val)
    rw [he] at hm
    rw [ZMod.val_add, ← pow_add]
    exact hm
  have hone : ∀ e : A, orderOf e = n → ∀ i : ZMod n, e ^ i.val = 1 → i = 0 := by
    intro e he i hi
    have hdvd := orderOf_dvd_of_pow_eq_one hi
    rw [he] at hdvd
    exact (ZMod.val_eq_zero i).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt i))
  let f : Multiplicative (ZMod n) × Multiplicative (ZMod n) →* A :=
    { toFun := fun p => e₁ ^ p.1.toAdd.val * e₂ ^ p.2.toAdd.val
      map_one' := by simp
      map_mul' := fun p q => by
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, key e₁ h₁, key e₂ h₂]
        exact mul_mul_mul_comm _ _ _ _ }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨i, j⟩ hij
    have hij' : e₁ ^ i.toAdd.val * e₂ ^ j.toAdd.val = 1 := hij
    have h1 : e₁ ^ i.toAdd.val = 1 := by
      apply hint
      · exact Subgroup.pow_mem _ (Subgroup.mem_zpowers e₁) _
      · have : e₁ ^ i.toAdd.val = (e₂ ^ j.toAdd.val)⁻¹ := eq_inv_of_mul_eq_one_left hij'
        rw [this]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers e₂) _)
    have h2 : e₂ ^ j.toAdd.val = 1 := by
      rw [h1, one_mul] at hij'
      exact hij'
    have hi := hone e₁ h₁ _ h1
    have hj := hone e₂ h₂ _ h2
    ext
    · exact hi
    · exact hj
  have hbij : Function.Bijective f := by
    apply hinj.bijective_of_nat_card_le
    rw [hcard, Nat.card_prod]
    have : Nat.card (Multiplicative (ZMod n)) = n :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod n)
    rw [this]
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end CFSG.GH74.GLS.Stage4.Rest
