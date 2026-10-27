module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Elems

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

@[expose] def NoOrder (n : ℕ) (G : Type*) [Group G] : Prop := ∀ g : G, orderOf g ≠ n

theorem not_typeL2_four_of_noOrder65 {S : Type} [Group S] [Finite S] (h : NoOrder 65 S)
    (A : Subgroup S) : ¬ IsTypeL2 (4 ^ 3) (barOf 3 A) := fun hL2 => by
  obtain ⟨a, -, ha⟩ := exists_order_sixtyFive_of_sectionL2 A hL2
  exact h a ha

theorem not_typeL2_five_of_noOrder186 {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) (h : NoOrder 186 S) {ψ : MulAut S} (hψ3 : ψ ^ 3 = 1)
    (hψ1 : ψ ≠ 1) (hψ : ∃ x : S, MulAut.conj x = ψ) (A : Subgroup S) (hA : A ≤ fixSub ψ) :
    ¬ IsTypeL2 (5 ^ 3) (barOf 3 A) := fun hL2 => by
  obtain ⟨a, haA, ha⟩ := exists_order_sixtyTwo_of_sectionL2 A hL2
  obtain ⟨x, rfl⟩ := hψ
  have hx3 : x ^ 3 = 1 := by
    have h3 : MulAut.conj (x ^ 3) = 1 := by rw [map_pow]; exact hψ3
    have hmem : x ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun β : MulAut S => β g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hψ1 (map_one _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcomm : Commute x a := by
    have := mem_fixSub.1 (hA haA)
    simp only [MulAut.conj_apply] at this
    unfold Commute SemiconjBy
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hcop : Nat.Coprime (orderOf x) (orderOf a) := by
    rw [hxo, ha]
    norm_num
  exact h (x * a) (by rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hxo, ha])

end CFSG.HardMathSupport.Dickson.Sec6.I1431
