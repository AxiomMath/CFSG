module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

theorem exists_fixed_involution {Y : Type} [Group Y] [Finite Y] (hY : 2 ∣ Nat.card Y)
    (α : MulAut Y) (hα : α * α = 1) : ∃ x : Y, orderOf x = 2 ∧ α x = x := by
  classical
  have : Fintype Y := Fintype.ofFinite Y
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : Equiv.Perm Y := MulAut.toPerm Y α with hσdef
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, ← map_mul, hα, map_one]
  have hmod := Equiv.Perm.card_compl_support_modEq hσ
  have hfix : Nat.card (fixSubgroup α) = σ.supportᶜ.card := by
    rw [Nat.card_eq_fintype_card]
    have : (σ.supportᶜ : Finset Y) = Finset.univ.filter (fun x => α x = x) := by
      ext x
      simp only [Equiv.Perm.mem_support, hσdef, Finset.mem_compl, not_not, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rfl
    rw [this, ← Fintype.card_subtype]
    rfl
  have hdvd : 2 ∣ Nat.card (fixSubgroup α) := by
    rw [hfix]
    have h2 : 2 ∣ Fintype.card Y := by rwa [Nat.card_eq_fintype_card] at hY
    exact (Nat.modEq_zero_iff_dvd).1 (hmod.trans ((Nat.modEq_zero_iff_dvd).2 h2))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fixSubgroup α) 2 hdvd
  refine ⟨(x : Y), by rw [Subgroup.orderOf_coe]; exact hx, x.2⟩

theorem umovesCond_of_forall_isConj {Y : Type} [Group Y] [Finite Y] (hY : 2 ∣ Nat.card Y)
    (hcl : ∀ a b : Y, orderOf a = 2 → orderOf b = 2 → IsConj a b) : UMovesCond Y := by
  intro u hu α hα
  obtain ⟨x, hx2, hαx⟩ := exists_fixed_involution hY α hα
  obtain ⟨h, hh⟩ := isConj_iff.1 (hcl u x hu hx2)
  exact ⟨h, by rw [hh]; exact hαx⟩

end CFSG.EvenSporadicStandard.Solomon78
