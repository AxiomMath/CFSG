module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open Equiv.Perm

theorem card_modEq_fixedBy_four {G X : Type*} [Group G] [MulAction G X] [Finite X]
    [IsSimpleGroup G] (hna : ∃ a b : G, a * b ≠ b * a) {e : G} (he : e * e = 1) :
    Nat.card X ≡ Nat.card (MulAction.fixedBy X e) [MOD 4] := by
  classical
  have := Fintype.ofFinite X
  let φ := MulAction.toPermHom G X
  let sg : G →* ℤˣ := Equiv.Perm.sign.comp φ
  have hker : sg.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal sg.ker with h | h
    · exfalso
      have hinj : Function.Injective sg := (MonoidHom.ker_eq_bot_iff sg).1 h
      obtain ⟨a, b, hab⟩ := hna
      apply hab
      apply hinj
      rw [map_mul, map_mul, mul_comm]
    · exact h
  have h1 : Equiv.Perm.sign (φ e) = 1 := by
    have : e ∈ sg.ker := hker ▸ Subgroup.mem_top e
    exact this
  have hσ : (φ e) ^ 2 = 1 := by rw [← map_pow, pow_two, he, map_one]
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hσ
  rw [h1] at hsign
  have hfix : Function.fixedPoints (φ e) = MulAction.fixedBy X e := by
    ext x
    simp [Function.fixedPoints, Function.IsFixedPt, φ, MulAction.mem_fixedBy]
  have hcard : Fintype.card (Function.fixedPoints (φ e)) = Nat.card (MulAction.fixedBy X e) := by
    rw [← Nat.card_eq_fintype_card]
    exact congrArg (fun s : Set X => Nat.card ↥s) hfix
  have hcompl : Fintype.card (Function.fixedPoints (φ e)) = ((φ e).supportᶜ).card := by
    rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType, Finset.card_compl]
  have hpar := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) (σ := φ e)
    (by rw [pow_one]; exact hσ)
  have hle : Fintype.card (Function.fixedPoints (φ e)) ≤ Fintype.card X := by
    rw [hcompl]
    exact Finset.card_le_univ _
  have hev : Even ((Fintype.card X - Fintype.card (Function.fixedPoints (φ e))) / 2) := by
    have h2 : (-1 : ℤˣ) ^ ((Fintype.card X - Fintype.card (Function.fixedPoints (φ e))) / 2) = 1 :=
      hsign.symm
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 h2
  have hdvd2 : 2 ∣ Fintype.card X - Fintype.card (Function.fixedPoints (φ e)) := by
    rw [hcompl] at hle ⊢
    have := (Nat.modEq_iff_dvd' hle).1 hpar
    exact this
  obtain ⟨m, hm⟩ := hev
  have h4 : 4 ∣ Fintype.card X - Fintype.card (Function.fixedPoints (φ e)) := by
    obtain ⟨k, hk⟩ := hdvd2
    refine ⟨m, ?_⟩
    omega
  rw [Nat.card_eq_fintype_card (α := X), ← hcard]
  exact ((Nat.modEq_iff_dvd' hle).2 h4).symm

end CFSG.EvenSporadicStandard.M12Std.Yosh
