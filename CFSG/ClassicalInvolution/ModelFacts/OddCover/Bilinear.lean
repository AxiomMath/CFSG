module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

section ScaleInvariant

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W]

theorem exists_good_scalar [Finite F] (h5 : 5 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0 := by
  classical
  have := Fintype.ofFinite F
  by_contra hcon
  push Not at hcon
  have hcard : Fintype.card F ≤ 4 := by
    by_cases hr : ∃ r : F, r ^ 2 + r + 1 = 0
    · obtain ⟨r, hr⟩ := hr
      have hsub : (Finset.univ : Finset F) ⊆ {0, -1, r, -r - 1} := by
        intro a _
        by_cases ha : a = 0
        · simp [ha]
        by_cases ha1 : a + 1 = 0
        · have : a = -1 := by linear_combination ha1
          simp [this]
        have h := hcon a ha ha1
        have : (a - r) * (a + r + 1) = 0 := by linear_combination h - hr
        rcases mul_eq_zero.1 this with h1 | h1
        · have : a = r := by linear_combination h1
          simp [this]
        · have : a = -r - 1 := by linear_combination h1
          simp [this]
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, -1, r, -r - 1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 4 := Finset.card_le_four
    · push Not at hr
      have hsub : (Finset.univ : Finset F) ⊆ {0, -1} := by
        intro a _
        by_cases ha : a = 0
        · simp [ha]
        by_cases ha1 : a + 1 = 0
        · have : a = -1 := by linear_combination ha1
          simp [this]
        exact absurd (hcon a ha ha1) (hr a)
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, -1} : Finset F).card := Finset.card_le_card hsub
        _ ≤ 4 := le_trans Finset.card_le_two (by norm_num)
  rw [Nat.card_eq_fintype_card] at h5
  omega

theorem biadd_eq_zero_of_scalar_invariant
    (h5 : ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0) (b : V →+ V →+ W)
    (hinv : ∀ a : F, a ≠ 0 → ∀ x y : V, b (a • x) (a • y) = b x y) : b = 0 := by
  by_contra hb
  let Partner : F → F → Prop := fun α β => ∀ x y : V, b (α • x) y = b x (β • y)
  have hPinv : ∀ a : F, a ≠ 0 → Partner a a⁻¹ := fun a ha x y => by
    have := hinv a ha x (a⁻¹ • y)
    rwa [smul_smul, mul_inv_cancel₀ ha, one_smul] at this
  have hPadd : ∀ α β α' β', Partner α β → Partner α' β' → Partner (α + α') (β + β') :=
    fun α β α' β' h h' x y => by
      rw [add_smul, map_add, AddMonoidHom.add_apply, h, h', add_smul, map_add]
  have huniq : ∀ α β β', Partner α β → Partner α β' → β = β' := by
    intro α β β' h h'
    by_contra hne
    apply hb
    have hd : β - β' ≠ 0 := sub_ne_zero.2 hne
    ext x y
    have key : b x ((β - β') • ((β - β')⁻¹ • y)) = 0 := by
      rw [sub_smul, map_sub, ← h x, ← h' x, sub_self]
    rwa [smul_smul, mul_inv_cancel₀ hd, one_smul] at key
  obtain ⟨a, ha0, ha1, ha2⟩ := h5
  have h1 : Partner 1 1 := by simpa using hPinv 1 one_ne_zero
  have h2 := hPadd _ _ _ _ (hPinv a ha0) h1
  have h3 := huniq _ _ _ h2 (hPinv (a + 1) ha1)
  apply ha2
  field_simp at h3
  linear_combination h3

theorem eq_one_of_scalar_invariant {W : Type*} [CommGroup W]
    (h5 : ∃ a : F, a ≠ 0 ∧ a + 1 ≠ 0 ∧ a ^ 2 + a + 1 ≠ 0) (b : V → V → W)
    (hadd₁ : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hadd₂ : ∀ x y y', b x (y + y') = b x y * b x y')
    (hinv : ∀ a : F, a ≠ 0 → ∀ x y, b (a • x) (a • y) = b x y) (x y : V) : b x y = 1 := by
  let b' : V →+ V →+ Additive W :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => Additive.ofMul (b x y))
      (fun y y' => hadd₂ x y y')) (fun x x' => by ext y; exact hadd₁ x x' y)
  have h := biadd_eq_zero_of_scalar_invariant h5 b' (fun a ha x y => hinv a ha x y)
  exact congrArg Additive.toMul (DFunLike.congr_fun (DFunLike.congr_fun h x) y)

end ScaleInvariant

end CFSG.ClassicalInvolution.ModelFacts.OddCover
