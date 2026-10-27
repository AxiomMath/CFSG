module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup

variable {Γ : Type*} [Group Γ]

def conjFun (g : Γ) (E : Subgroup Γ) (hgE : ∀ x ∈ E, g * x * g⁻¹ ∈ E) : ↥E → ↥E :=
  fun x => ⟨g * x * g⁻¹, hgE x x.2⟩

def conjEnd (g : Γ) (E : Subgroup Γ) (hgE : ∀ x ∈ E, g * x * g⁻¹ ∈ E) : Function.End ↥E :=
  conjFun g E hgE

theorem conjEnd_pow_apply (g : Γ) (E : Subgroup Γ) (hgE : ∀ x ∈ E, g * x * g⁻¹ ∈ E) (n : ℕ)
    (x : ↥E) : (((conjEnd g E hgE) ^ n) x : Γ) = g ^ n * x * (g ^ n)⁻¹ := by
  induction n generalizing x with
  | zero =>
    rw [pow_zero, pow_zero]
    show (x : Γ) = 1 * x * 1⁻¹
    group
  | succ n ih =>
    have h1 : ((conjEnd g E hgE) ^ (n + 1)) x = ((conjEnd g E hgE) ^ n) ((conjEnd g E hgE) x) := by
      rw [pow_succ]
      rfl
    rw [h1, ih]
    show g ^ n * (g * (x : Γ) * g⁻¹) * (g ^ n)⁻¹ = g ^ (n + 1) * x * (g ^ (n + 1))⁻¹
    group

theorem card_modEq_card_inf_centralizer {g : Γ} (hg : g ^ 23 = 1) {E : Subgroup Γ} [Finite E]
    (hgE : ∀ x ∈ E, g * x * g⁻¹ ∈ E) :
    Nat.card E ≡ Nat.card ↥(E ⊓ centralizer ({g} : Set Γ)) [MOD 23] := by
  have : Fact (Nat.Prime 23) := ⟨by decide⟩
  have : Fintype ↥E := Fintype.ofFinite _
  have : DecidableEq ↥E := Classical.decEq _
  have hf : (conjEnd g E hgE) ^ 23 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show (((conjEnd g E hgE) ^ 23 ^ 1) x : Γ) = x
    rw [pow_one, conjEnd_pow_apply, hg]
    group
  have h := Equiv.Perm.card_fixedPoints_modEq (p := 23) (n := 1) hf
  have hfix : Nat.card (Function.fixedPoints (conjFun g E hgE)) =
      Nat.card ↥(E ⊓ centralizer ({g} : Set Γ)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · have h2 := congrArg Subtype.val x.2
      simp only [conjFun] at h2
      exact mem_centralizer_singleton_iff.2 (by
        calc (x.1 : Γ) * g = g * x.1 * g⁻¹ * g := by rw [h2]
          _ = g * x.1 := by group)
    · apply Subtype.ext
      have h2 : (y : Γ) * g = g * y := mem_centralizer_singleton_iff.1 y.2.2
      show g * (y : Γ) * g⁻¹ = y
      calc g * (y : Γ) * g⁻¹ = (g * y) * g⁻¹ := rfl
        _ = (y * g) * g⁻¹ := by rw [h2]
        _ = y := by group
  have h' : Fintype.card ↥E ≡ Fintype.card ↑(Function.fixedPoints (conjFun g E hgE)) [MOD 23] := h
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hfix] at h'
  exact h'

theorem card_dvd_factorial_index {M : Type*} [Group M] [Finite M] [IsSimpleGroup M]
    {S : Subgroup M} (hS : S ≠ ⊤) : Nat.card M ∣ S.index.factorial := by
  have hker : (MulAction.toPermHom M (M ⧸ S)).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom M (M ⧸ S)).ker with h | h
    · exact h
    · exfalso
      apply hS
      rw [eq_top_iff]
      intro g _
      have hg : g ∈ (MulAction.toPermHom M (M ⧸ S)).ker := h ▸ mem_top g
      have h1 : (MulAction.toPermHom M (M ⧸ S) g) (QuotientGroup.mk (1 : M)) =
          QuotientGroup.mk 1 := by
        rw [MonoidHom.mem_ker.1 hg]
        rfl
      have h3 : (MulAction.toPermHom M (M ⧸ S) g) (QuotientGroup.mk (1 : M)) =
          QuotientGroup.mk (g * 1) := rfl
      rw [mul_one] at h3
      have h4 := QuotientGroup.eq.1 (h3.symm.trans h1)
      simpa using h4
  have hinj : Function.Injective (MulAction.toPermHom M (M ⧸ S)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have h := Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card] at h
  exact h

end CFSG.EvenSporadicStandard.Induction.Balance
