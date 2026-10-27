module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Matrix

theorem card_modEq_card_fixed_of_iterate_seven {α : Type*} [Finite α] (f : α → α)
    (hf : f^[7] = id) : Nat.card α ≡ Nat.card {a // f a = a} [MOD 7] := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := (f : Function.End α)) (p := 7)
    (n := 1) hf
  have hcardfix : Fintype.card {a // f a = a} =
      Fintype.card (Function.fixedPoints (f : Function.End α)) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
    rfl
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcardfix]
  exact h

variable {K : Type*} [Field K]

theorem card_fixedVec_eq_four_of_pow_seven (hK : Nat.card K = 4) {g : Matrix (Fin 4) (Fin 4) K}
    (hg7 : g ^ 7 = 1) (hg1 : g ≠ 1) : Nat.card {v : Fin 4 → K // g *ᵥ v = v} = 4 := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  letI : Fintype K := Fintype.ofFinite K
  have hKcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have hcardV : Nat.card (Fin 4 → K) = 256 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, hKcard, Fintype.card_fin]
    norm_num
  have hpow : ∀ (n : ℕ) (v : Fin 4 → K),
      (fun w : Fin 4 → K => g *ᵥ w)^[n] v = g ^ n *ᵥ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [Function.iterate_succ_apply', ih]
      show g *ᵥ (g ^ n *ᵥ v) = g ^ (n + 1) *ᵥ v
      rw [Matrix.mulVec_mulVec, pow_succ']
  have hf7 : (fun v : Fin 4 → K => g *ᵥ v)^[7] = id := by
    funext v
    rw [hpow 7 v, hg7, Matrix.one_mulVec]
    rfl
  have hmod : Nat.card (Fin 4 → K) ≡ Nat.card {v : Fin 4 → K // g *ᵥ v = v} [MOD 7] := by
    simpa using card_modEq_card_fixed_of_iterate_seven (α := Fin 4 → K) (fun v => g *ᵥ v) hf7
  have hmod' : Nat.card {v : Fin 4 → K // g *ᵥ v = v} ≡ 4 [MOD 7] := by
    have h1 : Nat.card {v : Fin 4 → K // g *ᵥ v = v} ≡ Nat.card (Fin 4 → K) [MOD 7] :=
      hmod.symm
    rw [hcardV] at h1
    exact h1.trans (by norm_num [Nat.ModEq])
  let W : Submodule K (Fin 4 → K) := LinearMap.ker (Matrix.mulVecLin (g - 1))
  have hmem : ∀ v : Fin 4 → K, v ∈ W ↔ g *ᵥ v = v := fun v => by
    show v ∈ LinearMap.ker (Matrix.mulVecLin (g - 1)) ↔ g *ᵥ v = v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hWset : (W : Set (Fin 4 → K)) = {v : Fin 4 → K | g *ᵥ v = v} :=
    Set.ext fun v => by simpa using hmem v
  have hcardW : Nat.card {v : Fin 4 → K // g *ᵥ v = v} = Nat.card W :=
    Nat.card_congr (Set.equivOfEq hWset).symm
  have hcardWfin : Nat.card W = 4 ^ Module.finrank K W := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := W), hK]
  have hfinV : Module.finrank K (Fin 4 → K) = 4 := by rw [Module.finrank_fin_fun]
  have hrle : Module.finrank K W ≤ 4 :=
    (Submodule.finrank_le W).trans (le_of_eq hfinV)
  have hrmod : 4 ^ Module.finrank K W ≡ 4 [MOD 7] := by
    rw [hcardW, hcardWfin] at hmod'
    exact hmod'
  have key : ∀ r : ℕ, r ≤ 4 → 4 ^ r ≡ 4 [MOD 7] → r = 1 ∨ r = 4 := by
    intro r _ h
    interval_cases r
    · exact absurd h (by norm_num [Nat.ModEq])
    · exact Or.inl rfl
    · exact absurd h (by norm_num [Nat.ModEq])
    · exact absurd h (by norm_num [Nat.ModEq])
    · exact Or.inr rfl
  obtain hr1 | hr4 := key (Module.finrank K W) hrle hrmod
  · rw [hcardW, hcardWfin, hr1]
    norm_num
  · exfalso
    have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hr4, hfinV])
    have hfixall : ∀ v : Fin 4 → K, g *ᵥ v = v := by
      intro v
      have hv : v ∈ W := by rw [htop]; exact Submodule.mem_top
      exact (hmem v).mp hv
    apply hg1
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [Matrix.one_mulVec]
    exact hfixall (Pi.single j 1)

end CFSG.OddStandard.AltStdSec.SwapPartner
