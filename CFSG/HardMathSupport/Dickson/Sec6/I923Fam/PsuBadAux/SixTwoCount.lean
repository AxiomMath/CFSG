module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem card_modEq_fixed (g : Matrix (Fin n) (Fin n) K) (hg : g ^ 11 = 1)
    (U : Submodule K (Fin n → K)) (hU : ∀ v ∈ U, g *ᵥ v ∈ U) :
    ∃ F : Submodule K (Fin n → K), F ≤ U ∧ (∀ v, v ∈ F ↔ v ∈ U ∧ g *ᵥ v = v) ∧
      Nat.card U ≡ Nat.card F [MOD 11] := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let F : Submodule K (Fin n → K) :=
    { carrier := {v | v ∈ U ∧ g *ᵥ v = v}
      add_mem' := fun {a b} ha hb => ⟨U.add_mem ha.1 hb.1, by rw [mulVec_add, ha.2, hb.2]⟩
      zero_mem' := ⟨U.zero_mem, mulVec_zero g⟩
      smul_mem' := fun c v hv => ⟨U.smul_mem c hv.1, by rw [mulVec_smul, hv.2]⟩ }
  have hF : ∀ v, v ∈ F ↔ v ∈ U ∧ g *ᵥ v = v := fun v => Iff.rfl
  refine ⟨F, fun v hv => hv.1, hF, ?_⟩
  let f : Function.End U := fun v => ⟨g *ᵥ (v : Fin n → K), hU v v.2⟩
  have hfpow : ∀ k : ℕ, ∀ v : U, (((f ^ k) v : U) : Fin n → K) = (g ^ k) *ᵥ (v : Fin n → K) := by
    intro k
    induction k with
    | zero => intro v; rw [pow_zero, pow_zero, one_mulVec]; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, Function.End.mul_def]
      change (((f ^ k) (f v) : U) : Fin n → K) = _
      rw [ih, pow_succ, ← mulVec_mulVec]
  have hf : f ^ 11 ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, hfpow, hg, one_mulVec]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 11) (n := 1) hf
  have e : f.fixedPoints ≃ F :=
    { toFun := fun v => ⟨(v.1 : Fin n → K), (hF _).2 ⟨v.1.2, by
        have := v.2
        exact congrArg Subtype.val this⟩⟩
      invFun := fun v => ⟨⟨v.1, ((hF _).1 v.2).1⟩, Subtype.ext ((hF _).1 v.2).2⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  have h1 : Nat.card U = Fintype.card U := Nat.card_eq_fintype_card
  have h2 : Nat.card F = Fintype.card f.fixedPoints := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e]
  rw [h2, h1]
  exact hmod

theorem natCard_submodule (hK : Nat.card K = 4) (U : Submodule K (Fin n → K)) :
    Nat.card U = 4 ^ Module.finrank K U := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := U),
    ← Nat.card_eq_fintype_card (α := K), hK]

theorem four_pow_modEq_aux : ∀ m ≤ 6, ∀ d < m, 4 ^ m % 11 = 4 ^ d % 11 → 5 ≤ m := by
  decide

theorem four_pow_modEq_six : ∀ d < 6, 4 ^ 6 % 11 = 4 ^ d % 11 → d = 1 := by
  decide

theorem five_le_finrank_of_ne (hK : Nat.card K = 4) (g : Matrix (Fin n) (Fin n) K)
    (hg : g ^ 11 = 1) (U : Submodule K (Fin n → K)) (hU : ∀ v ∈ U, g *ᵥ v ∈ U)
    (hm : Module.finrank K U ≤ 6) (hne : ∃ v ∈ U, g *ᵥ v ≠ v) : 5 ≤ Module.finrank K U := by
  classical
  obtain ⟨F, hFU, hF, hmod⟩ := card_modEq_fixed g hg U hU
  have hlt : F < U := by
    obtain ⟨v, hvU, hv⟩ := hne
    exact lt_of_le_of_ne hFU fun h => hv (((hF v).1 (h ▸ hvU)).2)
  have hd : Module.finrank K F < Module.finrank K U := Submodule.finrank_lt_finrank_of_lt hlt
  rw [natCard_submodule hK, natCard_submodule hK] at hmod
  exact four_pow_modEq_aux _ hm _ hd hmod

theorem finrank_fixed_eq_one (hK : Nat.card K = 4) (g : Matrix (Fin 6) (Fin 6) K)
    (hg : g ^ 11 = 1) (hne : g ≠ 1) :
    ∃ F : Submodule K (Fin 6 → K), (∀ v, v ∈ F ↔ g *ᵥ v = v) ∧ Module.finrank K F = 1 := by
  classical
  obtain ⟨F, hFU, hF, hmod⟩ := card_modEq_fixed g hg ⊤ (fun v _ => Submodule.mem_top)
  refine ⟨F, fun v => by rw [hF]; simp, ?_⟩
  have hlt : F < ⊤ := by
    refine lt_of_le_of_ne hFU fun h => hne ?_
    have : ∀ v, g *ᵥ v = v := fun v => ((hF v).1 (h ▸ Submodule.mem_top)).2
    ext i j
    have := congrFun (this (Pi.single j 1)) i
    simpa [mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
  have hd : Module.finrank K F < Module.finrank K (⊤ : Submodule K (Fin 6 → K)) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  rw [natCard_submodule hK, natCard_submodule hK] at hmod
  have h6 : Module.finrank K (⊤ : Submodule K (Fin 6 → K)) = 6 := by
    rw [finrank_top, Module.finrank_fin_fun]
  rw [h6] at hmod hd
  exact four_pow_modEq_six _ hd hmod

end CFSG.HardMathSupport.Dickson.Sec6.I923
