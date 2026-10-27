module

public import CFSG.LargeExtraspecial.S14W4SetDictC
public import CFSG.LargeExtraspecial.S4Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup CFSG.LargeExtraspecial.S4

variable {X : Type*} [Group X] [Finite X] (T : Setting X)

@[expose] def Lat (R : Subgroup X) : Prop :=
  (∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = ⊤) ∨
    ∃ W₁ W₂ : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W₁ ∧ W4Dict.IsInv T R W₂ ∧
      W₁ ⊓ W₂ = ⊥ ∧ Nat.card W₁ = 2 ^ 4 ∧ Nat.card W₂ = 2 ^ 4 ∧
      ∀ W : Submodule (ZMod 2) T.Qt, W4Dict.IsInv T R W → W = ⊥ ∨ W = W₁ ∨ W = W₂ ∨ W = ⊤

instance instFiniteO : Finite T.O :=
  Finite.of_injective (fun s : T.O => ((s : T.Qt ≃ₗ[ZMod 2] T.Qt) : T.Qt → T.Qt))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

variable {T}

theorem mem_fixSub_zpowers_iff (e : T.O) (v : T.Qt) :
    v ∈ fixSub T (zpowers e) ↔ (e : T.Qt ≃ₗ[ZMod 2] T.Qt) v = v := by
  constructor
  · exact fun hv => hv e (mem_zpowers e)
  · intro hv x hx
    have hx' : ∃ i : ℤ, e ^ i = x := mem_zpowers_iff.mp hx
    cases hx' with
    | intro i hi =>
      subst hi
      have hfix : ∀ n : ℕ, ((e ^ n : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v = v := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih =>
          change ((e ^ n * e : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v = v
          rw [← pow_succ, pow_succ']
          change (e : T.Qt ≃ₗ[ZMod 2] T.Qt) (((e ^ n : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) v) = v
          rw [ih, hv]
      have hfo : IsOfFinOrder e := isOfFinOrder_of_finite e
      obtain ⟨n, hn⟩ := (hfo.mem_powers_iff_mem_zpowers (y := e ^ i)).mpr (zpow_mem_zpowers e i)
      rw [← hn]
      exact hfix n

theorem isPGroup_zpowers_ρ (k : T.M) (hk : ∃ n : ℕ, k ^ 2 ^ n = 1) :
    IsPGroup 2 (zpowers (T.ρ k)) := by
  intro x
  have hx : ∃ i : ℤ, T.ρ k ^ i = x := mem_zpowers_iff.mp x.2
  cases hk with
  | intro n hn =>
    cases hx with
    | intro i hi =>
      refine ⟨n, Subtype.ext ?_⟩
      have e1 : T.ρ k ^ 2 ^ n = 1 := by rw [← map_pow, hn, map_one]
      have e2 : ((x ^ 2 ^ n : ↥(zpowers (T.ρ k))) : T.O) = (x : T.O) ^ 2 ^ n := rfl
      rw [e2, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, e1, one_zpow]
      rfl

end CFSG.LargeExtraspecial.S14.W4Loc
