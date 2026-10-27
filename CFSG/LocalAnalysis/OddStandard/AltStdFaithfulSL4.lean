module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.OddStandard.AltStdFaithful

open Module

section Counting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

theorem card_modEq_card_ker_inf {p n : ℕ} [hp : Fact p.Prime] {g : Module.End K V}
    (hg : g ^ p ^ n = 1) (U : Submodule K V) (hU : ∀ v ∈ U, g v ∈ U) :
    Nat.card U ≡ Nat.card (U ⊓ LinearMap.ker (g - 1) : Submodule K V) [MOD p] := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let f : Function.End U := fun v => ⟨g v, hU v v.2⟩
  have hpow : ∀ k : ℕ, ∀ v : U, ((f ^ k) v : V) = (g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ, pow_succ]
      exact (ih (f v)).trans rfl
  have hf : f ^ p ^ n = 1 := by
    funext v
    apply Subtype.ext
    rw [hpow, hg]
    rfl
  have h1 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := n) hf
  have hmem : ∀ v : Function.fixedPoints (f : U → U),
      ((v.1 : U) : V) ∈ LinearMap.ker (g - 1) := by
    intro v
    have h : g (v.1 : V) = (v.1 : V) := congrArg Subtype.val v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply]
    exact sub_eq_zero.2 h
  have hfix : ∀ w : ↥(U ⊓ LinearMap.ker (g - 1) : Submodule K V),
      (f : U → U) ⟨w.1, w.2.1⟩ = ⟨w.1, w.2.1⟩ := by
    intro w
    have h := (LinearMap.mem_ker.1 w.2.2)
    rw [LinearMap.sub_apply, Module.End.one_apply] at h
    exact Subtype.ext (sub_eq_zero.1 h)
  let e : (Function.fixedPoints (f : U → U)) ≃ ↥(U ⊓ LinearMap.ker (g - 1) : Submodule K V) :=
    { toFun := fun v => ⟨(v.1 : V), v.1.2, hmem v⟩
      invFun := fun w => ⟨⟨w.1, w.2.1⟩, hfix w⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }
  have h2 : Nat.card (Function.fixedPoints (f : U → U)) =
      Nat.card ↥(U ⊓ LinearMap.ker (g - 1) : Submodule K V) := Nat.card_congr e
  rw [← h2, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card (α := Function.fixedPoints (f : U → U))]
  convert h1

end Counting

section Group

open CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Fintype K]

omit [Fintype K] in
theorem det_eq_one_of_mem_statedSL {n : ℕ} {A : GL (Fin n) K} (hA : A ∈ StatedSL n K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL hA

end Group

end CFSG.OddStandard.AltStdFaithful
