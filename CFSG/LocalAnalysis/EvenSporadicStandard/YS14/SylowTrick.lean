module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.YS14

open Subgroup

open scoped Pointwise

theorem exists_fixed_of_pow_four_eq_one {α : Type*} [Finite α] (σ : Equiv.Perm α)
    (hσ : σ ^ 4 = 1) (hodd : Odd (Nat.card α)) : ∃ a : α, σ a = a := by
  classical
  haveI := Fintype.ofFinite α
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : σ ^ 2 ^ 2 = 1 := by simpa using hσ
  have hmod := Equiv.Perm.card_compl_support_modEq h4
  rw [Nat.card_eq_fintype_card] at hodd
  by_contra hno
  push Not at hno
  have hempty : (Equiv.Perm.support σ)ᶜ = ∅ := by
    ext a
    simp [Equiv.Perm.mem_support, hno a]
  rw [hempty, Finset.card_empty] at hmod
  have : Even (Fintype.card α) := by
    rw [Nat.even_iff]
    exact (Nat.ModEq.symm hmod)
  exact (Nat.not_even_iff_odd.2 hodd) this

theorem finite_subgroup_of_finite (K : Type*) [Group K] [Finite K] : Finite (Subgroup K) :=
  Finite.of_injective (fun H : Subgroup K => (H : Set K)) SetLike.coe_injective

theorem card_fixedSubgroup_ge {K : Type*} [Group K] [Finite K] (α : MulAut K)
    (hαα : α * α = 1) (E : Subgroup K) (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hαE : α • E = E) :
    ∃ C : Subgroup K, (∀ x ∈ C, α x = x) ∧ (∀ x ∈ C, x * x = 1) ∧
      (∀ x ∈ C, ∀ y ∈ C, x * y = y * x) ∧ Nat.card ↥E ≤ Nat.card ↥C * Nat.card ↥C := by
  classical
  have hinv : ∀ a : K, α (α a) = a := fun a => by
    have h := congrArg (fun f : MulAut K => f a) hαα
    simpa using h
  have hmapE : ∀ a ∈ E, α a ∈ E := fun a ha => by
    have h : α • a ∈ α • E := Subgroup.smul_mem_pointwise_smul a α E ha
    rw [hαE] at h
    exact h
  let C : Subgroup K :=
    { carrier := {x | x ∈ E ∧ α x = x}
      mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by simp [map_mul, hx.2, hy.2]⟩
      one_mem' := ⟨E.one_mem, map_one α⟩
      inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by simp [map_inv, hx.2]⟩ }
  have hC : ∀ x, x ∈ C ↔ x ∈ E ∧ α x = x := fun x => Iff.rfl
  have hφC : ∀ a : E, (a : K) * α a ∈ C := by
    intro a
    rw [hC]
    refine ⟨E.mul_mem a.2 (hmapE _ a.2), ?_⟩
    rw [map_mul, hinv]
    exact hEc _ (hmapE _ a.2) _ a.2
  let Φ : E →* C := MonoidHom.mk' (fun a : E => (⟨(a : K) * α a, hφC a⟩ : C)) (by
    intro a b
    apply Subtype.ext
    show (a : K) * (b : K) * α ((a : K) * (b : K)) = ((a : K) * α a) * ((b : K) * α b)
    rw [map_mul]
    have hc : (b : K) * α a = α a * (b : K) := hEc _ b.2 _ (hmapE _ a.2)
    calc (a : K) * (b : K) * (α a * α b) = (a : K) * ((b : K) * α a) * α b := by group
      _ = (a : K) * (α a * (b : K)) * α b := by rw [hc]
      _ = ((a : K) * α a) * ((b : K) * α b) := by group)
  have hker : ∀ y : E, y ∈ Φ.ker → α (y : K) = (y : K) := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (y : K) * α y = 1 := by
      have := congrArg Subtype.val hy
      exact this
    have h2 : (y : K) * (y : K) = 1 := hE2 _ y.2
    calc α (y : K) = ((y : K))⁻¹ := eq_inv_of_mul_eq_one_right h1
      _ = (y : K) := inv_eq_of_mul_eq_one_right h2
  have hkerC : ∀ y : Φ.ker, (((y : E) : K)) ∈ C := fun y =>
    (hC _).2 ⟨(y : E).2, hker _ y.2⟩
  have hcard_ker : Nat.card Φ.ker ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun y : Φ.ker => (⟨((y : E) : K), hkerC y⟩ : C)) (by
      intro y z h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h'))
  have hcard_range : Nat.card Φ.range ≤ Nat.card C := Subgroup.card_le_card_group _
  refine ⟨C, fun x hx => ((hC x).1 hx).2, fun x hx => hE2 x ((hC x).1 hx).1,
    fun x hx y hy => hEc x ((hC x).1 hx).1 y ((hC y).1 hy).1, ?_⟩
  calc Nat.card ↥E = Nat.card Φ.ker * Φ.ker.index := (Subgroup.card_mul_index Φ.ker).symm
    _ = Nat.card Φ.ker * Nat.card Φ.range := by rw [Subgroup.index_ker]
    _ ≤ Nat.card C * Nat.card C := Nat.mul_le_mul hcard_ker hcard_range

end CFSG.EvenSporadicStandard.YS14
