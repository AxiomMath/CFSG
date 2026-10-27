module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

theorem exists_fixed_of_involutive {α : Type} [Finite α] {f : α → α} (hf : Function.Involutive f)
    (hodd : Odd (Nat.card α)) : ∃ x : α, f x = x := by
  have : Fintype α := Fintype.ofFinite α
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    ext x
    exact hf x
  have hndvd : ¬ 2 ∣ Fintype.card α := by
    rw [← Nat.card_eq_fintype_card]
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (hp := ⟨Nat.prime_two⟩) hndvd hσ
  exact ⟨x, hx⟩

theorem exists_fixed_lift {J : Type} [Group J] [Finite J] (N : Subgroup J) [N.Normal]
    (hN : Odd (Nat.card N)) (a : MulAut J) (ha : a * a = 1) (haN : N.map a.toMonoidHom = N)
    (g : J) (hg : (a g)⁻¹ * g ∈ N) : ∃ g' : J, a g' = g' ∧ (g'⁻¹ * g) ∈ N := by
  have ha' : ∀ x : J, a (a x) = x := fun x => by
    have := congrArg (fun f : MulAut J => f x) ha
    simpa using this
  have haN' : ∀ n ∈ N, a n ∈ N := fun n hn => by
    have := Subgroup.mem_map_of_mem a.toMonoidHom hn
    rwa [haN] at this
  have hmem : ∀ y : {y : J // y⁻¹ * g ∈ N}, (a y.1)⁻¹ * g ∈ N := by
    intro y
    have h1 : a (y.1⁻¹ * g) ∈ N := haN' _ y.2
    have h2 : (a y.1)⁻¹ * g = a (y.1⁻¹ * g) * ((a g)⁻¹ * g) := by
      rw [map_mul, map_inv]
      group
    rw [h2]
    exact N.mul_mem h1 hg
  let f : {y : J // y⁻¹ * g ∈ N} → {y : J // y⁻¹ * g ∈ N} := fun y => ⟨a y.1, hmem y⟩
  have hf : Function.Involutive f := fun y => Subtype.ext (ha' y.1)
  let e : {y : J // y⁻¹ * g ∈ N} ≃ N :=
    { toFun := fun y => ⟨y.1⁻¹ * g, y.2⟩
      invFun := fun n => ⟨g * n.1⁻¹, by simp⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun n => Subtype.ext (by simp) }
  have hcard : Nat.card {y : J // y⁻¹ * g ∈ N} = Nat.card N := Nat.card_congr e
  obtain ⟨y, hy⟩ := exists_fixed_of_involutive hf (hcard ▸ hN)
  exact ⟨y.1, congrArg Subtype.val hy, y.2⟩

end CFSG.GH74.GLS.Stage2.Local.P27.QId
