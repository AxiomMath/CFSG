module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LinearAlgebra

theorem exists_cartan_fixed_axis_coordinates
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h : I → V) (α : I → Module.Dual K V) (x : V)
    (hx : x ∉ Submodule.span K (Set.range h))
    (hsurj : Function.Surjective (LinearMap.pi α))
    (hker : (LinearMap.pi α).ker = Submodule.span K {x}) :
    ∃ (e : V ≃ₗ[K] ((I → K) × K)),
      e x = (0, 1) ∧
      (∀ i, e (h i) = ((fun j => α j (h i)), 0)) ∧
      (∀ v, (e v).1 = fun i => α i v) ∧
      (∀ i v, e (v - α i v • h i) =
        ((e v).1 - (e v).1 i • (fun j => α j (h i)), (e v).2)) := by
  classical
  let U := Submodule.span K (Set.range h)
  obtain ⟨ℓ, hℓU, hℓx⟩ := LinearMap.exists_extend_of_notMem
    (0 : U →ₗ[K] K) hx 1
  have hℓh : ∀ i, ℓ (h i) = 0 := by
    intro i
    have hv := congrArg (fun f : U →ₗ[K] K =>
      f ⟨h i, Submodule.subset_span (Set.mem_range_self i)⟩) hℓU
    exact hv
  let a : V →ₗ[K] (I → K) := LinearMap.pi α
  have hax : a x = 0 := by
    have hxker : x ∈ a.ker := by
      rw [hker]
      exact Submodule.subset_span (Set.mem_singleton x)
    exact hxker
  let f : V →ₗ[K] ((I → K) × K) := a.prod ℓ
  have hfinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro v hv
      have hav : a v = 0 := congrArg Prod.fst hv
      have hℓv : ℓ v = 0 := congrArg Prod.snd hv
      have hvker : v ∈ a.ker := hav
      rw [hker, Submodule.mem_span_singleton] at hvker
      obtain ⟨t, rfl⟩ := hvker
      have ht : t = 0 := by simpa [hℓx] using hℓv
      simp [ht]
    · exact bot_le
  have hfsurj : Function.Surjective f := by
    rintro ⟨u, t⟩
    obtain ⟨v, hv⟩ := hsurj u
    refine ⟨v + (t - ℓ v) • x, ?_⟩
    apply Prod.ext
    · change a (v + (t - ℓ v) • x) = u
      simpa only [map_add, map_smul, hax, smul_zero, add_zero] using hv
    · change ℓ (v + (t - ℓ v) • x) = t
      simp [map_add, map_smul, hℓx]
  let e := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (a x, ℓ x) = (0, 1)
    rw [hax, hℓx]
  · intro i
    apply Prod.ext
    · rfl
    · exact hℓh i
  · intro v
    rfl
  · intro i v
    apply Prod.ext
    · change a (v - α i v • h i) = a v - α i v • a (h i)
      rw [map_sub, map_smul]
    · change ℓ (v - α i v • h i) = ℓ v
      simp [hℓh]

theorem exists_cartan_fixed_axis_coordinates_of_finrank
    {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I]
    (h : I → V) (α : I → Module.Dual K V) (x : V)
    (hx : x ∉ Submodule.span K (Set.range h))
    (hdim : Module.finrank K V = Fintype.card I + 1)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span K {x}) :
    ∃ (e : V ≃ₗ[K] ((I → K) × K)),
      e x = (0, 1) ∧
      (∀ i, e (h i) = ((fun j => α j (h i)), 0)) ∧
      (∀ v, (e v).1 = fun i => α i v) ∧
      (∀ i v, e (v - α i v • h i) =
        ((e v).1 - (e v).1 i • (fun j => α j (h i)), (e v).2)) := by
  classical
  have hx0 : x ≠ 0 := by
    intro hx0
    exact hx (hx0 ▸ (Submodule.zero_mem _))
  have hker : (LinearMap.pi α).ker = Submodule.span K {x} := by
    ext v
    change (fun i => α i v) = 0 ↔ _
    simpa only [funext_iff, Pi.zero_apply] using hfix v
  have hsurj : Function.Surjective (LinearMap.pi α) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have hrank := (LinearMap.pi α).finrank_range_add_finrank_ker
    rw [hker, finrank_span_singleton hx0, hdim] at hrank
    simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, mul_one] using Nat.add_right_cancel hrank
  exact exists_cartan_fixed_axis_coordinates h α x hx hsurj hker

end CFSG.LinearAlgebra
