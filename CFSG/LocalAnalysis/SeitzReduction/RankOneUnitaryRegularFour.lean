module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryAffinePerm

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup Equiv

namespace DegreeFour

@[expose] def kleinSet : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinSet_mul : ∀ x ∈ kleinSet, ∀ y ∈ kleinSet, x * y ∈ kleinSet := by decide

theorem kleinSet_inv : ∀ x ∈ kleinSet, x⁻¹ ∈ kleinSet := by decide

theorem kleinSet_conj : ∀ g : Perm (Fin 4), ∀ x ∈ kleinSet, g * x * g⁻¹ ∈ kleinSet := by decide

theorem kleinSet_reg : ∀ x ∈ kleinSet, ∀ y ∈ kleinSet, ∀ a : Fin 4, x a = y a → x = y := by
  decide

theorem kleinSet_ex : ∀ a b : Fin 4, ∃ x ∈ kleinSet, x a = b := by decide

theorem kleinSet_sq : ∀ x ∈ kleinSet, ∃ y : Perm (Fin 4), y ^ 2 = x := by decide

@[expose] def klein : Subgroup (Perm (Fin 4)) where
  carrier := {x | x ∈ kleinSet}
  mul_mem' {x y} hx hy := kleinSet_mul x hx y hy
  one_mem' := by decide
  inv_mem' {x} hx := kleinSet_inv x hx

theorem mem_klein {x : Perm (Fin 4)} : x ∈ klein ↔ x ∈ kleinSet := Iff.rfl

theorem card_pairs : Nat.card {p : Fin 4 × Fin 4 // p.1 ≠ p.2} = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem klein_le {N : Subgroup (Perm (Fin 4))}
    (h2 : ∀ a b c d : Fin 4, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d) : klein ≤ N := by
  classical
  have hsel : ∀ p : {p : Fin 4 × Fin 4 // p.1 ≠ p.2}, ∃ x : N, (x : Perm (Fin 4)) 0 = p.1.1 ∧
      (x : Perm (Fin 4)) 1 = p.1.2 := fun p => by
    obtain ⟨x, hx, h0, h1⟩ := h2 0 1 p.1.1 p.1.2 (by decide) p.2
    exact ⟨⟨x, hx⟩, h0, h1⟩
  choose sel hsel0 hsel1 using hsel
  have hinj : Function.Injective sel := fun p p' hpp => by
    have e0 := hsel0 p
    have e1 := hsel1 p
    rw [hpp, hsel0 p'] at e0
    rw [hpp, hsel1 p'] at e1
    exact Subtype.ext (Prod.ext e0.symm e1.symm)
  have hcard : 12 ≤ Nat.card N := by
    rw [← card_pairs]
    exact Nat.card_le_card_of_injective sel hinj
  have htop : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hidx := N.card_mul_index
  rw [htop] at hidx
  have hidx2 : N.index = 1 ∨ N.index = 2 := by
    have hpos : 0 < N.index := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hidx; omega)
    have hle : N.index ≤ 2 := by
      by_contra hlt
      push Not at hlt
      have : 12 * 3 ≤ Nat.card N * N.index := Nat.mul_le_mul hcard hlt
      omega
    omega
  intro x hx
  rcases hidx2 with h1 | h2'
  · rw [index_eq_one.mp h1]
    exact mem_top x
  · obtain ⟨y, rfl⟩ := kleinSet_sq x hx
    exact sq_mem_of_index_two h2' y

theorem hasRegularNormalSubgroup_fin {N : Subgroup (Perm (Fin 4))}
    (h2 : ∀ a b c d : Fin 4, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d) :
    HasRegularNormalSubgroup N := by
  have hle := klein_le h2
  refine ⟨klein, hle, ⟨fun x hx g => ?_⟩, fun a b => ?_⟩
  · rw [mem_subgroupOf] at hx ⊢
    have h1 := kleinSet_conj (g : Perm (Fin 4)) _ hx
    rw [← mem_klein] at h1
    simpa using h1
  · obtain ⟨x, hx, hxab⟩ := kleinSet_ex a b
    refine ⟨⟨x, hx⟩, hxab, fun y hy => Subtype.ext ?_⟩
    exact kleinSet_reg _ y.2 x hx a (hy.trans hxab.symm)

end DegreeFour

open DegreeFour

theorem hasRegularNormalSubgroup_of_card_eq_four {Ω : Type*} [Finite Ω] (hΩ : Nat.card Ω = 4)
    {N : Subgroup (Perm Ω)} (h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ x ∈ N, x a = c ∧ x b = d) :
    HasRegularNormalSubgroup N := by
  obtain ⟨e⟩ : Nonempty (Ω ≃ Fin 4) := by
    rw [← Fintype.card_fin 4, ← Nat.card_eq_fintype_card] at hΩ
    exact Finite.card_eq.mp hΩ
  have h2' : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
      ∃ x ∈ N.map e.permCongrHom.toMonoidHom, x a = c ∧ x b = d := by
    intro a b c d hab hcd
    obtain ⟨x, hx, hxa, hxb⟩ := h2 (e.symm a) (e.symm b) (e.symm c) (e.symm d)
      (fun h => hab (e.symm.injective h)) (fun h => hcd (e.symm.injective h))
    refine ⟨e.permCongrHom x, mem_map_of_mem _ hx, ?_, ?_⟩
    · rw [permCongrHom_apply_apply, hxa, Equiv.apply_symm_apply]
    · rw [permCongrHom_apply_apply, hxb, Equiv.apply_symm_apply]
  have h := (hasRegularNormalSubgroup_fin h2').map_permCongr e.symm
  have e1 : (N.map e.permCongrHom.toMonoidHom).map e.symm.permCongrHom.toMonoidHom = N :=
    map_permCongrHom_symm_map e N
  rwa [e1] at h

end CFSG.SeitzReduction.RankOne
