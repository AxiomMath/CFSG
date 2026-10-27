module

public import CFSG.CGT.PushingUpLit.CGT6.Diag.Defs
public import CFSG.CGT.PushingUpLit.CGT6.Diag.BoundBasic

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Diag.Bound

open CFSG.Quasithin

theorem exists_threeCycle_range {m : ℕ} (hm : 3 ≤ m) :
    ∃ c : alternatingGroup (Fin m), orderOf c = 3 ∧
      Nat.card (Set.range (fun v : Fin m → ZMod 2 =>
        fun i => v ((c : Equiv.Perm (Fin m))⁻¹ i) - v i)) ≤ 4 := by
  classical
  let a0 : Fin m := ⟨0, by omega⟩
  let a1 : Fin m := ⟨1, by omega⟩
  let a2 : Fin m := ⟨2, by omega⟩
  have h01 : a0 ≠ a1 := by simp [a0, a1, Fin.ext_iff]
  have h02 : a0 ≠ a2 := by simp [a0, a2, Fin.ext_iff]
  have h12 : a1 ≠ a2 := by simp [a1, a2, Fin.ext_iff]
  have h3 : (Equiv.swap a0 a1 * Equiv.swap a0 a2).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same h01 h02 h12
  refine ⟨⟨Equiv.swap a0 a1 * Equiv.swap a0 a2, Equiv.Perm.mem_alternatingGroup.mpr h3.sign⟩,
    ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe]
    exact h3.orderOf
  · have hinv : ((Equiv.swap a0 a1 * Equiv.swap a0 a2)⁻¹ : Equiv.Perm (Fin m)) =
        Equiv.swap a0 a2 * Equiv.swap a0 a1 := by
      rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
    have e0 : (Equiv.swap a0 a2 * Equiv.swap a0 a1) a0 = a1 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h01.symm h12]
    have e1 : (Equiv.swap a0 a2 * Equiv.swap a0 a1) a1 = a2 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
    have e2 : (Equiv.swap a0 a2 * Equiv.swap a0 a1) a2 = a0 := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h02.symm h12.symm,
        Equiv.swap_apply_right]
    have ei : ∀ i : Fin m, 3 ≤ i.val → (Equiv.swap a0 a2 * Equiv.swap a0 a1) i = i := by
      intro i hi
      have n0 : i ≠ a0 := fun h => by simp [h, a0] at hi
      have n1 : i ≠ a1 := fun h => by simp [h, a1] at hi
      have n2 : i ≠ a2 := fun h => by simp [h, a2] at hi
      simp [Equiv.swap_apply_of_ne_of_ne, n0, n1, n2]
    simp only [hinv]
    let Φ : Set.range (fun v : Fin m → ZMod 2 =>
        fun i => v ((Equiv.swap a0 a2 * Equiv.swap a0 a1) i) - v i) → ZMod 2 × ZMod 2 :=
      fun w => (w.1 a0, w.1 a1)
    have hΦ : Function.Injective Φ := by
      rintro ⟨_, v, rfl⟩ ⟨_, v', rfl⟩ h
      simp only [Φ, Prod.mk.injEq, e0, e1] at h
      obtain ⟨h0, h1⟩ := h
      refine Subtype.ext (funext fun i => ?_)
      simp only
      by_cases hi : i = a0
      · subst hi
        simpa [e0] using h0
      by_cases hi1 : i = a1
      · subst hi1
        simpa [e1] using h1
      by_cases hi2 : i = a2
      · subst hi2
        rw [e2]
        linear_combination -h0 - h1
      · have : 3 ≤ i.val := by
          have h0' : i.val ≠ 0 := fun h => hi (Fin.ext h)
          have h1' : i.val ≠ 1 := fun h => hi1 (Fin.ext h)
          have h2' : i.val ≠ 2 := fun h => hi2 (Fin.ext h)
          omega
        simp [ei i this]
    have := Nat.card_le_card_of_injective Φ hΦ
    rw [Nat.card_prod, Nat.card_zmod] at this
    simpa using this

end CFSG.CGT.PushingUpLit.CGT6.Diag.Bound

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

theorem diagBoundAlt_holds : DiagBoundAlt := by
  intro V _ _ hV Y m hm5 _ hnat
  obtain ⟨hinv, θ, β, -, hβk, hβe⟩ := hnat
  obtain ⟨c, hc3, hcard⟩ := Diag.Bound.exists_threeCycle_range (m := m) (by omega)
  obtain ⟨y, hyθ⟩ : ∃ y : ↥Y, θ y = c := ⟨θ.symm c, θ.apply_symm_apply c⟩
  have hord : orderOf (y : MulAut V) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ y, hyθ]
    exact hc3
  refine ⟨(y : MulAut V), y.2, hord, ?_⟩
  have hodd : Odd (orderOf (y : MulAut V)) := by
    rw [hord]
    decide
  have hle : commV (Subgroup.zpowers (y : MulAut V)) ≤ commV Y :=
    Diag.Bound.commV_zpowers_le y.2
  have hinj := Diag.Bound.injective_comp_inclusion hV y.2 hodd (Z := commV Y ⊓ fixV Y)
    inf_le_right β hβk
  have hmem : ∀ r : ↥(commV (Subgroup.zpowers (y : MulAut V))),
      Multiplicative.toAdd ((β (Subgroup.inclusion hle r) : ↥(Quasithin.G6.coreMod m)) :
        Quasithin.G6.PermMod m) ∈ Set.range (fun v : Fin m → ZMod 2 =>
          fun i => v ((c : Equiv.Perm (Fin m))⁻¹ i) - v i) := by
    intro r
    obtain ⟨u, hu, hur⟩ := Diag.Bound.exists_comm_eq hV hodd r.2
    let uU : ↥(commV Y) := ⟨u, hle hu⟩
    have hyu : (y : MulAut V) u ∈ commV Y := hinv y y.2 u uU.2
    have h1 : Subgroup.inclusion hle r = ⟨(y : MulAut V) u, hyu⟩ * uU⁻¹ := Subtype.ext hur.symm
    have h2 : β ⟨(y : MulAut V) u, hyu⟩ = altAct m c (β uU) := by
      have h := hβe y uU hyu
      rw [hyθ] at h
      exact h
    have h3 : β (Subgroup.inclusion hle r) = altAct m c (β uU) * (β uU)⁻¹ := by
      rw [h1, map_mul, map_inv, h2]
      rfl
    refine ⟨Multiplicative.toAdd ((β uU : ↥(Quasithin.G6.coreMod m)) : Quasithin.G6.PermMod m),
      ?_⟩
    funext i
    rw [h3]
    simp [altAct, Quasithin.G6.coreAct_coe, Quasithin.G6.permAct_apply, sub_eq_add_neg]
  let π : ↥(commV (Subgroup.zpowers (y : MulAut V))) → Set.range (fun v : Fin m → ZMod 2 =>
      fun i => v ((c : Equiv.Perm (Fin m))⁻¹ i) - v i) := fun r => ⟨_, hmem r⟩
  have hπ : Function.Injective π := by
    intro a b hab
    have h : (π a).1 = (π b).1 := congrArg Subtype.val hab
    have h' : Multiplicative.toAdd ((β (Subgroup.inclusion hle a) : ↥(Quasithin.G6.coreMod m)) :
        Quasithin.G6.PermMod m) = Multiplicative.toAdd ((β (Subgroup.inclusion hle b) :
          ↥(Quasithin.G6.coreMod m)) : Quasithin.G6.PermMod m) := h
    exact hinj (Subtype.ext (Multiplicative.toAdd.injective h'))
  exact (Nat.card_le_card_of_injective π hπ).trans hcard

end CFSG.CGT.PushingUpLit.CGT6
