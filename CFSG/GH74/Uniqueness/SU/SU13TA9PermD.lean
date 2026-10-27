module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.Uniqueness.SU.SU13TA9PermE
public import CFSG.GH74.Uniqueness.SU.SU13TA9PermS

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA.L9

open Equiv Equiv.Perm Subgroup

@[expose] def Dbar : Subgroup (alternatingGroup (Fin 9)) := Ebar ⊓ AS

theorem toP_k_zero : ∀ k : Fin 3, (pc ^ (k : ℕ)) 6 = 6 → k = 0 := by decide

theorem mem_Dbar_iff {x : alternatingGroup (Fin 9)} : x ∈ Dbar ↔ ∃ i j : Fin 3, x = toE i j 0 := by
  constructor
  · rintro ⟨hxE, hxA⟩
    obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hxE
    have h6 := (mem_AS_iff.mp hxA).1
    have hk : k = 0 := by
      refine toP_k_zero k ?_
      have := toP_apply_c i j k 6 (by decide)
      rw [← this]
      exact h6
    exact ⟨i, j, by rw [hk]⟩
  · rintro ⟨i, j, rfl⟩
    refine ⟨mem_Ebar_iff_toE.mpr ⟨i, j, 0, rfl⟩, mem_AS_iff.mpr ⟨?_, ?_, ?_⟩⟩ <;> decide +revert

theorem card_Dbar : Nat.card Dbar = 9 := by
  let f : Fin 3 × Fin 3 → Dbar := fun p => ⟨toE p.1 p.2 0, mem_Dbar_iff.mpr ⟨_, _, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      obtain ⟨h1, h2, -⟩ := toP_injective
        (congrArg (fun x : Dbar => ((x : alternatingGroup (Fin 9)) : Perm (Fin 9))) h)
      exact Prod.ext h1 h2
    · rintro ⟨x, hx⟩
      obtain ⟨i, j, rfl⟩ := mem_Dbar_iff.mp hx
      exact ⟨(i, j), rfl⟩
  rw [← Nat.card_eq_of_bijective f hf]
  simp

theorem pc_inv_mul_toP : ∀ i j k : Fin 3, (pc ^ (k : ℕ))⁻¹ * toP i j k = toP i j 0 := by decide

theorem toE_mem_Dbar (i j : Fin 3) : toE i j 0 ∈ Dbar := mem_Dbar_iff.mpr ⟨i, j, rfl⟩

theorem et_conj_mem_Dbar {x : alternatingGroup (Fin 9)} (hx : x ∈ Dbar) : et * x * et⁻¹ ∈ Dbar := by
  obtain ⟨i, j, rfl⟩ := mem_Dbar_iff.mp hx
  have : et * toE i j 0 * et⁻¹ = toE j i 0 := Subtype.ext (by
    have := pt_mul_toP i j 0
    simpa [toE, coe_et, neg_zero] using this)
  rw [this]
  exact toE_mem_Dbar j i

@[expose] def pr : Perm (Fin 9) := swap 0 3 * swap 1 4 * swap 4 2 * swap 2 5

theorem sign_pr : Perm.sign pr = 1 := by decide

@[expose] def er : alternatingGroup (Fin 9) := ⟨pr, Perm.mem_alternatingGroup.mpr sign_pr⟩

theorem coe_er : (er : Perm (Fin 9)) = pr := rfl

theorem er_mem_AS : er ∈ AS := mem_AS_iff.mpr ⟨by decide, by decide, by decide⟩

theorem er_sq : ((er ^ 2 : alternatingGroup (Fin 9)) : Perm (Fin 9)) = swap 1 2 * swap 4 5 := by
  rw [Subgroup.coe_pow]
  decide

theorem cycleType_er_sq : ((er ^ 2 : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2} := by
  rw [er_sq]
  exact cycleType_swap_mul_swap_of_nodup (by decide)

theorem er_sq_ne_one : er ^ 2 ≠ 1 := fun h => by
  have := congrArg (fun x : alternatingGroup (Fin 9) => (x : Perm (Fin 9))) h
  rw [er_sq] at this
  revert this
  decide

theorem et_mul_er : et * er * et⁻¹ = er⁻¹ := Subtype.ext (by decide)

theorem pr_mul_toP : ∀ i j k : Fin 3, pr * toP i j k * pr⁻¹ = toP (-j) i k := by decide

theorem er_conj_mem_Ebar {x : alternatingGroup (Fin 9)} (hx : x ∈ Ebar) : er * x * er⁻¹ ∈ Ebar := by
  obtain ⟨i, j, k, rfl⟩ := mem_Ebar_iff_toE.mp hx
  have : er * toE i j k * er⁻¹ = toE (-j) i k := Subtype.ext (by
    have := pr_mul_toP i j k
    simpa [toE, coe_er] using this)
  rw [this]
  exact mem_Ebar_iff_toE.mpr ⟨_, _, _, rfl⟩

theorem er_conj_mem_Dbar {x : alternatingGroup (Fin 9)} (hx : x ∈ Dbar) : er * x * er⁻¹ ∈ Dbar :=
  ⟨er_conj_mem_Ebar hx.1, AS.mul_mem (AS.mul_mem er_mem_AS hx.2) (AS.inv_mem er_mem_AS)⟩

end CFSG.GH74.Uniqueness.SU.SU13.TA.L9
