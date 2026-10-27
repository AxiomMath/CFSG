module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Defs
public import Mathlib.LinearAlgebra.DFinsupp

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

open Equiv

@[expose] def permW (σ : Perm (Fin 24)) : Word ≃ₗ[ZMod 2] Word :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) σ⁻¹

@[simp] theorem permW_apply (σ : Perm (Fin 24)) (v : Word) (i : Fin 24) :
    permW σ v i = v (σ⁻¹ i) := rfl

theorem permW_mul (σ τ : Perm (Fin 24)) (v : Word) :
    permW (σ * τ) v = permW σ (permW τ v) := rfl

theorem permW_one (v : Word) : permW 1 v = v := rfl

theorem permW_permW_inv (σ : Perm (Fin 24)) (v : Word) : permW σ (permW σ⁻¹ v) = v := by
  ext i
  simp

theorem permW_single (σ : Perm (Fin 24)) (i : Fin 24) :
    permW σ (Pi.single i 1) = Pi.single (σ i) 1 := by
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

@[expose] def aut : Subgroup (Perm (Fin 24)) where
  carrier := {σ | ∀ v, permW σ v ∈ golay ↔ v ∈ golay}
  mul_mem' := by
    intro σ τ hσ hτ v
    rw [permW_mul, hσ, hτ]
  one_mem' := fun v => Iff.rfl
  inv_mem' := by
    intro σ hσ v
    rw [← hσ (permW σ⁻¹ v), permW_permW_inv]

theorem mem_aut_iff (σ : Perm (Fin 24)) :
    σ ∈ aut ↔ ∀ v, permW σ v ∈ golay ↔ v ∈ golay := Iff.rfl

@[expose] def act (σ : Perm (Fin 24)) : Syn →ₗ[ZMod 2] Syn :=
  ∑ j, (LinearMap.proj j : Syn →ₗ[ZMod 2] ZMod 2).smulRight (col (σ (pivot j)))

theorem act_apply (σ : Perm (Fin 24)) (s : Syn) : act σ s = ∑ j, s j • col (σ (pivot j)) := by
  simp [act, LinearMap.sum_apply]

theorem act_single (σ : Perm (Fin 24)) (j : Fin 12) :
    act σ (Pi.single j 1) = col (σ (pivot j)) := by
  rw [act_apply]
  simp [Pi.single_apply]

theorem sum_smul_col_pivot (s : Syn) : ∑ j, s j • col (pivot j) = s := by
  ext k
  simp [col_pivot, Finset.sum_apply, Pi.single_apply]

theorem act_col {σ : Perm (Fin 24)} (hσ : σ ∈ aut) (i : Fin 24) :
    act σ (col i) = col (σ i) := by
  set r : Word := Pi.single i 1 - ∑ k, col i k • Pi.single (pivot k) 1 with hr
  have h1 : synd r = 0 := by
    simp only [hr, map_sub, map_sum, map_smul, synd_single, col_pivot]
    rw [sub_eq_zero]
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : permW σ r ∈ golay := (hσ r).2 h1
  have h3 : synd (permW σ r) = 0 := h2
  simp only [hr, map_sub, map_sum, map_smul, permW_single, synd_single] at h3
  rw [sub_eq_zero] at h3
  rw [act_apply, h3]

theorem act_mul {σ τ : Perm (Fin 24)} (hσ : σ ∈ aut) (hτ : τ ∈ aut) :
    act (σ * τ) = (act σ).comp (act τ) := by
  refine LinearMap.pi_ext fun j x => ?_
  have hx : (Pi.single j x : Syn) = x • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_smul, map_smul, LinearMap.comp_apply, ← col_pivot, act_col (mul_mem hσ hτ),
    act_col hτ, act_col hσ]
  rfl

theorem act_one : act 1 = LinearMap.id := by
  refine LinearMap.pi_ext fun j x => ?_
  have hx : (Pi.single j x : Syn) = x • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  rw [hx, map_smul, act_single]
  simp [col_pivot]

@[expose] def actEquiv {σ : Perm (Fin 24)} (hσ : σ ∈ aut) : Syn ≃ₗ[ZMod 2] Syn :=
  LinearEquiv.ofLinearMap (act σ) (act σ⁻¹)
    (by rw [← act_mul hσ (inv_mem hσ), mul_inv_cancel, act_one])
    (by rw [← act_mul (inv_mem hσ) hσ, inv_mul_cancel, act_one])

@[expose] def actHom : aut →* (Syn ≃ₗ[ZMod 2] Syn) where
  toFun σ := actEquiv σ.2
  map_one' := LinearEquiv.ext fun s => by
    show act 1 s = s
    rw [act_one]
    rfl
  map_mul' σ τ := LinearEquiv.ext fun s => by
    show act (σ * τ : Perm (Fin 24)) s = act σ (act τ s)
    rw [act_mul σ.2 τ.2]
    rfl

theorem actHom_apply (σ : aut) (s : Syn) : actHom σ s = act σ s := rfl

theorem actHom_injective : Function.Injective actHom := by
  intro σ τ h
  apply Subtype.ext
  ext i
  have h1 : act σ (col i) = act τ (col i) := by
    have := congrArg (fun f : Syn ≃ₗ[ZMod 2] Syn => f (col i)) h
    exact this
  rw [act_col σ.2, act_col τ.2] at h1
  exact congrArg Fin.val (col_injective h1)

end CFSG.EvenSporadicStandard.Induction.Balance.Cocode24
