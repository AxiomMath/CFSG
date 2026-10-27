module

public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Orbit

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.RootAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag}

theorem corootPair_sum {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) (u : ι → Fin τ.rank → ℤ) :
    corootPair β (∑ i ∈ s, c i • u i) = ∑ i ∈ s, c i * corootPair β (u i) := by
  have hp := iform_self_pos_of_isRoot hβ
  have h1 := corootPair_mul hβ (∑ i ∈ s, c i • u i)
  have h2 : (∑ i ∈ s, c i * corootPair β (u i)) * iform β β =
      2 * iform β (∑ i ∈ s, c i • u i) := by
    rw [iform_finset_sum_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iform_smul_right, mul_assoc, corootPair_mul hβ]
    ring
  exact mul_right_cancel₀ hp.ne' (h1.trans h2.symm)

variable {Ψ : Set (Fin τ.rank → ℤ)} {n : ℕ}

@[expose] def liftCoeff (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) :
    (Fin τ.rank → ℤ) → ℤ :=
  fun β => if h : β ∈ simpleRoots Ψ then x (e ⟨β, h⟩) else 0

@[expose] def rootLift (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) : Fin τ.rank → ℤ :=
  ∑ β ∈ simpleRoots Ψ, liftCoeff e x β • β

theorem sum_liftCoeff (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) (g : (Fin τ.rank → ℤ) → ℤ) :
    ∑ β ∈ simpleRoots Ψ, liftCoeff e x β * g β = ∑ j, x j * g (e.symm j) := by
  rw [← Finset.sum_coe_sort (simpleRoots Ψ)]
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [liftCoeff]

theorem liftCoeff_single (e : simpleRoots Ψ ≃ Fin n) (i : Fin n) :
    liftCoeff e (Pi.single i 1) = unitCoords (e.symm i : Fin τ.rank → ℤ) := by
  funext β
  by_cases h : β ∈ simpleRoots Ψ
  · simp only [liftCoeff, h, ↓reduceDIte, unitCoords]
    by_cases hb : β = (e.symm i : Fin τ.rank → ℤ)
    · have : e ⟨β, h⟩ = i := by
        rw [show (⟨β, h⟩ : simpleRoots Ψ) = e.symm i from Subtype.ext hb, Equiv.apply_symm_apply]
      rw [this, Pi.single_eq_same, ite_eq_left hb]
    · have : e ⟨β, h⟩ ≠ i := fun h' => hb (by rw [← h', Equiv.symm_apply_apply])
      rw [Pi.single_eq_of_ne this, ite_eq_right hb]
  · have hb : β ≠ (e.symm i : Fin τ.rank → ℤ) := fun hb => h (hb ▸ (e.symm i).2)
    simp [liftCoeff, h, unitCoords, hb]

theorem rootLift_single (e : simpleRoots Ψ ≃ Fin n) (i : Fin n) :
    rootLift e (Pi.single i 1) = (e.symm i : Fin τ.rank → ℤ) := by
  rw [rootLift, liftCoeff_single, sum_unitCoords (e.symm i).2]

theorem liftCoeff_sub_smul (e : simpleRoots Ψ ≃ Fin n) (x : Fin n → ℤ) (c : ℤ) (i : Fin n) :
    liftCoeff e (x - c • Pi.single i 1) = liftCoeff e x - c • liftCoeff e (Pi.single i 1) := by
  funext β
  by_cases h : β ∈ simpleRoots Ψ <;> simp [liftCoeff, h]

theorem rootLift_coordReflect (e : simpleRoots Ψ ≃ Fin n) {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    (i : Fin n) (x : Fin n → ℤ) :
    rootLift e (coordReflect M i x) =
      rootReflection (e.symm i : Fin τ.rank → ℤ) • rootLift e x := by
  have hβ : IsRoot τ (e.symm i : Fin τ.rank → ℤ) := simpleRoots_isRoot (e.symm i).2
  have hpair : corootPair (e.symm i : Fin τ.rank → ℤ) (rootLift e x) = ∑ j, M i j * x j := by
    rw [rootLift, corootPair_sum hβ, sum_liftCoeff]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [he, Equiv.apply_symm_apply, Equiv.apply_symm_apply, mul_comm]
  rw [rootReflection_smul hβ, hpair, coordReflect, rootLift, rootLift, liftCoeff_sub_smul]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib,
    mul_smul]
  rw [← Finset.smul_sum, liftCoeff_single, sum_unitCoords (e.symm i).2]

theorem rootLift_injective (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin n) :
    Function.Injective (rootLift e) := by
  intro x y hxy
  have h := coords_unique hΨ hxy
  funext j
  have hj := h (e.symm j) (e.symm j).2
  simpa [liftCoeff] using hj

theorem rootLift_mem (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ))
    {x : Fin n → ℤ} (hx : IsOrbitRoot M x) : rootLift e x ∈ Ψ := by
  induction hx with
  | single i =>
    rw [rootLift_single]
    exact simpleRoots_subset (e.symm i).2
  | reflect i _ ih =>
    rw [rootLift_coordReflect e he]
    exact hΨ.reflection_mem _ ih _ (simpleRoots_subset (e.symm i).2)

theorem image_rootLift_orbit (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ)) :
    rootLift e '' {x | IsOrbitRoot M x} = Ψ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact rootLift_mem hΨ e he hx
  · intro γ hγ
    obtain ⟨w, hw, β, hβ, rfl⟩ := exists_smul_simpleRoot hΨ hγ
    set S := rootLift e '' {x | IsOrbitRoot M x} with hS
    have hSΨ : S ⊆ Ψ := by
      rintro _ ⟨x, hx, rfl⟩
      exact rootLift_mem hΨ e he hx
    have hSr : ∀ δ ∈ simpleRoots Ψ, ∀ α ∈ S, rootReflection δ • α ∈ S := by
      rintro δ hδ _ ⟨x, hx, rfl⟩
      refine ⟨coordReflect M (e ⟨δ, hδ⟩) x, IsOrbitRoot.reflect _ hx, ?_⟩
      rw [rootLift_coordReflect e he, Equiv.symm_apply_apply]
    have hβS : β ∈ S := ⟨Pi.single (e ⟨β, hβ⟩) 1, IsOrbitRoot.single _, by
      rw [rootLift_single, Equiv.symm_apply_apply]⟩
    exact smul_mem_of_forall_rootReflection hΨ hSΨ hSr hw β hβS

theorem ncard_eq_ncard_orbit (hΨ : IsRootComponent Ψ) (e : simpleRoots Ψ ≃ Fin n)
    {M : Matrix (Fin n) (Fin n) ℤ}
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ = M (e β) (e γ)) :
    Ψ.ncard = {x | IsOrbitRoot M x}.ncard := by
  rw [← image_rootLift_orbit hΨ e he, Set.ncard_image_of_injective _ (rootLift_injective hΨ e)]

end CFSG.HardMathSupport.Timmesfeld.RootAut
