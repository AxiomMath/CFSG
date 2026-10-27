module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finset.Attr

public section

namespace CFSG.OddStandard.SmallF3.Omega

theorem sec5la_exists_induced_aut {A P : Type} [Group A] [Group P] {ρ : A →* P}
    (hρ : Function.Surjective ρ) (σ : MulAut A) (hker : ∀ n : A, n ∈ ρ.ker ↔ σ n ∈ ρ.ker) :
    ∃ α : MulAut P, (∀ a : A, ρ (σ a) = α (ρ a)) ∧ ∀ n : ℕ, σ ^ n = 1 → α ^ n = 1 := by
  have hk : ρ.ker ≤ (ρ.comp σ.toMonoidHom).ker := fun n hn => (hker n).mp hn
  let α₀ : P →* P := ρ.liftOfSurjective hρ ⟨ρ.comp σ.toMonoidHom, hk⟩
  have hα₀ : ∀ a : A, α₀ (ρ a) = ρ (σ a) := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ρ.comp σ.toMonoidHom, hk⟩ a
  have hσinv : ∀ a : A, σ (σ⁻¹ a) = a := fun a => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hσinv' : ∀ a : A, σ⁻¹ (σ a) = a := fun a => by
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hk' : ρ.ker ≤ (ρ.comp σ⁻¹.toMonoidHom).ker := fun n hn =>
    (hker (σ⁻¹ n)).mpr (by rw [hσinv]; exact hn)
  let β₀ : P →* P := ρ.liftOfSurjective hρ ⟨ρ.comp σ⁻¹.toMonoidHom, hk'⟩
  have hβ₀ : ∀ a : A, β₀ (ρ a) = ρ (σ⁻¹ a) := fun a =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨ρ.comp σ⁻¹.toMonoidHom, hk'⟩ a
  have hαβ : ∀ p : P, α₀ (β₀ p) = p := by
    intro p
    obtain ⟨a, rfl⟩ := hρ p
    rw [hβ₀, hα₀, hσinv]
  have hβα : ∀ p : P, β₀ (α₀ p) = p := by
    intro p
    obtain ⟨a, rfl⟩ := hρ p
    rw [hα₀, hβ₀, hσinv']
  let α : MulAut P :=
    { toFun := α₀
      invFun := β₀
      left_inv := hβα
      right_inv := hαβ
      map_mul' := map_mul α₀ }
  refine ⟨α, fun a => (hα₀ a).symm, ?_⟩
  have hpow : ∀ m : ℕ, ∀ a : A, (α ^ m) (ρ a) = ρ ((σ ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; simp
    | succ m ih =>
        intro a
        rw [pow_succ, MulAut.mul_apply]
        change (α ^ m) (α₀ (ρ a)) = ρ ((σ ^ m) (σ a))
        rw [hα₀, ih]
  intro n hn
  ext p
  obtain ⟨a, rfl⟩ := hρ p
  rw [hpow n a, hn, MulAut.one_apply, MulAut.one_apply]

end CFSG.OddStandard.SmallF3.Omega
