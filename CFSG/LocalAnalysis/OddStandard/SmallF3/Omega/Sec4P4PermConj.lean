module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4P4Alt

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Equiv Equiv.Perm

variable {n : ℕ} {N : Type*} [Group N]

theorem sec4P4_perm_conj_section (hn : 3 ≤ n) (π : N →* Perm (Fin n))
    (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    {σ : alternatingGroup (Fin n) →* N} (hσ : ∀ a, π (σ a) = a) (m : N)
    (a b : alternatingGroup (Fin n)) (hab : (b : Perm (Fin n)) = π m * a * (π m)⁻¹) :
    m * σ a * m⁻¹ = σ b := by
  let σ' : alternatingGroup (Fin n) →* N :=
    (MulAut.conj m⁻¹).toMonoidHom.comp
      (σ.comp (MulAut.conjNormal (π m)).toMonoidHom)
  have hπσ' : ∀ a, π (σ' a) = a := by
    intro a
    have h1 : σ' a = m⁻¹ * σ (MulAut.conjNormal (π m) a) * m := by simp [σ']
    rw [h1]
    simp only [map_mul, map_inv, hσ (MulAut.conjNormal (π m) a), MulAut.conjNormal_apply]
    group
  have hσ' : σ' = σ :=
    sec4P4_alt_hom_eq hn π hC h2 (fun a => (hπσ' a).trans (hσ a).symm)
  have heval : σ' a = σ a := DFunLike.congr_fun hσ' a
  have hca : MulAut.conjNormal (π m) a = b := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hab]
  have heq : m⁻¹ * σ b * m = σ a := by
    have h1 : σ' a = m⁻¹ * σ (MulAut.conjNormal (π m) a) * m := by simp [σ']
    rw [hca] at h1
    exact h1.symm.trans heval
  rw [← heq]
  group

theorem sec4P4_perm_range_normal (hn : 3 ≤ n) (π : N →* Perm (Fin n))
    (hC : π.ker ≤ Subgroup.center N) (h2 : ∀ k ∈ π.ker, k ^ 2 = 1)
    {σ : alternatingGroup (Fin n) →* N} (hσ : ∀ a, π (σ a) = a) : σ.range.Normal := by
  refine ⟨fun k hk m => ?_⟩
  rcases hk with ⟨a, rfl⟩
  refine ⟨⟨π m * a * (π m)⁻¹, (alternatingGroup.normal).conj_mem a a.2 (π m)⟩, ?_⟩
  exact (sec4P4_perm_conj_section hn π hC h2 hσ m a _ rfl).symm

end CFSG.OddStandard.SmallF3.Omega
