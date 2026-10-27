module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Layer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem l515S_conj_inv {X : Subgroup G} {g : G} (h : CFSG.conjugate X g = X) :
    CFSG.conjugate X g⁻¹ = X := by
  calc CFSG.conjugate X g⁻¹ = CFSG.conjugate (CFSG.conjugate X g) g⁻¹ := by rw [h]
    _ = CFSG.conjugate X (g * g⁻¹) := sec5b517_conjugate_conjugate X g g⁻¹
    _ = X := by rw [mul_inv_cancel]; exact sec5b517_conjugate_one X

theorem l515S_conj_triple {X : Subgroup G} {g h : G} (hX : CFSG.conjugate X g = X)
    (hXh : CFSG.conjugate (CFSG.conjugate X h) g = CFSG.conjugate X h) :
    CFSG.conjugate X (g⁻¹ * h * g) = CFSG.conjugate X h := by
  calc CFSG.conjugate X (g⁻¹ * h * g) = CFSG.conjugate (CFSG.conjugate X (g⁻¹ * h)) g :=
        (sec5b517_conjugate_conjugate X (g⁻¹ * h) g).symm
    _ = CFSG.conjugate (CFSG.conjugate (CFSG.conjugate X g⁻¹) h) g := by
        rw [← sec5b517_conjugate_conjugate X g⁻¹ h]
    _ = CFSG.conjugate (CFSG.conjugate X h) g := by rw [l515S_conj_inv hX]
    _ = CFSG.conjugate X h := hXh

theorem l515S_kfam_eq {K₁ K₂ : Subgroup G} {h h' : G}
    (h1 : CFSG.conjugate K₁ h' = CFSG.conjugate K₁ h)
    (h2 : CFSG.conjugate K₂ h' = CFSG.conjugate K₂ h) : Kfam5 K₁ K₂ h' = Kfam5 K₁ K₂ h := by
  unfold Kfam5
  rw [h1, h2]

theorem l515S_kfam_mem_gamma (K₁ K₂ : Subgroup G) (h : G) (a : Fin 4) :
    Kfam5 K₁ K₂ h a ∈ Gamma5 K₁ K₂ h := by
  fin_cases a <;> simp [Kfam5, Gamma5]

theorem l515S_gamma_mem {K₁ K₂ P : Subgroup G} {h : G} (hP : P ∈ Gamma5 K₁ K₂ h) :
    ∃ a : Fin 4, P = Kfam5 K₁ K₂ h a := by
  simp only [Gamma5, Set.mem_insert_iff, Set.mem_singleton_iff] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact ⟨0, by simp [Kfam5]⟩
  · exact ⟨1, by simp [Kfam5]⟩
  · exact ⟨2, by simp [Kfam5]⟩
  · exact ⟨3, by simp [Kfam5]⟩

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem l515S_ctx_fix (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {g : G} (hgz : g⁻¹ * z * g = z)
    (hgK : ∀ l : Fin 4, CFSG.conjugate (Kfam5 K₁ K₂ h l) g = Kfam5 K₁ K₂ h l) :
    Sec5HCtx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) z (g⁻¹ * r * g)
        (CFSG.conjugate B g) (CFSG.conjugate A g) K₁ K₂ (g⁻¹ * h * g) ∧
      CFSG.conjugate K₁ (g⁻¹ * h * g) = CFSG.conjugate K₁ h ∧
      CFSG.conjugate K₂ (g⁻¹ * h * g) = CFSG.conjugate K₂ h := by
  have hK0 : CFSG.conjugate K₁ g = K₁ := by simpa [Kfam5] using hgK 0
  have hK1 : CFSG.conjugate K₂ g = K₂ := by simpa [Kfam5] using hgK 1
  have hK2 : CFSG.conjugate (CFSG.conjugate K₁ h) g = CFSG.conjugate K₁ h := by
    simpa [Kfam5] using hgK 2
  have hK3 : CFSG.conjugate (CFSG.conjugate K₂ h) g = CFSG.conjugate K₂ h := by
    simpa [Kfam5] using hgK 3
  refine ⟨?_, l515S_conj_triple hK0 hK2, l515S_conj_triple hK1 hK3⟩
  have := sec5HCtx_conj c g
  rwa [hgz, hK0, hK1] at this

end Ctx

end CFSG.OddStandard.SmallF3.Omega
