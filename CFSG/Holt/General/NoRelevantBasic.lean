module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
import CFSG.Assembly.ComponentTypeDefs
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.Holt.General.NoRelevant

open MulAction Subgroup CFSG.ABGLocalTools

section Cores

variable {X : Type*} [Group X] [Finite X]

theorem generalizedFitting_normal : (generalizedFitting X).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := X)
  have : (fittingSubgroup X).Normal := (CFSG.LocalCores.fitting_nilpotent (G := X)).2.1
  simp only [CFSG.generalizedFitting.eq_sup]
  infer_instance

theorem isSylowOf_map {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] {P K : Subgroup X}
    (h : IsSylowOf p P K) (f : X →* Y) : IsSylowOf p (P.map f) (K.map f) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, map_map, map_map]
  rfl

end Cores

section Normalizers

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_map {M : Subgroup G} (K : Subgroup M) [K.Characteristic] :
    normalizer (M : Set G) ≤ normalizer (K.map M.subtype : Set G) := by
  have key : ∀ g ∈ normalizer (M : Set G), ∀ x ∈ K.map M.subtype,
      g * x * g⁻¹ ∈ K.map M.subtype := by
    rintro g hg _ ⟨k, hk, rfl⟩
    set φ : MulAut M := M.normalizerMonoidHom ⟨g, hg⟩
    have hφ : K.map φ.toMonoidHom = K := characteristic_iff_map_eq.mp inferInstance φ
    have hk' : φ k ∈ K := by
      rw [← hφ]
      exact ⟨k, hk, rfl⟩
    exact ⟨φ k, hk', rfl⟩
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

end Normalizers

end CFSG.Holt.General.NoRelevant
