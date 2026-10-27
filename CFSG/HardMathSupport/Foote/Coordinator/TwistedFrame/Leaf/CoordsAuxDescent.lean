module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.CoordsAuxLang

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

set_option linter.unusedSectionVars false


namespace CoordsAux

section Lang

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

theorem desc {x : ModGL τ D.L} (hx : x ∈ Qθ τ D.L) :
    heisCoord τ D.L (D.g⁻¹ * x * D.g) ∈
      Submodule.span D.L (κ D '' (Qθ τ K : Set (ModGL τ K))) := by
  set 𝒮 := Submodule.span D.L (κ D '' (Qθ τ K : Set (ModGL τ K))) with h𝒮
  have hconj : ∀ y ∈ Qθ τ D.L, D.g⁻¹ * y * D.g ∈ Qθ τ D.L := by
    intro y hy
    have := Lθ_conj_mem_Qθ (inv_mem D.g_mem) hy
    rwa [inv_inv] at this
  have hconjU : ∀ y ∈ Uθ τ D.L, D.g⁻¹ * y * D.g ∈ Uθ τ D.L := by
    intro y hy
    have := Lθ_conj_mem_Uθ (inv_mem D.g_mem) hy
    rwa [inv_inv] at this
  have hg1 : D.g⁻¹ * (1 : ModGL τ D.L) * D.g = 1 := by group
  refine Qθ_induction (P := fun y => heisCoord τ D.L (D.g⁻¹ * y * D.g) ∈ 𝒮) ?_ ?_ ?_ ?_ ?_ x hx
  · rw [hg1, heisCoord_one]
    exact zero_mem _
  · intro y z hy hz hPy hPz
    have e : D.g⁻¹ * (y * z) * D.g = (D.g⁻¹ * y * D.g) * (D.g⁻¹ * z * D.g) := by group
    rw [e, (heisCoord_spec τ D.L).mul _ (hconj y hy) _ (hconj z hz)]
    exact add_mem hPy hPz
  · intro y hy hPy
    have e : D.g⁻¹ * y⁻¹ * D.g = (D.g⁻¹ * y * D.g)⁻¹ := by group
    rw [e, heisCoord_inv (hconj y hy)]
    exact neg_mem hPy
  · intro β hβ t
    by_cases ht : t = 0
    · subst ht
      rw [pinnedX_zero, hg1, heisCoord_one]
      exact zero_mem _
    · obtain ⟨h, hcent, hh⟩ := CoordsAux.exists_scalarTorus_central (τ := τ) (F := D.L) ht
      have hx₁Q : pinnedX τ D.L β 1 ∈ Qθ τ D.L := pinnedX_mem_Qθ_of_mem_Deg1 hβ 1
      obtain ⟨hhQ, hhc⟩ := hh _ hx₁Q
      have hcoord : heisCoord τ D.L (pinnedX τ D.L β t) =
          heisCoord τ D.L (h * pinnedX τ D.L β 1 * h⁻¹) := by
        rw [hhc, (heisCoord_spec τ D.L).pinnedX_deg1 β hβ, (heisCoord_spec τ D.L).pinnedX_deg1 β hβ]
        funext γ
        by_cases hγ : γ = β
        · subst hγ
          simp
        · simp [Pi.single_apply, hγ]
      have hu : pinnedX τ D.L β t * (h * pinnedX τ D.L β 1 * h⁻¹)⁻¹ ∈ Uθ τ D.L :=
        mul_inv_mem_Uθ_of_coord_eq (pinnedX_mem_Qθ_of_mem_Deg1 hβ t) hhQ hcoord
      have hg : h * D.g = D.g * h := hcent D.g D.g_mem
      have hgi : h * D.g⁻¹ = D.g⁻¹ * h := hcent _ (inv_mem D.g_mem)
      have hg' : h⁻¹ * D.g = D.g * h⁻¹ := by
        calc h⁻¹ * D.g = h⁻¹ * (D.g * h) * h⁻¹ := by group
          _ = h⁻¹ * (h * D.g) * h⁻¹ := by rw [hg]
          _ = D.g * h⁻¹ := by group
      have e1 : D.g⁻¹ * (h * pinnedX τ D.L β 1 * h⁻¹) * D.g =
          h * (D.g⁻¹ * pinnedX τ D.L β 1 * D.g) * h⁻¹ := by
        calc D.g⁻¹ * (h * pinnedX τ D.L β 1 * h⁻¹) * D.g
            = (D.g⁻¹ * h) * pinnedX τ D.L β 1 * (h⁻¹ * D.g) := by group
          _ = (h * D.g⁻¹) * pinnedX τ D.L β 1 * (D.g * h⁻¹) := by rw [← hgi, hg']
          _ = h * (D.g⁻¹ * pinnedX τ D.L β 1 * D.g) * h⁻¹ := by group
      set u := pinnedX τ D.L β t * (h * pinnedX τ D.L β 1 * h⁻¹)⁻¹ with hu'
      have e2 : D.g⁻¹ * pinnedX τ D.L β t * D.g =
          (D.g⁻¹ * u * D.g) * (h * (D.g⁻¹ * pinnedX τ D.L β 1 * D.g) * h⁻¹) := by
        rw [← e1]
        calc D.g⁻¹ * pinnedX τ D.L β t * D.g
            = D.g⁻¹ * (u * (h * pinnedX τ D.L β 1 * h⁻¹)) * D.g := by rw [hu']; group
          _ = (D.g⁻¹ * u * D.g) * (D.g⁻¹ * (h * pinnedX τ D.L β 1 * h⁻¹) * D.g) := by group
      have hQ₁ : D.g⁻¹ * pinnedX τ D.L β 1 * D.g ∈ Qθ τ D.L := hconj _ hx₁Q
      obtain ⟨hhQ₂, hhc₂⟩ := hh _ hQ₁
      have hUQ : D.g⁻¹ * u * D.g ∈ Uθ τ D.L := hconjU _ hu
      rw [e2, (heisCoord_spec τ D.L).mul _ (Uθ_le_Qθ hUQ) _ hhQ₂,
        ((heisCoord_spec τ D.L).eq_zero_iff _ (Uθ_le_Qθ hUQ)).2 hUQ, zero_add, hhc₂]
      have hKQ : pinnedX τ K β 1 ∈ Qθ τ K := pinnedX_mem_Qθ_of_mem_Deg1 hβ 1
      have hκ : κ D (pinnedX τ K β 1) = heisCoord τ D.L (D.g⁻¹ * pinnedX τ D.L β 1 * D.g) := by
        unfold κ Ψ bc
        rw [baseChangeGL_pinnedX, map_one]
      rw [← hκ]
      exact Submodule.smul_mem 𝒮 t (Submodule.subset_span ⟨_, hKQ, rfl⟩)
  · intro t
    have hU : pinnedX τ D.L (highRoot τ) t ∈ Uθ τ D.L := mem_rootSubgroup.2 ⟨t, rfl⟩
    have hU' := hconjU _ hU
    rw [((heisCoord_spec τ D.L).eq_zero_iff _ (Uθ_le_Qθ hU')).2 hU']
    exact zero_mem _

end Lang

end CoordsAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
