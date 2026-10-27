module

public import CFSG.LargeExtraspecial.AS35YUSL4
public import CFSG.LargeExtraspecial.A2ModCfgTD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YU

open Module Matrix CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld.ARS A2Mod

open CFSG.Timmesfeld (edgeD)

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem finrank_commSpaceOf_levi_le_eight {Ψ : SpecialLinearGroup (Fin 4) (ZMod 2) →* X}
    {a b : X} (hA : A2Action D Q ρ) (h : IsLeviNode D Ψ a b) :
    finrank (ZMod 2) (commSpaceOf ρ (Ψ.range ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤
      8 := by
  obtain ⟨-, hA'⟩ := hA.comp_sl (by omega) h.map_mem
  rcases exists_isPointMaps_or_finrank_le_six hA' with ⟨P, Pd, hP⟩ | hle
  · rw [h.commSpaceOf_eq_of_isPointMaps hA rfl hP,
      finrank_range_sup_range_eq hP.injective hP.injective_dual hP.range_inf_range]
  · have h1 := h.finrank_commSpaceOf_le_add hA (by omega)
    rw [commSpaceOf_range] at h1
    omega

variable {R : Set (Subgroup X)}

theorem typeD_four_finrank_commSpaceOf_le_eight [Finite X] (hR : IsRootClass R)
    (hiso : NoIsolated R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
    (hDc : ∀ g, ∀ d ∈ D, g * d * g⁻¹ ∈ D) (hA : A2Action D Q ρ)
    (hX : HasGenConfig R (edgeD 4)) : finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 8 := by
  obtain ⟨A, B, hX, hgen⟩ := hX
  obtain ⟨Ψ, a, b, hL, htop⟩ :=
    exists_isLeviNode_of_isConfig_D (m := 3) hR hiso hRD hDc le_rfl hX hgen
  rw [← htop]
  exact finrank_commSpaceOf_levi_le_eight hA hL

end CFSG.LargeExtraspecial.AS35YU
