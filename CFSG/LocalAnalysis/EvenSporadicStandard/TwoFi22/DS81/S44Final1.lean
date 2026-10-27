module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Glue3
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Spine

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open Subgroup CFSG.Sporadic.Fi23 CFSG.Blueprint.NativeSporadic CFSG.EvenSmallLie CFSG.Quasithin
open CFSG.EvenSmallLie.UnitarySix S44

set_option linter.unusedSectionVars false


theorem stage44'_core {X : Type} [Group X] {E0 : Subgroup X} {d : X} {O : Fin 5 → Set X}
    (hMain : S44.CocodeMainStmt) (M0 : LocalModel X E0) (F0 : FrameModel X E0 d O)
    (hiso : ∀ (Λ : Type) [Group Λ], CFSG.Open.IsQuasisimple Λ → Nat.card (center Λ) = 2 →
      IsSporadic (Λ ⧸ center Λ) .Fi22 → ∀ τ ∈ center Λ, τ ≠ 1 → ∃ ψ : Λ ≃* X, ψ τ = d) :
    Stage44' := by
  intro G _ _ L h h2 hQ t ht hne
  have ht2 : orderOf t = 2 := orderOf_eq_two_of_center h2 ht
  have htZ : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  obtain ⟨τ, hτc, hτt⟩ := htZ
  have hτ1 : τ ≠ 1 := by
    intro h1
    rw [h1] at hτt
    have : t = 1 := hτt.symm
    rw [this, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  obtain ⟨ψ, hψτ⟩ := hiso L h.standard.1 h2 hQ τ hτc hτ1
  have M : LocalModel L (E0.map ψ.symm.toMonoidHom) := M0.of_mulEquiv ψ.symm
  have hιinj : Function.Injective (L.subtype.comp ψ.symm.toMonoidHom) :=
    Subtype.val_injective.comp ψ.symm.injective
  have hFG := F0.toG (L.subtype.comp ψ.symm.toMonoidHom) hιinj
  have hrange : (L.subtype.comp ψ.symm.toMonoidHom).range = L := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (ψ.symm c).2
    · intro hx
      exact ⟨ψ ⟨x, hx⟩, by simp⟩
  have hmap : E0.map (L.subtype.comp ψ.symm.toMonoidHom) =
      (E0.map ψ.symm.toMonoidHom).map L.subtype := by
    rw [Subgroup.map_map]
  have hz : (L.subtype.comp ψ.symm.toMonoidHom) d = t := by
    show ((ψ.symm d : L) : G) = t
    rw [← hψτ, MulEquiv.symm_apply_apply]
    exact hτt
  rw [hrange, hmap, hz] at hFG
  have htL : t ∈ L := by
    rw [← hτt]
    exact τ.2
  have htZ' : t ∈ (center L).map L.subtype := ht ▸ mem_zpowers t
  have hout := relIndex_sup_centralizer_le_two h hQ
    (std_center_facts h.toStandardSetting ht2 htZ').1 ht2
  obtain ⟨hCL, hmove⟩ := spine h h2 hQ ht M
  have D := Facts.of_localModel h ht2 htZ' M hout
  have hCE := centralizer_eq_of_localModel h h2 hQ ht M
  have hLF : L ⊔ centralizer (L : Set G) = L := by
    rw [hCL]
    exact sup_eq_left.2 (zpowers_le.2 htL)
  have hle2 := hout
  rw [hLF] at hle2
  have hne0 : L.relIndex (centralizer ({t} : Set G)) ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hne1 : L.relIndex (centralizer ({t} : Set G)) ≠ 1 := fun h1 =>
    hne (le_antisymm (relIndex_eq_one.1 h1) D.le_centralizer)
  have hLH : L.relIndex (centralizer ({t} : Set G)) = 2 := by omega
  have hout' := exists_outer_normalizer h h2 hQ ht M hne
  exact ⟨(E0.map ψ.symm.toMonoidHom).map L.subtype,
    Subgroup.map_subtype_le (E0.map ψ.symm.toMonoidHom),
    m24Out_of_frame hMain h D hCE hLH hmove hout' hFG⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81
