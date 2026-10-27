module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Setup

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

section K

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem C_data (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) :
    IsF20 (Us d) (star d d.x₅) (star d y₁) ∧
      img d (CMt d) = zpowers (star d d.t) ⊔ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) ∧
      zpowers (star d d.t) ⊓ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁) = ⊥ ∧
      ∀ a ∈ IsF20.Pgrp (Us d) (star d d.x₅) (star d y₁), star d d.t * a = a * star d d.t := by
  obtain ⟨hU, hU16, hrest⟩ := h17s
  obtain ⟨h17c, h17i, h17t⟩ := hrest y₁ hy
  have hF := isF20_Us h49 hd hz h10 hU hU16 hy
  have hPe := P_eq h49 hd y₁
  rw [hPe] at h17c h17i h17t
  exact ⟨hF, h17c, h17i, h17t⟩

theorem mem_normalizer_U0s {x : MulAut ↥d.s56V}
    (hx : x ∈ normalizer ((Us d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)))
    (hxt : x * star d d.t = star d d.t * x) :
    x ∈ normalizer ((U0s d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  refine mem_normalizer_sup' hx ?_
  apply Subgroup.centralizer_le_normalizer
  rw [mem_centralizer_iff]
  intro g hg
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
  exact (Commute.zpow_left (show Commute (star d d.t) x from hxt.symm) n).eq

theorem C_le_Ks (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h10 : Node10 d z₀)
    (h17s : Node17s d z₀) {y₁ : G} (hy : IsV1 d z₀ y₁) : img d (CMt d) ≤ Ks d := by
  obtain ⟨hF, hCe, -, hCt⟩ := C_data h49 hd hz h10 h17s hy
  refine le_inf ?_ (imgIn_mono _ (CMt_le_Hg h49 hd))
  rw [hCe]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    refine mem_normalizer_U0s ?_ rfl
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro u hu
    exact (hCt u (IsF20.U_le_Pgrp _ _ _ hu)).symm
  · intro p hp
    exact mem_normalizer_U0s (hF.Pgrp_le_normalizer hp) (hCt p hp).symm

end K

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
