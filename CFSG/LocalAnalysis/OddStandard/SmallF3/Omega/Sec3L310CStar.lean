module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310CStarOrd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Proj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Inputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def IsOmegaPlusStar (Y : Subgroup G) : Prop :=
  InFStar Y ∧ LieModel (↥Y ⧸ oddCore ↥Y) .POmegaPlus 4 3 1

theorem isOmegaPlusStar_of_dvd {X Y : Subgroup G} [Finite G] (hX : IsOmegaPlusStar X)
    (hY : InFStar Y) (hd : Nat.card (↥X ⧸ oddCore ↥X) ∣ Nat.card (↥Y ⧸ oddCore ↥Y)) :
    IsOmegaPlusStar Y := by
  rw [card_of_pOmegaPlus hX.2] at hd
  exact ⟨hY, lieModel_of_dvd_card hY hd⟩

theorem IsOmegaPlusStar.of_walterArrow [Finite G] (hA : AschA2 G) {X Y : Subgroup G}
    (h : WalterArrow X Y) (hX : IsOmegaPlusStar X) : IsOmegaPlusStar Y := by
  have hY : InFStar Y := inFStar_of_walterArrow hA h hX.1
  unfold WalterArrow at h
  obtain ⟨-, -, -, -, -, -, -, hXY, -⟩ := h
  exact isOmegaPlusStar_of_dvd hX hY (card_quotient_oddCore_dvd hXY)

theorem IsOmegaPlusStar.of_walterArrowDiag [Finite G] (hA : AschA2 G) {X Y : Subgroup G}
    (h : WalterArrowDiag X Y) (hX : IsOmegaPlusStar X) : IsOmegaPlusStar Y := by
  have hY : InFStar Y := inFStar_of_walterArrowDiag hA h hX.1
  unfold WalterArrowDiag at h
  obtain ⟨x, y, -, -, hxy, -, hYc, hle, hne⟩ := h
  have hxCy : x ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hxy.symm
  have hYxc : IsComponentIn (CFSG.conjugate Y x) (centralizer ({y} : Set G)) :=
    hYc.conjugate hxCy
  have hne' : Y ≠ CFSG.conjugate Y x := by
    intro heq
    apply hne
    rw [← heq]
    exact sup_idem Y
  have hcomm := hYc.commute_of_ne hYxc hne'
  have hq : IsQuasisimple X := isQuasisimple_of_isFStarGroup hX.1
  have hN : Nat.card (↥X ⧸ center ↥X) = 4952179814400 := by
    rw [center_eq_oddCore_of_pOmegaPlus hX.1 hX.2]
    exact card_of_pOmegaPlus hX.2
  rcases card_quotient_center_dvd_of_le_sup hcomm hle hq with hd | hd
  · rw [hN] at hd
    exact ⟨hY, lieModel_of_dvd_card hY
      (hd.trans (card_quotient_center_dvd_card_quotient_oddCore hY))⟩
  · rw [hN] at hd
    have hYx : InFStar (CFSG.conjugate Y x) := InFStar.conjugate hY x
    have h1 := hd.trans (card_quotient_center_dvd_card_quotient_oddCore hYx)
    rw [card_quotient_oddCore_conjugate Y x] at h1
    exact ⟨hY, lieModel_of_dvd_card hY h1⟩

theorem IsOmegaPlusStar.of_walterChain [Finite G] (hA : AschA2 G) {X Y : Subgroup G}
    (h : WalterChain X Y) (hX : IsOmegaPlusStar X) : IsOmegaPlusStar Y := by
  unfold WalterChain at h
  induction h with
  | refl => exact hX
  | tail _ hbc ih =>
      rcases hbc with hstep | hstep
      · exact IsOmegaPlusStar.of_walterArrow hA hstep ih
      · exact IsOmegaPlusStar.of_walterArrowDiag hA hstep ih

theorem asc82OmegaPlusCStar : Asc82OmegaPlusCStar := by
  intro G _ _ t L hS hΩ
  have hX : IsOmegaPlusStar L := ⟨inFStar_of_inF hS.inF, hΩ⟩
  refine ⟨⟨t, hS.involution, hS.component⟩, fun Y hY => ?_⟩
  have hYs := IsOmegaPlusStar.of_walterChain hS.a2 hY hX
  exact nonempty_equiv_center_quotient_of_pOmegaPlus hX.1 hYs.1 hX.2 hYs.2

end CFSG.OddStandard.SmallF3.Omega
