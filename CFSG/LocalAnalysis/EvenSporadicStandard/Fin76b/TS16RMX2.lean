module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMX
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMX1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK5

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G}

theorem OuterS16Hyp.xiOuter
    (h : OuterS16Hyp G L z t T E Q x B β) {ξ : G} (hξL : ξ ∈ L) (hξβ : ξ * β * ξ⁻¹ = β⁻¹) :
    ∀ d ∈ L ⊓ centralizer ({β} : Set G), ∃ y ∈ L ⊓ centralizer ({β} : Set G),
      (ξ * y * ξ⁻¹)⁻¹ * (d * y * d⁻¹) ∉ zpowers β := by
  intro d hd
  by_contra hcon
  push_neg at hcon
  have hβL : β ∈ L := h.outerB.B_le h.outerB.beta_mem
  have hβ3 := h.outerB.beta_order
  have hdL : d ∈ L := hd.1
  have hdβ : d * β = β * d := mem_centralizer_singleton_iff.1 hd.2
  have hdinv : d⁻¹ * β⁻¹ * d = β⁻¹ := by
    have : Commute d β⁻¹ := (show Commute d β from hdβ).inv_right
    calc d⁻¹ * β⁻¹ * d = d⁻¹ * (β⁻¹ * d) := by group
      _ = d⁻¹ * (d * β⁻¹) := by rw [this.eq.symm]
      _ = β⁻¹ := by group
  have hξ'L : d⁻¹ * ξ ∈ L := mul_mem (inv_mem hdL) hξL
  have hξ'β : d⁻¹ * ξ * β * (d⁻¹ * ξ)⁻¹ = β⁻¹ := by
    calc d⁻¹ * ξ * β * (d⁻¹ * ξ)⁻¹ = d⁻¹ * (ξ * β * ξ⁻¹) * d := by group
      _ = d⁻¹ * β⁻¹ * d := by rw [hξβ]
      _ = β⁻¹ := hdinv
  have hcomm : ∀ y ∈ L ⊓ centralizer ({β} : Set G),
      d⁻¹ * ξ * y * (d⁻¹ * ξ)⁻¹ * y⁻¹ ∈ zpowers β := by
    intro y hy
    have hb := hcon y hy
    set b : G := (ξ * y * ξ⁻¹)⁻¹ * (d * y * d⁻¹) with hbdef
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hb
    have hyβ : y * β = β * y := mem_centralizer_singleton_iff.1 hy.2
    have hbd : b * d = d * b := by
      rw [← hk]
      exact ((Commute.zpow_left (show Commute β d from hdβ.symm) k)).eq
    have hby : b * y = y * b := by
      rw [← hk]
      exact ((Commute.zpow_left (show Commute β y from hyβ.symm) k)).eq
    have e1 : ξ * y * ξ⁻¹ = d * y * d⁻¹ * b⁻¹ := by
      rw [hbdef]
      group
    have hbi : b⁻¹ * d = d * b⁻¹ := (show Commute b d from hbd).inv_left.eq
    have hbiy : b⁻¹ * y = y * b⁻¹ := (show Commute b y from hby).inv_left.eq
    have e2 : d⁻¹ * ξ * y * (d⁻¹ * ξ)⁻¹ * y⁻¹ = b⁻¹ := by
      calc d⁻¹ * ξ * y * (d⁻¹ * ξ)⁻¹ * y⁻¹ = d⁻¹ * (ξ * y * ξ⁻¹) * d * y⁻¹ := by group
        _ = d⁻¹ * (d * y * d⁻¹ * b⁻¹) * d * y⁻¹ := by rw [e1]
        _ = y * (d⁻¹ * b⁻¹ * d) * y⁻¹ := by group
        _ = y * b⁻¹ * y⁻¹ := by rw [show d⁻¹ * b⁻¹ * d = b⁻¹ by
            calc d⁻¹ * b⁻¹ * d = d⁻¹ * (b⁻¹ * d) := by group
              _ = d⁻¹ * (d * b⁻¹) := by rw [hbi]
              _ = b⁻¹ := by group]
        _ = b⁻¹ := by
            calc y * b⁻¹ * y⁻¹ = (y * b⁻¹) * y⁻¹ := by group
              _ = (b⁻¹ * y) * y⁻¹ := by rw [hbiy]
              _ = b⁻¹ := by group
    rw [e2]
    exact inv_mem (mem_zpowers_iff.2 ⟨k, hk⟩)
  obtain ⟨ι, hιL, hι2, hι1, h9⟩ := exists_invol_cent_nine hβL hβ3 h.card_D hξ'L hξ'β hcomm
  exact not_dvd_nine_cent_involution h.sporadic hιL hι2 hι1 h9

end CFSG.EvenSporadicStandard.Fin76b
