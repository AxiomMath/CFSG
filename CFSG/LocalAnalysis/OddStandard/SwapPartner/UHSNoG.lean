module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSG1
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSCount

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

theorem HSCtx.not_centralizes_g (C : HSCtx z ι ιd Kh) [Finite G] :
    ¬ ∀ k ∈ Kh, gElt ιd * k = k * gElt ιd := by
  intro hg
  obtain ⟨hx2, b, hbK, hb, hcard⟩ := C.exists_involution_of_g hg
  let Cc : Subgroup G := Kh ⊓ centralizer ({b} : Set G)
  have hCx : ∀ c ∈ Cc, z * ι τ₀ * c = c * (z * ι τ₀) := by
    intro c hc
    have hmem : c ∈ centralizer ({z * ι τ₀} : Set G) :=
      C.khat.le (Subgroup.mem_inf.mp hc).1
    exact (mem_centralizer_singleton_iff.mp hmem).symm
  have hCg : ∀ c ∈ Cc, gElt ιd * c = c * gElt ιd := by
    intro c hc
    exact hg c (Subgroup.mem_inf.mp hc).1
  have hCd : ∀ c ∈ Cc, ι (swap 0 1) * c = c * ι (swap 0 1) := by
    intro c hc
    have hcKh : c ∈ Kh := (Subgroup.mem_inf.mp hc).1
    have hcb : c * b = b * c :=
      mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    have hcx : c * (z * ι τ₀) = (z * ι τ₀) * c :=
      mem_centralizer_singleton_iff.mp (C.khat.le hcKh)
    rcases hb with hb | hb
    · rw [hb] at hcb
      exact hcb.symm
    · have hd : (z * ι τ₀) * b = ι (swap 0 1) := by
        rw [hb, ← mul_assoc, C.frame.d8.x_sq, one_mul]
      have hcomm : c * ((z * ι τ₀) * b) = ((z * ι τ₀) * b) * c := by
        calc c * ((z * ι τ₀) * b)
            = (c * (z * ι τ₀)) * b := by group
          _ = ((z * ι τ₀) * c) * b := by rw [hcx]
          _ = (z * ι τ₀) * (c * b) := by group
          _ = (z * ι τ₀) * (b * c) := by rw [hcb]
          _ = ((z * ι τ₀) * b) * c := by group
      rw [hd] at hcomm
      exact hcomm.symm
  have hx : z * ι τ₀ ∉ Cc := fun h => hx2 (Subgroup.mem_inf.mp h).1
  have hgmem : gElt ιd ∉ Cc := by
    intro h
    have hgKh : gElt ιd ∈ Kh := (Subgroup.mem_inf.mp h).1
    have hcenter : (⟨gElt ιd, hgKh⟩ : ↥Kh) ∈ center ↥Kh := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((hg y.1 y.2).symm)
    rw [C.center_eq_bot_of_g hg, Subgroup.mem_bot] at hcenter
    exact D8Rel.u_g_ne_one C.frame.d8 (congrArg Subtype.val hcenter)
  have hgxmem : gElt ιd * (z * ι τ₀) ∉ Cc := by
    intro h
    have hgxKh : gElt ιd * (z * ι τ₀) ∈ Kh := (Subgroup.mem_inf.mp h).1
    have hcenter : (⟨gElt ιd * (z * ι τ₀), hgxKh⟩ : ↥Kh) ∈ center ↥Kh := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have hyg : gElt ιd * y.1 = y.1 * gElt ιd := hg y.1 y.2
      have hyx : y.1 * (z * ι τ₀) = (z * ι τ₀) * y.1 :=
        mem_centralizer_singleton_iff.mp (C.khat.le y.2)
      calc y.1 * (gElt ιd * (z * ι τ₀))
          = (y.1 * gElt ιd) * (z * ι τ₀) := by group
        _ = (gElt ιd * y.1) * (z * ι τ₀) := by rw [← hyg]
        _ = gElt ιd * (y.1 * (z * ι τ₀)) := by group
        _ = gElt ιd * ((z * ι τ₀) * y.1) := by rw [hyx]
        _ = (gElt ιd * (z * ι τ₀)) * y.1 := by group
    rw [C.center_eq_bot_of_g hg, Subgroup.mem_bot] at hcenter
    exact D8Rel.u_gx_ne_one C.frame.d8 (congrArg Subtype.val hcenter)
  have hle := four_mul_card_le_of_commute C.frame (C := Cc) hCx hCg hCd hx hgmem hgxmem
  have hc : 2880 ≤ Nat.card ↥Cc := hcard
  omega

end CFSG.OddStandard.AltStdSec.SwapPartner
