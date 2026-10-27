module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyMultMain
public import CFSG.RankThree.Native.LyFiveKernel

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult

open Subgroup CFSG CFSG.Blueprint

theorem lyMultFive_thm :
    LyMultFive := by
  intro J _ _ hJ hLy hp
  have : Group.IsPerfect J := hJ.1
  have hker : (QuotientGroup.mk' (Subgroup.center J)).ker = Subgroup.center J :=
    QuotientGroup.ker_mk' _
  have hp' : IsPGroup 5 (QuotientGroup.mk' (Subgroup.center J)).ker := by
    rw [hker]; exact hp
  have h := (CFSG.RankThree.Native.R3E_Ly_full_central_five_kernel_trivial hLy
    (QuotientGroup.mk' (Subgroup.center J)) (QuotientGroup.mk'_surjective _) hker.le).2 hp'
  rw [hker] at h
  exact ⟨fun a b => Subtype.ext (by
    have ha : (a : J) ∈ (⊥ : Subgroup J) := h ▸ a.2
    have hb : (b : J) ∈ (⊥ : Subgroup J) := h ▸ b.2
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb])⟩

theorem lyMultTrivial_thm
    : LyMultTrivial :=
  lyMultTrivial_of_five lyMultFive_thm

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyMult
