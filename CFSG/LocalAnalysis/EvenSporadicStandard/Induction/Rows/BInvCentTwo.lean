module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.BInvCentStab

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.Monster.B CFSG.Monster.B.CTIB CFSG.Monster.B.Short

attribute [local instance] kvLeft

theorem Qs_le_Jbar_op : Qs ≤ Jbar.op := fun _ hx => Ebar_le_Jbar hx

theorem qS_mem_Jbar_op (n : ℕ) : qS n ∈ Jbar.op := Qs_le_Jbar_op (qS_mem n)

section


theorem xs_central : (⟨xs, Qs_le_Jbar_op xs_mem⟩ : ↥Jbar.op) ∈ center ↥Jbar.op := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  show (g : Sbp) * xs = xs * (g : Sbp)
  have h : (g : Sbp)⁻¹ * xs * (g : Sbp) = xs := conj_xs g.2
  calc (g : Sbp) * xs = (g : Sbp) * ((g : Sbp)⁻¹ * xs * (g : Sbp)) := by rw [h]
    _ = xs * (g : Sbp) := by group

end

theorem psiS_conj_stab {P : Subgroup KS} (hP : ∀ k ∈ P, k • vecW 7 = vecW 7) (x : ↥Jbar.op)
    (hx : piH x ∈ P) : psiS ((x : Sbp)⁻¹ * qS 7 * (x : Sbp)) = psiS (qS 7) := by
  rw [psiS_conj x.2 (qS_mem 7)]
  show wAct _ (piH x) (vecW 7) = vecW 7
  have h1 := hP (piH x)⁻¹ (P.inv_mem hx)
  rwa [kvLeft_smul, inv_inv] at h1

section


theorem twist_mem_center {P : Subgroup KS} (hP : ∀ k ∈ P, k • vecW 7 = vecW 7)
    (d : ↥Jbar.op) (hd : piH d ∈ P) :
    d * (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op) * d⁻¹ * (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op)⁻¹ ∈
      center ↥Jbar.op := by
  have h1 := psiS_conj_stab hP d⁻¹ (by rw [map_inv]; exact P.inv_mem hd)
  have hmem : (d : Sbp) * qS 7 * (d : Sbp)⁻¹ ∈ Qs := by
    have := conj_mem_Qs (g := (d : Sbp)⁻¹) d⁻¹.2 (qS_mem 7)
    rwa [inv_inv] at this
  have h2 : (d : Sbp) * qS 7 * (d : Sbp)⁻¹ = qS 7 ∨
      (d : Sbp) * qS 7 * (d : Sbp)⁻¹ = xs * qS 7 := by
    refine eq_of_psiS_eq hmem (qS_mem 7) ?_
    simpa using h1
  rcases h2 with h | h
  · have : d * (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op) * d⁻¹ *
        (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op)⁻¹ = 1 := by
      apply Subtype.ext
      show (d : Sbp) * qS 7 * (d : Sbp)⁻¹ * (qS 7)⁻¹ = 1
      rw [h, mul_inv_cancel]
    rw [this]
    exact one_mem _
  · have : d * (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op) * d⁻¹ *
        (⟨qS 7, qS_mem_Jbar_op 7⟩ : ↥Jbar.op)⁻¹ = ⟨xs, Qs_le_Jbar_op xs_mem⟩ := by
      apply Subtype.ext
      show (d : Sbp) * qS 7 * (d : Sbp)⁻¹ * (qS 7)⁻¹ = xs
      rw [h, mul_inv_cancel_right]
    rw [this]
    exact xs_central

end

section


theorem not_isSolvable_cent_qS7 : ¬ Group.IsSolvable ↥(centralizer ({qS 7} : Set Sbp)) := by
  obtain ⟨P, hnt, hperf, hP⟩ := exists_a5_stab
  intro hsolv
  have h := isSolvable_centralizer_subgroup Jbar.op ⟨qS 7, qS_mem_Jbar_op 7⟩ hsolv
  exact not_isSolvable_centralizer_of_perfect_section piH piH_surjective (P := P)
    (fun d hd => twist_mem_center hP d hd) h

end

end CFSG.EvenSporadicStandard.Induction.Hyp
