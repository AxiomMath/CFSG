module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.OctadElem

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup Octad

variable {G : Type} [Group G]

theorem exists_nData [Finite G] {L B : Subgroup G} {z : G} (hs : LocalSetting G L z)
    (hB : OctadType L B) (hb : OctadBasics L B) (hl : LiftDataB L B) (hsp : SplitDataB L B)
    (hcase : ¬ egM B z ≤ centralizer ({z} : Set G)) : ∃ D : Subgroup G, NData B z D := by
  have hBL : B ≤ L := hB.1
  obtain ⟨Y, hY⟩ := exists_YStructB hs hBL hb hsp hcase
  have hsq := Y_mul_self hs hBL hb hl hcase hY
  refine ⟨Y, ⟨hY.B_le, hY.le_lam, ⟨abelian_of_sq_eq_one hsq, hsq⟩, card_Y hs hBL hb hY hcase,
    hY.z_not_mem, ?_, ?_, ?_, hY.cover⟩⟩
  · intro n hn d hd
    have hxΛ : n * d * n⁻¹ ∈ egLam B z :=
      conj_mem_egLam_of_egM hs hBL hb hcase hn (hY.le_lam hd)
    have hx2 : n * d * n⁻¹ * (n * d * n⁻¹) = 1 := by
      calc n * d * n⁻¹ * (n * d * n⁻¹) = n * (d * d) * n⁻¹ := by group
        _ = 1 := by rw [hsq d hd, mul_one, mul_inv_cancel]
    rcases hY.cover _ hxΛ with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy, hyx⟩ : ∃ y ∈ Y, n * d * n⁻¹ = z * y :=
        ⟨z * (n * d * n⁻¹), h, by rw [← mul_assoc z z, z_mul_self hs, one_mul]⟩
      have hyB : y ∈ B := by
        refine phiB_eq_one_mem hs hBL hb hY hy ?_
        have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
        calc phiB z y = (z * y) * (z * y) := by rw [phiB, hyi]; group
          _ = 1 := by rw [← hyx]; exact hx2
      obtain ⟨b₁, hb₁, h1⟩ := conj_z_eq hs hBL (inv_mem hn)
      have h2 := conj_mem_B hs hBL hb hcase (inv_mem hn) hyB
      rw [inv_inv] at h1 h2
      have hd' : d = z * (b₁ * (n⁻¹ * y * n)) := by
        calc d = n⁻¹ * (n * d * n⁻¹) * n := by group
          _ = n⁻¹ * z * n * (n⁻¹ * y * n) := by rw [hyx]; group
          _ = z * (b₁ * (n⁻¹ * y * n)) := by rw [h1]; group
      apply hY.z_not_mem
      have e : z = d * (b₁ * (n⁻¹ * y * n))⁻¹ := by rw [hd']; group
      rw [e]
      exact mul_mem hd (inv_mem (hY.B_le (mul_mem hb₁ h2)))
  · intro d hd
    have e : z * d * z⁻¹ * d⁻¹ = phiB z d⁻¹ := by
      simp only [phiB, inv_inv, z_inv hs]
      group
    rw [e]
    exact phiB_mem hs hBL (mem_egLam.1 (hY.le_lam (inv_mem hd))).1
  · intro b hbB
    obtain ⟨d, hd, hdb⟩ := exists_phiB_eq_Y hs hBL hb hY hcase hbB
    refine ⟨d⁻¹, inv_mem hd, ?_⟩
    rw [← hdb]
    simp only [phiB, inv_inv, z_inv hs]
    group

end CFSG.EvenSporadicStandard.M24Std
