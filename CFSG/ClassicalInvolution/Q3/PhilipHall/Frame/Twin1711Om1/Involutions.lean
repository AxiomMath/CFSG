module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.Basic
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylT
public import Certificates.Certificate197001

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check

set_option linter.unusedSectionVars false


private theorem om1_frameDecode_zero : frameDecode 0 = 0 := by
  funext i
  revert i
  decide

private theorem om1_mem_evenMasks {m : ℕ} (hm : m < 256) (hp : framePop m % 2 = 0)
    (h0 : m ≠ 0) (h255 : m ≠ 255) : m ∈ evenMasks := by
  unfold evenMasks
  rw [List.mem_filter, List.mem_range]
  refine ⟨hm, ?_⟩
  simp [hp, h0, h255]

private theorem om1_exists_maskData {m : ℕ} (hm : m ∈ evenMasks) : ∃ d ∈ maskData, d.1 = m := by
  have h : evenMasks.all (fun m => maskData.any fun d => d.1 == m) = true := by decide +kernel
  obtain ⟨d, hd, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 h m hm)
  exact ⟨d, hd, beq_iff_eq.1 e⟩

private theorem om1_mem_allWords {d : ℕ × ℕ × List ℕ} (hd : d ∈ maskData) :
    d.2.2 ∈ allWords := by
  unfold allWords
  exact List.mem_append_right _ (List.mem_map_of_mem (f := fun e : ℕ × ℕ × List ℕ => e.2.2) hd)

theorem exists_conj_rep (t : WP) (ht : t * t = 1) (h1 : t ≠ 1) (hz : t ≠ zW) :
    ∃ g : WP, g * t * g⁻¹ = t0 ∨ g * t * g⁻¹ = ta ∨ g * t * g⁻¹ = tb ∨ g * t * g⁻¹ = tc := by
  have hT : (t : Equiv.Perm (Fin 240)) * (t : Equiv.Perm (Fin 240)) = 1 := by
    simpa using congrArg Subtype.val ht
  obtain ⟨h, hh, hhe⟩ := CFSG.EvenSmallLie.OmegaEight.Weyl.conj_e1PlusSub t.2 hT
  obtain ⟨v, hve, hv⟩ := CFSG.EvenSmallLie.OmegaEight.Weyl.mem_e1PlusSub.1 hhe
  have hdec : frameDecode (frameEncode v) = v := frameDecode_frameEncode v
  have hm256 : frameEncode v < 256 := frameEncode_lt v
  have hpop : framePop (frameEncode v) % 2 = 0 := by
    rw [← frameWt_eq]
    exact (mem_evenSub_iff_frameWt v).1 hve
  have hm0 : frameEncode v ≠ 0 := by
    intro h0
    have hv0 : v = 0 := by
      rw [← hdec, h0, om1_frameDecode_zero]
    have hfe : h * (t : Equiv.Perm (Fin 240)) * h⁻¹ = 1 := by
      rw [← hv, hv0, CFSG.EvenSmallLie.OmegaEight.Weyl.frameElt_zero]
    have ht1 : (t : Equiv.Perm (Fin 240)) = 1 := by
      calc (t : Equiv.Perm (Fin 240))
          = h⁻¹ * (h * (t : Equiv.Perm (Fin 240)) * h⁻¹) * h := by group
        _ = 1 := by rw [hfe]; group
    apply h1
    apply Subtype.ext
    simp [ht1]
  have hm255 : frameEncode v ≠ 255 := by
    intro h255
    have hvZ : v = frameZ := by
      rw [← hdec, h255, frameDecode_255]
    have hzP : h * (t : Equiv.Perm (Fin 240)) * h⁻¹ = zPerm := by
      rw [← hv, hvZ, CFSG.EvenSmallLie.OmegaEight.Weyl.frameElt_frameZ]
    have hcomm := CFSG.EvenSmallLie.OmegaEight.Weyl.zPerm_comm h⁻¹
      (inv_mem (CFSG.EvenSmallLie.OmegaEight.Weyl.wPlus_le hh))
    have ht1 : (t : Equiv.Perm (Fin 240)) = zPerm := by
      calc (t : Equiv.Perm (Fin 240))
          = h⁻¹ * (h * (t : Equiv.Perm (Fin 240)) * h⁻¹) * h := by group
        _ = h⁻¹ * zPerm * h := by rw [hzP]
        _ = zPerm * h⁻¹ * h := by rw [hcomm]
        _ = zPerm := by group
    apply hz
    apply Subtype.ext
    simpa [zW] using ht1
  obtain ⟨d, hd, hdm⟩ := om1_exists_maskData (om1_mem_evenMasks hm256 hpop hm0 hm255)
  obtain ⟨hi4, heq⟩ := Certificates.certificate197001.2.2.2.2.2.1 d hd
  have hr4 : repMasks.getD d.2.1 0 = 15 ∨ repMasks.getD d.2.1 0 = 3 ∨
      repMasks.getD d.2.1 0 = 252 ∨ repMasks.getD d.2.1 0 = 23 := by
    have key : ∀ i < 4, repMasks.getD i 0 = 15 ∨ repMasks.getD i 0 = 3 ∨
        repMasks.getD i 0 = 252 ∨ repMasks.getD i 0 = 23 := by decide
    exact key _ hi4
  have hrp : repMasks.getD d.2.1 0 < 256 ∧ framePop (repMasks.getD d.2.1 0) % 2 = 0 := by
    have key : ∀ i < 4, repMasks.getD i 0 < 256 ∧ framePop (repMasks.getD i 0) % 2 = 0 := by
      decide
    exact key _ hi4
  have hwc : wordOK d.2.2 = true := wordOK_of_allWords (om1_mem_allWords hd)
  have hY : Om1Facts.e d.1 = frameElt v := by
    refine CFSG.RankThree.Native.permOfArr_eq_of_rep ?_
    rw [hdm, eA, hdec]
    exact rep_frameArr v
  have hcr : ((wpE d.2.2 : WP) : Equiv.Perm (Fin 240)) * frameElt v *
      ((wpE d.2.2 : WP) : Equiv.Perm (Fin 240))⁻¹ =
        ((eW (repMasks.getD d.2.1 0) : WP) : Equiv.Perm (Fin 240)) := by
    rw [coe_wpE_eq_E hwc, ← hY, coe_eW_eq_e hrp]
    exact heq
  have hconj : ∃ g : WP, g * t * g⁻¹ = eW (repMasks.getD d.2.1 0) := by
    refine ⟨wpE d.2.2 * (⟨h, hh⟩ : WP), Subtype.ext ?_⟩
    have e1 : ((wpE d.2.2 * (⟨h, hh⟩ : WP) * t * (wpE d.2.2 * (⟨h, hh⟩ : WP))⁻¹ : WP) :
        Equiv.Perm (Fin 240)) =
        ((wpE d.2.2 : WP) : Equiv.Perm (Fin 240)) * (h * (t : Equiv.Perm (Fin 240)) * h⁻¹) *
          ((wpE d.2.2 : WP) : Equiv.Perm (Fin 240))⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1, ← hv]
    exact hcr
  obtain ⟨g, hg⟩ := hconj
  rcases hr4 with hr | hr | hr | hr <;> rw [hr] at hg
  · exact ⟨g, Or.inl hg⟩
  · exact ⟨g, Or.inr (Or.inl hg)⟩
  · exact ⟨g, Or.inr (Or.inr (Or.inl hg))⟩
  · exact ⟨g, Or.inr (Or.inr (Or.inr hg))⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1
