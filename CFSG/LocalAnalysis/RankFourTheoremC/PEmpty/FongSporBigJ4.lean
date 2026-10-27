module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporBigCoatom
public import CFSG.Sporadic.J4.QT2LocX0Main
public import CFSG.Sporadic.J4.QT2LocCntMain
public import CFSG.Sporadic.J4.QT2LocZMain
public import CFSG.Sporadic.Bridge.J4Surj
public import Certificates.Certificate40344

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.J4 Subgroup

theorem coatomW_J4_5 :
    CoatomW ↥J 5 := by
  have hF : J4Facts := j4Facts
  have hM : MatFacts := hF.mat
  have h407 := Certificates.certificate40344
  have hfix : QT2.fiveAct 407 = 407 := h407.1
  have hz407 : (407 : ℕ) ∈ QT2.zMasks := h407.2
  have hElem : QT.Elem QT.uJ 11 := QT.elem_uJ hM
  refine ⟨QT2.fiveElt, QT.eta QT.uJ 11 407, QT.Eg QT.uJ 11, QT2.orderOf_fiveElt_J4, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have h := QT.Eg_sq hElem g.2
    simpa [pow_one, pow_two] using h
  · rw [QT.normalizer_Eg_eq_Hj hF]
    exact QT2.fiveElt_mem_Hj
  · exact QT.eta_mem_Eg 11 le_rfl 407
  · exact QT.eta_sq hElem 407
  ·
    have hcard := QT2.card_centralizer_eta_of_mem_zMasks hz407
    intro h1
    rw [h1] at hcard
    have htop : Subgroup.centralizer ({(1 : ↥J)} : Set ↥J) = ⊤ := by
      ext x
      simp [Subgroup.mem_centralizer_iff]
    rw [htop, Subgroup.card_top, card_J hF] at hcard
    norm_num at hcard
  · have h := QT2.fiveElt_conj hM 407
    rw [hfix] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · rw [QT.normalizer_Eg_eq_Hj hF]
    exact QT.isCoatom_Hj hF
  · rw [QT.normalizer_Eg_eq_Hj hF]
    intro hle
    obtain ⟨g₁, hg₁, hg₁eq⟩ := QT2.exists_conj_eta_three_of_mem_zMasks hz407
    obtain ⟨g₂, hg₂, hg₂eq⟩ := QT2.exists_conj_eta_three_of_mem_zMasks QT2.mem_zMasks_1131
    obtain ⟨x, hxc, hxH⟩ := QT2.centralizer_z0_not_le_Hj
    set e3 := QT.eta QT.uJ 11 3 with he3
    have hxc' : x * (g₂ * e3 * g₂⁻¹) = (g₂ * e3 * g₂⁻¹) * x := by
      rw [hg₂eq]
      exact hxc
    have hc3 : (g₂⁻¹ * x * g₂) * e3 = e3 * (g₂⁻¹ * x * g₂) := by
      calc (g₂⁻¹ * x * g₂) * e3 = g₂⁻¹ * (x * (g₂ * e3 * g₂⁻¹)) * g₂ := by group
        _ = g₂⁻¹ * ((g₂ * e3 * g₂⁻¹) * x) * g₂ := by rw [hxc']
        _ = e3 * (g₂⁻¹ * x * g₂) := by group
    have hy : g₁ * (g₂⁻¹ * x * g₂) * g₁⁻¹ ∈
        Subgroup.centralizer ({QT.eta QT.uJ 11 407} : Set ↥J) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hg₁eq]
      calc g₁ * (g₂⁻¹ * x * g₂) * g₁⁻¹ * (g₁ * e3 * g₁⁻¹)
          = g₁ * ((g₂⁻¹ * x * g₂) * e3) * g₁⁻¹ := by group
        _ = g₁ * (e3 * (g₂⁻¹ * x * g₂)) * g₁⁻¹ := by rw [hc3]
        _ = (g₁ * e3 * g₁⁻¹) * (g₁ * (g₂⁻¹ * x * g₂) * g₁⁻¹) := by group
    have hyH := hle hy
    have hx : x = g₂ * g₁⁻¹ * (g₁ * (g₂⁻¹ * x * g₂) * g₁⁻¹) * g₁ * g₂⁻¹ := by group
    apply hxH
    rw [hx]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hg₂ (Subgroup.inv_mem _ hg₁)) hyH) hg₁) (Subgroup.inv_mem _ hg₂)

theorem row_J4_5 :
    KFactSporLocalRow .J4 5 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  have hF : J4Facts := j4Facts
  refine row_of_coatomW (↥J) (fun G _ h => by
    obtain ⟨e⟩ := h
    exact ⟨e.trans (b.symm.trans (seedEquiv hF.mat))⟩) ?_ coatomW_J4_5
  rw [card_J hF]
  norm_num

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
