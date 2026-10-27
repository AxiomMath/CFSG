module

public import CFSG.GF2Type.Smith1979W3.ReducibleSplit
public import CFSG.LargeExtraspecial.FSmithQuatOfNondeg
public import CFSG.LargeExtraspecial.FSmithQuatConj
public import CFSG.LargeExtraspecial.OrthoF2AnisoPlane
public import CFSG.GF2Type.ModelPSL
public import CFSG.GF2Type.Smith1979CharTwo
public import CFSG.LargeExtraspecial.AS62EnumInputs
public import CFSG.LargeExtraspecial.S14Main
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Defs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeldBridge
public import CFSG.Sporadic.Th.KernelPlanes
public import CFSG.Sporadic.Th.Local
public import Certificates.Certificate19780

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG CFSG.LargeExtraspecial

theorem dw3NoNondeg : DW3NoNondeg := by
  intro G _ _ _ S hw hnwc W hW h0 htop hc
  obtain ⟨P, hPQ, hPM, hP8, hPsq⟩ := DW.exists_quat_of_isCompl S hw hW h0 htop hc
  have hP : DW.NormalQuat S P := ⟨hPQ, hPM, hP8, hPsq⟩
  obtain ⟨g₀, hg₀Q, hg₀z⟩ := hnwc
  have hn : 3 ≤ S.width := by omega
  refine OrthoF2.false_of_anisotropicPlane
    (V := S.Qt) (q := S.q) (W := S.clSub P)
    (hq := S.q_nondegenerate) (hV := ?_) (hW2 := hP.finrank_clSub) (hWq := ?_)
    (H := S.Mbar) (hHW := ?_) (hO2 := ?_) (hfix := ?_)
    (D := {v : S.Qt | ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z ∧
      S.cl (g * S.z * g⁻¹) = v})
    (hD := ?_) (hDU := ?_) (hDq := ?_) (hDH := ?_) (hE := ?_) (hY := ?_)
  · rw [S.finrank_Qt_eq_two_mul_width, hw]
  · intro w hwmem hw0
    exact hP.q_eq_one_of_mem_clSub hwmem hw0
  · intro h hh w hwmem
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hh
    exact hP.isMbarInvariant_clSub m w hwmem
  · intro N hNM hN h2
    exact S.eq_bot_of_normalized_L hNM hN h2
  · intro v hv
    exact DW.eq_zero_of_forall_ρ_apply_eq (S := S) (by omega : 2 ≤ S.width)
      (fun m => hv (S.ρ m) ⟨m, rfl⟩)
  · exact ⟨S.cl (g₀ * S.z * g₀⁻¹), g₀, hg₀Q, hg₀z, rfl⟩
  · intro v hv
    obtain ⟨g, hgQ, hgne, rfl⟩ := hv
    exact (hP.cl_conj_mem_perp hn hgQ hgne).1
  · intro a ha
    obtain ⟨g, hgQ, hgne, rfl⟩ := ha
    exact (hP.cl_conj_mem_perp hn hgQ hgne).2
  · intro h hh a ha
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hh
    obtain ⟨g, hgQ, hgne, rfl⟩ := ha
    have hconj : (m * g) * S.z * (m * g)⁻¹ = m * (g * S.z * g⁻¹) * (m : G)⁻¹ := by group
    have hzm : (m : G)⁻¹ * S.z * (m : G) = S.z := by
      calc (m : G)⁻¹ * S.z * (m : G) = (m : G)⁻¹ * (S.z * (m : G)) := by rw [mul_assoc]
        _ = (m : G)⁻¹ * ((m : G) * S.z) := by rw [(S.z_comm m.2).symm]
        _ = S.z := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨m * g, ?_, ?_, ?_⟩
    · rw [hconj]
      exact S.conj_mem_QG m.2 hgQ
    · intro hz
      apply hgne
      calc g * S.z * g⁻¹ =
          (m : G)⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * (m : G) := by group
        _ = (m : G)⁻¹ * S.z * (m : G) := by rw [← hconj, hz]
        _ = S.z := hzm
    · rw [hconj]
      exact (S.ρ_cl m hgQ).symm
  · intro a ha u hu hau
    obtain ⟨g, hgQ, hgne, rfl⟩ := ha
    obtain ⟨m, hm⟩ := hP.exists_ρL_eq_eichler hw hgQ hgne hu hau
    exact MonoidHom.mem_range.mpr ⟨m, Subtype.ext hm⟩
  · intro h hh hfixU
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hh
    exact hP.ρ_eq_one_of_forall_perp hn hg₀Q hg₀z (fun u hu => hfixU u hu)

end CFSG.GF2Type.Smith1979W3
