module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Frontier

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁}

theorem not_A8 (I : In81) (h8 : GS81Step8Input) {v : H} (hst : d.Stage7 v) :
    ¬ Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8)) := by
  intro hA8
  have hv := hst.isV
  have F := hst.facts
  have h3 := not_conj_asigma_sigma F hst.not_b_bz
  obtain ⟨A, hAR, hA2, hA32, hfus⟩ := h8 H h H₁ d v hst hA8
  have hAU : A ≤ h.U81 v := hAR.trans inf_le_left
  obtain ⟨t, htAP, ht1, hta⟩ := exists_mem_E32_P hv I F h3 hAU hA2 hA32
  obtain ⟨htA, htP⟩ := mem_inf.mp htAP
  have ht2 : t * t = 1 := hA2 t htA
  have hinv : ∀ x y : H, x * y = y * x → x * x = 1 → y * y = 1 → x * y * (x * y) = 1 := by
    intro x y hxy hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hxy]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hx, hy, one_mul]
  have haσ2 : h.a * d.sigma * (h.a * d.sigma) = 1 :=
    hinv h.a d.sigma (h.toHyp52.comm_a d.sigma_mem_S).symm (Six.a_mul_a_self h.toHyp52)
      d.sigma_mul_self
  have htnot : t ∉ zpowers (h.a * d.sigma) := by
    intro htz
    rcases eq_one_or_of_mem_zpowers_of_mul_self haσ2 htz with h1 | h1
    · exact ht1 h1
    · apply d.sigma_not_mem_P I.cf1 I.cf2 F
      have := mul_mem (inv_mem h.toHyp52.a_mem_P) (h1 ▸ htP)
      rwa [inv_mul_cancel_left] at this
  obtain ⟨c, hc⟩ := hst.fusion t htP ht2 ht1 hta
  rcases hfus t (mem_inf.mpr ⟨htA, (mem_inf.mp htP).2⟩) htnot with ⟨c', hc'⟩ | ⟨c', hc'⟩
  ·
    apply not_conj_a_b hv I F (c' * c⁻¹)
    rw [show (c' * c⁻¹)⁻¹ * h.a * (c' * c⁻¹) = c * (c'⁻¹ * h.a * c') * c⁻¹ by group, hc', ← hc]
    group
  ·
    obtain ⟨k, hk, hkz⟩ := F.z_tau
    apply hst.not_b_bz (c * c'⁻¹ * k⁻¹)
    rw [show (c * c'⁻¹ * k⁻¹)⁻¹ * d.b * (c * c'⁻¹ * k⁻¹) =
        k * (c' * (c⁻¹ * d.b * c) * c'⁻¹) * k⁻¹ by group, hc, ← hc',
      Eight.mul_conj_inv_cancel c' d.sigma, d.k_sigma hk hkz]

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
