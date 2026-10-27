module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AS
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AG
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BIn
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BPr
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3BSi

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec8t84g_exists_m (hP : Sec8T84FactP) (hS4 : Sec8T84FactS4) {G : Type} [Group G]
    [Finite G] {t : G} {E Y1 Y2 T T1 T2 V1 V2 F1 F2 : Subgroup G}
    (h : Sec8T84GSet G t E Y1 Y2 T T1 T2 V1 V2 F1 F2) {γ : G} (hγ2 : γ * γ = 1)
    (hE1 : E.map (MulAut.conj γ).toMonoidHom = F1 ⊔ F2)
    (hE0 : (F1 ⊔ F2).map (MulAut.conj γ).toMonoidHom = E)
    (hU1 : (V1 ⊔ F1).map (MulAut.conj γ).toMonoidHom = V1 ⊔ F1)
    (hU2 : (V2 ⊔ F2).map (MulAut.conj γ).toMonoidHom = V2 ⊔ F2)
    (hC1 : IsElemAb2 ((V1 ⊔ F1) ⊓ centralizer ({γ} : Set G)) 2)
    (hC2 : IsElemAb2 ((V2 ⊔ F2) ⊓ centralizer ({γ} : Set G)) 2) :
    ∃ m ∈ sec8t84g_Q E (F1 ⊔ F2),
      (∃ k : ℕ, m ^ (3 ^ k) ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2))) ∧
      γ * m * γ⁻¹ * m⁻¹ ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) ∧
      m ∈ normalizer ((V1 ⊔ F1 : Subgroup G) : Set G) ∧
      m ∈ normalizer ((V2 ⊔ F2 : Subgroup G) : Set G) ∧
      (∀ u ∈ V1 ⊔ F1, m * u = u * m → u = 1) ∧ (∀ u ∈ V2 ⊔ F2, m * u = u * m → u = 1) := by
  obtain ⟨hγQ, hγO, -⟩ := sec8t84g3a_gamma_Q hE1 hE0
  have hQ : ∀ x ∈ sec8t84g_Q E (F1 ⊔ F2), γ * x * γ⁻¹ ∈ sec8t84g_Q E (F1 ⊔ F2) :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hγQ x).mp hx
  have hO : ∀ o ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)),
      γ * o * γ⁻¹ ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) :=
    fun o ho => (Subgroup.mem_normalizer_iff.mp hγO o).mp ho
  have hU1' := sec8t84g3b_conj_of_map hU1
  have hU2' := sec8t84g3b_conj_of_map hU2
  obtain ⟨H1, S1⟩ := sec8t84g3b_side1 h
  obtain ⟨H2, S2⟩ := sec8t84g3b_side2 h
  obtain ⟨z1, hz1Q, hz1Y, hz1c, hz1n, hz13, hz1γ, hz1f⟩ :=
    sec8t84g3b_side_exists hP hS4 S1 hγ2 hQ hO hU1' hU2' hC1
  obtain ⟨z2, hz2Q, hz2Y, hz2c, hz2n, hz23, hz2γ, hz2f⟩ :=
    sec8t84g3b_side_exists hP hS4 S2 hγ2 hQ hO hU2' hU1' hC2
  have hcomm : z1 * z2 * z1⁻¹ * z2⁻¹ ∈ oddCoreIn (sec8t84g_Q E (F1 ⊔ F2)) := by
    rw [S1.O_eq]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hz1Q hz2Q)
      (Subgroup.inv_mem _ hz1Q)) (Subgroup.inv_mem _ hz2Q), S1.comm z1 hz1Y z2 hz2Y⟩
  refine ⟨z1 * z2, Subgroup.mul_mem _ hz1Q hz2Q, ⟨1, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pow_one]
    exact sec8t84g3b_pow3_mul hz1Q hz2Q hz13 hz23 hcomm
  · have h1 : γ * (z1 * z2) * γ⁻¹ * (z1 * z2)⁻¹ =
        (γ * z1 * γ⁻¹ * z1⁻¹) * (z1 * (γ * z2 * γ⁻¹ * z2⁻¹) * z1⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ hz1γ (CFSG.ClassicalInvolution.Balance.conj_mem_oddCoreIn hz1Q hz2γ)
  · exact Subgroup.mul_mem _ hz1n (sec8t84g3b_norm_of_cent hz2c)
  · exact Subgroup.mul_mem _ (sec8t84g3b_norm_of_cent hz1c) hz2n
  · exact fun u hu hm => hz1f u hu (sec8t84g3b_comm_cancel_left (hz2c u hu) hm)
  · exact fun u hu hm => hz2f u hu (sec8t84g3b_comm_cancel_right (hz1c u hu) hm)

end CFSG.OddStandard.SmallF3.Omega
