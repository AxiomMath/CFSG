module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkI4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FramePocket

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

namespace Pk

theorem exists_frame_tA
    {G : Type} [Group G] {L : Subgroup G} (hL : IsPSp43 L) {z : G} (hz : IsI4PlusIn L z) :
    ∃ (F : PspFrame L) (hzL : z ∈ L), F.ψ ⟨z, hzL⟩ = tA := by
  obtain ⟨F0⟩ := exists_pspFrame hL
  have hzL : z ∈ L := PspFrame.mem_of_isI4PlusIn hz
  have hp : IsI4PlusIn QP45.originalSubgroup (F0.ψ ⟨z, hzL⟩) :=
    (F0.isI4PlusIn_img_iff hzL).1 hz
  obtain ⟨c, hc, hcov⟩ := exists_cover_pk (F0.ψ_mem ⟨z, hzL⟩) hp.1
  rcases hcov with h | h
  · exact ⟨F0.conj c hc, hzL, by rw [PspFrame.conj_psi, h]⟩
  · exfalso
    have h' : c⁻¹ * tB * c⁻¹⁻¹ = F0.ψ ⟨z, hzL⟩ := by
      rw [inv_inv, ← h]
      group
    exact not_isI4PlusIn_of_conj_tB (QP45.originalSubgroup.inv_mem hc) h' hp

theorem commutator_le_of_le {G : Type} [Group G] {L X Y : Subgroup G} (hX : X ≤ L) (hY : Y ≤ L) :
    ⁅X, Y⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact L.mul_mem (L.mul_mem (L.mul_mem (hX ha) (hY hb)) (L.inv_mem (hX ha))) (L.inv_mem (hY hb))

theorem conjugate_le_of_le {G : Type} [Group G] {L X : Subgroup G} {g : G} (hX : X ≤ L)
    (hg : g ∈ L) : CFSG.conjugate X g ≤ L := by
  intro y hy
  rw [mem_conjugate_iff'] at hy
  have h := L.mul_mem (L.mul_mem (L.inv_mem hg) (hX hy)) hg
  rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h

end Pk

end CFSG.OddStandard.SmallF3.Omega
