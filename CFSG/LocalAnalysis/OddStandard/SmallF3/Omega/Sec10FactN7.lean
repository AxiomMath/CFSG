module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelT0

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem asc82FactN7_of_cert :
    Asc82FactN7 := by
  intro G _ _ L hL x hx hord P hP
  obtain ⟨F0⟩ := exists_pspFrame hL
  have hxp : orderOf (F0.ψ ⟨x, hx⟩) = 2 := by rw [F0.orderOf_psi]; exact hord
  obtain ⟨c, hc, hcov⟩ := exists_cover (F0.ψ_mem ⟨x, hx⟩) hxp
  obtain ⟨r, hr, hcr⟩ : ∃ r : P45,
      (r = Certificates.OmegaT0.z0 () ∨ r = Certificates.OmegaT0.yB ()) ∧
        c * F0.ψ ⟨x, hx⟩ * c⁻¹ = r := by
    rcases hcov with h | h
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr rfl, h⟩
  have h1 : (F0.conj c hc).ψ ⟨x, hx⟩ = r := by rw [PspFrame.conj_psi, hcr]
  have hC := (F0.conj c hc).img_inf_centralizer_singleton ⟨x, hx⟩
  rw [h1] at hC
  have hPL : P ≤ L := hP.1.trans inf_le_left
  have hS1 : IsSylow2Of ((F0.conj c hc).img P)
      (QP45.originalSubgroup ⊓ centralizer ({r} : Set P45)) := by
    rw [← hC]
    exact (F0.conj c hc).isSylow2Of_img inf_le_left hP
  obtain ⟨-, hSyl, hcomm⟩ := n7_model hr
  obtain ⟨a, ha, hmem⟩ := IsSylow2Of.exists_conj_mem hS1 hSyl
  have haP : a ∈ QP45.originalSubgroup := (Subgroup.mem_inf.1 ha).1
  have har : a * r = r * a := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
  have h2 : ((F0.conj c hc).conj a haP).img P =
      QT0.originalSubgroup ⊓ centralizer ({r} : Set P45) := by
    ext p
    rw [PspFrame.mem_img_conj, ← hmem]
  have h3 : ((F0.conj c hc).conj a haP).ψ ⟨x, hx⟩ = r := by
    rw [PspFrame.conj_psi, h1]
    exact mul_inv_eq_iff_eq_mul.2 har
  rw [← PspFrame.psi_mem_img (F := (F0.conj c hc).conj a haP) (l := ⟨x, hx⟩),
    PspFrame.img_commutator (F := (F0.conj c hc).conj a haP) hPL hPL, h2, h3]
  exact hcomm

end CFSG.OddStandard.SmallF3.Omega
