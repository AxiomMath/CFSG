module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L124Z4Sigma
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L122Yc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

theorem sec124_exists_u (F : Sec12Frame t L S) {X0 : Subgroup G}
    (hX0B : X0 ⊓ secB S L = ⊥) (hX0sup : X0 ⊔ secB S L = (secM t S L ⊓ L) ⊔ S)
    {φ : (Fin 5 → ZMod 2) → G}
    (hperm : IsPermModuleVia IsEvenVec φ (secB S L) (secM t S L ⊓ L)
      (alternatingGroup (Fin 5))) :
    ∃ u ∈ secM t S L ⊓ L, u * u = 1 ∧
      ∀ v, IsEvenVec v → u * φ v * u⁻¹ = φ (permVec sec124Sigma v) := by
  obtain ⟨y, hy, hyσ⟩ := hperm.2.2.2.2 sec124Sigma sec124Sigma_mem
  have hφB : ∀ v, IsEvenVec v → φ v ∈ secB S L := fun v hv =>
    (hperm.2.2.1 (φ v)).mpr ⟨v, hv, rfl⟩
  have hBY : secB S L ≤ secM t S L ⊓ L :=
    le_inf ((le_sup_left : secB S L ≤ secA t S L).trans Subgroup.le_normalizer) F.bdata.1
  have hX0Yc : X0 ≤ (secM t S L ⊓ L) ⊔ S := by rw [← hX0sup]; exact le_sup_left
  have hX0N : X0 ≤ normalizer (secB S L : Set G) := hX0Yc.trans (sec122_Yc_le_normalizer_B F)
  have hyYc : y ∈ X0 ⊔ secB S L := by rw [hX0sup]; exact Subgroup.mem_sup_left hy
  have hy' : y ∈ (X0 : Set G) * (secB S L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right X0 (secB S L) hX0N]
    exact hyYc
  obtain ⟨x, hxX, b, hbB, hxb⟩ := Set.mem_mul.mp hy'
  have hx_eq : x = y * b⁻¹ := by rw [← hxb]; group
  have hxY : x ∈ secM t S L ⊓ L := by
    rw [hx_eq]
    exact (secM t S L ⊓ L).mul_mem hy ((secM t S L ⊓ L).inv_mem (hBY hbB))
  have hact : ∀ v, IsEvenVec v → x * φ v * x⁻¹ = φ (permVec sec124Sigma v) := by
    intro v hv
    have hcomm : b⁻¹ * φ v * b = φ v := by
      have h := sec12E_B_comm F hbB (hφB v hv)
      rw [show b⁻¹ * φ v * b = b⁻¹ * (φ v * b) by group, ← h]
      group
    rw [hx_eq]
    calc (y * b⁻¹) * φ v * (y * b⁻¹)⁻¹ = y * (b⁻¹ * φ v * b) * y⁻¹ := by group
      _ = y * φ v * y⁻¹ := by rw [hcomm]
      _ = φ (permVec sec124Sigma v) := hyσ v hv
  refine ⟨x, hxY, ?_, hact⟩
  have hxx_cent : x * x ∈ centralizer (secB S L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    obtain ⟨v, hv, rfl⟩ := (hperm.2.2.1 c).mp hc
    have hv' : IsEvenVec (permVec sec124Sigma v) := isEvenVec_permVec _ hv
    have h2 : x * x * φ v * (x * x)⁻¹ = φ v := by
      calc x * x * φ v * (x * x)⁻¹ = x * (x * φ v * x⁻¹) * x⁻¹ := by group
        _ = x * φ (permVec sec124Sigma v) * x⁻¹ := by rw [hact v hv]
        _ = φ (permVec sec124Sigma (permVec sec124Sigma v)) := hact _ hv'
        _ = φ v := by rw [permVec_sec124Sigma_twice]
    have h3 := congrArg (· * (x * x)) h2
    simp only [inv_mul_cancel_right] at h3
    exact h3.symm
  have hxxB : x * x ∈ secB S L := by
    have h : x * x ∈ centralizer (secB S L : Set G) ⊓ L :=
      ⟨hxx_cent, L.mul_mem hxY.2 hxY.2⟩
    rwa [F.bdata.2.2.1] at h
  have hxxbot : x * x ∈ X0 ⊓ secB S L := ⟨X0.mul_mem hxX hxX, hxxB⟩
  rw [hX0B] at hxxbot
  simpa using hxxbot

end CFSG.OddStandard.SmallF3.Omega
