module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12InputsI
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10FrameB0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10ModelB0Cls
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10PkBasic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatFactsSmall.PSp43

local notation "P45" => Equiv.Perm (Fin 45)

theorem exists_conj_mem_B0
    {p : P45} (hp : p ∈ QP45.originalSubgroup)
    (h2 : orderOf p = 2) : ∃ g ∈ QP45.originalSubgroup, g * p * g⁻¹ ∈ B0 := by
  have hv4 : IsEvenVec (![1, 1, 1, 1, 0] : Fin 5 → ZMod 2) := by
    unfold IsEvenVec
    decide
  have hw4 : vecWeight (![1, 1, 1, 1, 0] : Fin 5 → ZMod 2) = 4 := by
    unfold vecWeight
    decide
  have hv2 : IsEvenVec (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) := by
    unfold IsEvenVec
    decide
  have hw2 : vecWeight (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) = 2 := by
    unfold vecWeight
    decide
  obtain ⟨c, hc, hcov⟩ := Pk.exists_cover_pk hp h2
  rcases hcov with h | h
  · obtain ⟨c', hc', hce⟩ := phiB_class4 hv4 hw4
    refine ⟨c' * c, QP45.originalSubgroup.mul_mem hc' hc, ?_⟩
    rw [show c' * c * p * (c' * c)⁻¹ = c' * (c * p * c⁻¹) * c'⁻¹ by group, h, hce]
    exact phiB_mem_B0 hv4
  · obtain ⟨c', hc', hce⟩ := phiB_class2 hv2 hw2
    refine ⟨c' * c, QP45.originalSubgroup.mul_mem hc' hc, ?_⟩
    rw [show c' * c * p * (c' * c)⁻¹ = c' * (c * p * c⁻¹) * c'⁻¹ by group, h, hce]
    exact phiB_mem_B0 hv2

theorem asc82FactInvB_of_cert :
    Asc82FactInvB := by
  intro G _ _ L hL P hP u hu hsq
  obtain ⟨F0⟩ := exists_pspFrame hL
  obtain ⟨F, hFP⟩ := F0.exists_frame_syl hP
  have hJ : JElem P = F.pre B0 := F.jElem_eq hFP hP.1
  by_cases hu1 : u = 1
  · exact ⟨1, L.one_mem, 1, (JElem P).one_mem, by rw [hu1]; group⟩
  let ul : ↥L := ⟨u, hu⟩
  have hp2 : orderOf (F.ψ ul) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, show ul * ul = 1 from Subtype.ext hsq, map_one]
    · intro h
      exact hu1 (congrArg Subtype.val (F.ψ_injective (h.trans (map_one F.ψ).symm)))
  obtain ⟨g, hg, hgB⟩ := exists_conj_mem_B0 (F.ψ_mem ul) hp2
  obtain ⟨l0, hl0⟩ := F.ψ_surj hg
  have hψb : F.ψ (l0 * ul * l0⁻¹) = g * F.ψ ul * g⁻¹ := by
    rw [map_mul, map_mul, map_inv, hl0]
  refine ⟨((l0⁻¹ : ↥L) : G), (l0⁻¹).2, ((l0 * ul * l0⁻¹ : ↥L) : G), ?_, ?_⟩
  · rw [hJ]
    exact PspFrame.mem_pre.2 ⟨(l0 * ul * l0⁻¹).2, by
      show F.ψ (l0 * ul * l0⁻¹) ∈ B0
      rw [hψb]
      exact hgB⟩
  · simp [ul]

end CFSG.OddStandard.SmallF3.Omega
