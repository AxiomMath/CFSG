module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173AMExcComm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

private theorem map_conj_map {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') (K : Subgroup Ω)
    (a : Ω) : (K.map (MulAut.conj a).toMonoidHom).map π =
      (K.map π).map (MulAut.conj (π a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp

theorem uexc_closureIn_map {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') (K N : Subgroup Ω) :
    (closureIn K N).map π = closureIn (K.map π) (N.map π) := by
  apply le_antisymm
  · unfold closureIn
    rw [Subgroup.map_iSup]
    refine iSup_le fun a => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ha => ?_
    rw [map_conj_map]
    exact le_iSup₂_of_le (π a) (Subgroup.mem_map_of_mem π ha) le_rfl
  · unfold closureIn
    refine iSup₂_le fun g hg => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hg
    rw [← map_conj_map]
    exact Subgroup.map_mono (le_iSup₂_of_le a ha le_rfl)

theorem uexc_hc_map {Ω Ω' : Type} [Group Ω] [Group Ω'] (π : Ω →* Ω') {S B N K : Subgroup Ω}
    (hS : S.Normal) (hkc : π.ker ≤ Subgroup.centralizer (S : Set Ω)) (hKS : K ≤ S)
    (hKperf : ⁅K, K⁆ = K)
    (hc : ∃ T : Subgroup Ω, T ≤ S ∧ IsPGroup 2 T ∧
      closureIn K N ⊔ B ≤ Subgroup.normalizer (T : Set Ω) ∧
      (⁅closureIn K N, T⁆ : Subgroup Ω) ≠ ⊥) :
    ∃ T : Subgroup Ω', T ≤ S.map π ∧ IsPGroup 2 T ∧
      closureIn (K.map π) (N.map π) ⊔ B.map π ≤ Subgroup.normalizer (T : Set Ω') ∧
      (⁅closureIn (K.map π) (N.map π), T⁆ : Subgroup Ω') ≠ ⊥ := by
  obtain ⟨T, hTS, hT2, hTN, hTne⟩ := hc
  have hIS : closureIn K N ≤ S := by
    unfold closureIn
    refine iSup₂_le fun a _ => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact hS.conj_mem k (hKS hk) a
  have hperf : ⁅closureIn K N, closureIn K N⁆ = closureIn K N := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g₁ h₁ g₂ h₂
      rw [commutatorElement_def]
      exact (closureIn K N).mul_mem ((closureIn K N).mul_mem ((closureIn K N).mul_mem h₁ h₂)
        ((closureIn K N).inv_mem h₁)) ((closureIn K N).inv_mem h₂)
    · unfold closureIn
      refine iSup₂_le fun a ha => ?_
      have hle : K.map (MulAut.conj a).toMonoidHom ≤
          ⁅closureIn K N, closureIn K N⁆ := by
        have hK' : K.map (MulAut.conj a).toMonoidHom =
            ⁅K.map (MulAut.conj a).toMonoidHom, K.map (MulAut.conj a).toMonoidHom⁆ := by
          rw [← Subgroup.map_commutator, hKperf]
        rw [hK']
        exact Subgroup.commutator_mono (le_iSup₂_of_le a ha le_rfl)
          (le_iSup₂_of_le a ha le_rfl)
      exact hle
  refine ⟨T.map π, Subgroup.map_mono hTS, hT2.map π, ?_, ?_⟩
  · rw [← uexc_closureIn_map, ← Subgroup.map_sup]
    exact (Subgroup.map_mono hTN).trans (Subgroup.le_normalizer_map π)
  · rw [← uexc_closureIn_map, ← Subgroup.map_commutator]
    intro hbot
    apply hTne
    have hle : ⁅closureIn K N, T⁆ ≤ π.ker := (Subgroup.map_eq_bot_iff _).1 hbot
    exact uexc_comm_eq_bot hperf
      (hle.trans (hkc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hIS))))

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
