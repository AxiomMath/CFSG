module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGD2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCCos

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec9CosI1_of (hT6 : Asc82Tab6M) : Asc82Sec9CosI1 := by
  intro G _ _ L hL P hP B hBP hB y hy2 hyN hyB hyout
  obtain ⟨V, _, _, _, Q, hQ, e, hm, F, hF16, hlift, hFmem, hFsurj⟩ :=
    sec9g_model_E16 hT6 G L hL P hP B hBP hB
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    hBP.trans (hP.1.trans Subgroup.le_normalizer)
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e
  have hu : ∀ f ∈ F, Φ ⟨y, hyN⟩ * f = f * Φ ⟨y, hyN⟩ := by
    intro f hf
    obtain ⟨b, hb, hbf⟩ := hFsurj f hf
    rw [← hbf, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hyB b hb)
  have hnot : Φ ⟨y, hyN⟩ ∉ F := by
    intro hmem
    obtain ⟨b, hb, hbf⟩ := hFsurj (Φ ⟨y, hyN⟩) hmem
    have hΦ1 : Φ (⟨b, hBN hb⟩⁻¹ * ⟨y, hyN⟩) = 1 := by
      rw [map_mul, map_inv, hbf, inv_mul_cancel]
    have hcent : b⁻¹ * y ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf _).mp hΦ1
    have hbL : b ∈ L := (hBP.trans hP.1) hb
    exact hyout (by
      rw [InnerOn, show y = b * (b⁻¹ * y) from by group]
      exact Subgroup.mul_mem_sup hbL hcent)
  obtain ⟨f, hfF, hdim⟩ := sec9g_i1_of_coset hQ hm.1 F hF16 hlift hu hnot
  obtain ⟨b, hb, hbf⟩ := hFsurj f hfF
  have hdim' : SimHasDim (Φ ⟨y * b, Subgroup.mul_mem _ hyN (hBN hb)⟩) 1 := by
    have heq : Φ ⟨y * b, Subgroup.mul_mem _ hyN (hBN hb)⟩ = Φ ⟨y, hyN⟩ * f := by
      rw [← hbf, ← map_mul]
      congr 1
    rw [heq]
    exact hdim
  obtain ⟨α, hα⟩ := sec9g_simHasType_of_simHasDim hQ hm.1 (le_refl 1) (by norm_num) hdim'
  exact ⟨b, hb, α, V, inferInstance, inferInstance, inferInstance, Q, hQ, e,
    Φ ⟨y * b, Subgroup.mul_mem _ hyN (hBN hb)⟩, hm.1, hm.2,
    ffInducesHom_spec hm e ⟨y * b, Subgroup.mul_mem _ hyN (hBN hb)⟩, hα⟩

end CFSG.OddStandard.SmallF3.Omega
