module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtDict
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzJtMod
public import Certificates.Data.FzJtCheck

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup Certificates.FzJ36 Certificates.FzFus Certificates.FzJt

theorem fzCalZPairR3_of_model (h : F3Fact) : FzCalZPairR3 := by
  intro G _ _ _ t L S T₂ x₁ x₂ lam rho tau a₁₂ a₂₂ a₃₂ hset a ha ha2 v hv w hw hv2 hw2 hv1 hw1
    hvw hcomm
  obtain ⟨ht2, h1, h2, -⟩ := fzFus_rels hset
  obtain ⟨π, hd, hπ3⟩ := fzJt_dict hset.shape ht2 h1 h2
  obtain ⟨q, rfl⟩ := (fzJt_mem_fzR3_iff hset.shape hπ3).mp ha
  have hq : q * q = QuaternionGroup.a 2 := fzJt_R3_sq hd ha2
  obtain ⟨mv, rfl⟩ := hd.mem_T₂_iff.mp hv.1
  obtain ⟨mw, rfl⟩ := hd.mem_T₂_iff.mp hw.1
  have hIv : IsInvM mv := (hd.isInvM_iff mv).mpr ⟨by rw [← pow_two]; exact hv2, hv1⟩
  have hIw : IsInvM mw := (hd.isInvM_iff mw).mpr ⟨by rw [← pow_two]; exact hw2, hw1⟩
  have hcv : KEq (mv * mkE 1 1 q) (mkE 1 1 q * mv) := by
    refine (hd.eq_iff _ _).mp ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hv.2
  have hcw : KEq (mw * mkE 1 1 q) (mkE 1 1 q * mw) := by
    refine (hd.eq_iff _ _).mp ?_
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hw.2
  have hne : ¬ KEq mv mw := fun hk => hvw ((hd.eq_iff _ _).mpr hk)
  have hc : KEq (mv * mw) (mw * mv) := by
    refine (hd.eq_iff _ _).mp ?_
    rw [map_mul, map_mul]
    exact hcomm
  rcases h q hq mv mw hIv hIw hcv hcw hne hc with hz | hz | hz
  · exact Or.inl ((fzJt_mem_calZ_iff hd mv).mpr hz)
  · exact Or.inr (Or.inl ((fzJt_mem_calZ_iff hd mw).mpr hz))
  · refine Or.inr (Or.inr ?_)
    rw [← map_mul]
    exact (fzJt_mem_calZ_iff hd (mv * mw)).mpr hz

end CFSG.OddStandard.SmallF3.FritzII
