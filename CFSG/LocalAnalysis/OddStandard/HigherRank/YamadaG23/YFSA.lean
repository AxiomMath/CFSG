module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFNorm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFGen
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFExt

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} (s : Setting3 G L)

theorem fusion32_of_RT (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (h31 : s.Fact31) (hA : LFactsA s) (e : Setting3.Ext s) (hRT : s.R = s.T) : e.Fact32 := by
  have hz : s.fr.z ≠ 1 := by
    intro h
    have h2 : orderOf s.fr.z = 1 := by simp [h]
    exact absurd (h2 ▸ hA.z_order) (by norm_num)
  have hgen : closure (invols s.fr.S) = s.fr.S :=
    srel_closure_invols_S (s3_srel hS hZ s) hz
  have hST : s.fr.S ≤ e.T₁ := (s3_S_le_T s).trans e.T_le
  have hAT : s.fr.A ≤ e.T₁ := (s3_A_le_S s).trans hST
  have hTnorm : (s.T.subgroupOf e.T₁).Normal := s3_T_normal_T1 s hA h31 e
  have hSnorm : (s.fr.S.subgroupOf e.T₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hST]
    intro y k hy hk
    exact s3_inv_arg s hS hZ h31 hA e (s3_S_le_L s) hgen hk (fun y hy => by
      have hyT : y ∈ s.T := s3_S_le_T s hy
      have hkyT : k * y * k⁻¹ ∈ s.T :=
        (Subgroup.normal_subgroupOf_iff (H := s.T) (K := e.T₁) e.T_le).mp hTnorm y k hyT hk
      rw [← hRT] at hkyT
      obtain ⟨w, hwS, hw | hw⟩ := s3_R_cases s hS h31 (k * y * k⁻¹) hkyT
      · exact Or.inl (by rw [hw]; exact hwS)
      · exact Or.inr ⟨w, hwS, hw⟩) y hy
  have hAnorm : (s.fr.A.subgroupOf e.T₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hAT]
    intro a k ha hk
    have hSconj : ∀ b ∈ s.fr.S, k * b * k⁻¹ ∈ s.fr.S :=
      fun b hb => (Subgroup.normal_subgroupOf_iff hST).mp hSnorm b k hb hk
    have hAle : conjSub k s.fr.A ≤ s.fr.S := by
      intro z hz'
      unfold conjSub at hz'
      rcases Subgroup.mem_map.mp hz' with ⟨b, hb, rfl⟩
      simpa [MulAut.conj_apply] using hSconj b (s3_A_le_S s hb)
    have hAeq : conjSub k s.fr.A = s.fr.A :=
      s3_A_unique hS hZ s hAle (isExtraspecialTwo_conjSub k (s3_A_extraspecial hA))
    have h1 : (MulAut.conj k) a ∈ conjSub k s.fr.A := by
      unfold conjSub
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hAeq] at h1
    simpa [MulAut.conj_apply] using h1
  refine ⟨⟨hAT, hAnorm⟩, ⟨hST, hSnorm⟩, ?_, ?_⟩
  · rw [Setting3.Ext.R₁, if_pos hRT]
    exact (inf_eq_right.mpr e.T_le).trans hRT.symm
  · intro hne
    exact absurd hRT hne

end CFSG.OddStandard.HigherRank.YamadaG23
