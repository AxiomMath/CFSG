module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3CaseA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Embed
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3L34
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Harris

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.EvenSporadicStandard.HSStd

theorem s3_of (hHar : Harada39One) (hOv : HaradaOvergroups)
    (hL34 : HaradaL34Data) (hc : HarrisContra) (hF : FusionA) : StepS3 := by
  intro G _ _ L t E W z hb a
  have hsh := a.dshape hb
  obtain ⟨ec⟩ := hsh.centEquiv
  have hord := hsh.orderOf_t
  have hu : a.u ∈ L ⊓ Cen a.y := a.K₀_le a.u_mem
  have hswap : (a.eKb ⟨oMk (Cen a.y) ⟨a.u, a.K₀_le_cen a.u_mem⟩, a.mem_Kb a.u_mem⟩).IsSwap := by
    have : a.eKb ⟨oMk (Cen a.y) ⟨a.u, a.K₀_le_cen a.u_mem⟩, a.mem_Kb a.u_mem⟩ =
        a.eK₀ ⟨a.u, a.u_mem⟩ := a.eKb_kmapEquiv ⟨a.u, a.u_mem⟩
    rw [this]
    exact a.u_swap
  have hKD : CFSG.SectionRank.IsKGroupCat (OQuot (Cen a.y)) :=
    (hb.setting.1.isKGroupCat_centralizer_of_orderOf (n := 3) (by norm_num) a.y_ord).quotient _
  have hlist := hHar (OQuot (Cen a.y)) hKD hsh.zstar a.tb hord ⟨ec⟩
  rcases hlist with he | h2 | h3 | h4 | he5 | h6 | h7
  · obtain ⟨e⟩ := he
    obtain ⟨c⟩ := caseA_data hsh e
    obtain ⟨ι, hinj, ht, halt, hrange, hι⟩ := caseA_embed hsh c a.eKb
    obtain ⟨σ, hσ, hσ'⟩ := hι _ (a.mem_Kb a.u_mem) hswap
    exact ⟨{ toPA2 := a
             ι := ι
             ι_inj := hinj
             ι_t := ht
             ι_alt := halt
             ι_range := hrange
             ι_u := ⟨σ, hσ, hσ'⟩ }⟩
  · exact (hOv _ hsh.zstar a.tb hord ⟨ec⟩ (Or.inl h2) a.rank4_D).elim
  · exact (hOv _ hsh.zstar a.tb hord ⟨ec⟩ (Or.inr (Or.inl h3)) a.rank4_D).elim
  · exact (hOv _ hsh.zstar a.tb hord ⟨ec⟩ (Or.inr (Or.inr (Or.inl h4))) a.rank4_D).elim
  · exact (hOv _ hsh.zstar a.tb hord ⟨ec⟩ (Or.inr (Or.inr (Or.inr (Or.inl he5)))) a.rank4_D).elim
  · exact (hOv _ hsh.zstar a.tb hord ⟨ec⟩ (Or.inr (Or.inr (Or.inr (Or.inr h6)))) a.rank4_D).elim
  · exfalso
    obtain ⟨o, ho, h7', hnc⟩ := hL34 (OQuot (Cen a.y)) hsh.zstar a.tb a.Kb hord hsh.cent hsh.disj
      a.eKb h7 (oMk (Cen a.y) ⟨a.u, a.K₀_le_cen a.u_mem⟩) (a.mem_Kb a.u_mem) hswap
    rcases ho with rfl | ho
    · exact l34_false hc hF hb a a.u (Or.inl rfl) hu.2 h7' hnc
    · have ho' : o = a.tb * oMk (Cen a.y) ⟨a.u, a.K₀_le_cen a.u_mem⟩ := ho
      have hwy : t * a.u ∈ Cen a.y := mul_mem a.t_cy hu.2
      have hoeq : o = oMk (Cen a.y) ⟨t * a.u, hwy⟩ := by
        rw [ho']
        exact (map_mul (oMk (Cen a.y)) _ _).symm
      rw [hoeq] at h7' hnc
      exact l34_false hc hF hb a (t * a.u) (Or.inr rfl) hwy h7' hnc

theorem s3 (hHar : Harada39One) (hHs : Harris311)
    (hOv : HaradaOvergroups) (hL34 : HaradaL34Data) (h7 : ThreeCentralizer7) (hF : FusionA) :
    StepS3 :=
  s3_of hHar hOv hL34 (harris_contra hHs h7) hF

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
