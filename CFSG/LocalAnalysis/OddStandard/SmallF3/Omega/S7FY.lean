module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FHyp62
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FYCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.S7FYCStar
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63ArrowAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Final7Y_of_sec7 (h33 : Asc82Lemma33) (h35 : Asc82Lemma35) (h36 : Asc82Lemma36)
    (h63 : Asc82Lemma63) (h78 : Asc82Lemma78) (hsh : Asc82Shapes) (hP : Asc82Tab6P)
    (hM : Asc82Tab6M) (hF : Asc82AutFacts) (hZ : Asc82ZExists) (h76c : Asc82Lemma76Choice)
    (h79a : Asc82Lemma79a) : Asc82Final7Y := by
  intro G _ _ t L S z g B E U hU b hbB hb1 hbt
  have hE : Sec7E G t L S z g B E := hU.hE
  have hc : Sec7Choice G t L S z g B := hE.choice
  have hctx : Sec7Ctx G t L S z := hc.ctx
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hc.normalE16.2.1.1.2 b hbB) hb1
  have hbL : b ∈ L := (hc.normalE16.1 hbB).2
  have hHyp : Asc82Hyp62 G := s7f_hyp62 hZ h76c h79a hS
  obtain ⟨Y, hYc, hYF, hXY⟩ := s7f_exists_Y h36 hP h63 hctx hHyp hb2 hbL hbt
  have hYn := s7f_normal_of_63 h63 hS hHyp hb2 hYc hYF
  have hEY : E ≤ normalizer (Y : Set G) := fun e he =>
    sec64_mem_normalizer h63 hS hHyp hb2 hYc hYF (Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (hE.sylow.1 he).2 b hbB).symm)
  have hX : IsL29 (layerCent L b) :=
    hP.layer_i2 G L hctx.isOm6P b hb2 (Subgroup.le_normalizer hbL) hbt
  have hXq : IsQuasisimple ↥(layerCent L b) :=
    (isComponentIn_layerCent (Or.inr (Or.inl hX))).isQuasisimple
  have hYq := hYc.isQuasisimple
  have hX360 : ctrQ (layerCent L b) = 360 := ctrQ_of_l29 hXq hX
  have hshape : IsOmega5 Y ∨ IsOmega6Plus Y ∨ IsL281 Y := by
    rcases sec65_shape hsh hS ⟨b, hb2, hYc⟩ hYF with h | h | h | h | h | h
    · exfalso
      have heq : layerCent L b = Y :=
        eq_of_le_of_ctrQ_eq hYq hXY (by rw [hX360, ctrQ_of_l29 hYq h])
      have htY : t ∈ centralizer (Y : Set G) := by
        rw [← heq]
        refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
        exact Subgroup.mem_centralizer_iff.mp hctx.t_mem_centralizer x (s7f_layerCent_le L b hx)
      exact s7f_not_mem_tB h36 hP hE hEY hXq hXY ⟨1, B.one_mem, (mul_one t).symm⟩ htY
    · exact Or.inr (Or.inr h)
    · exfalso
      have hdvd := ctrQ_dvd_of_le hXY
      rw [hX360] at hdvd
      rcases h with h | h
      · rw [ctrQ_of_l33 hYq h] at hdvd
        omega
      · rw [ctrQ_of_u33 hYq h] at hdvd
        omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact (s7f_not_om6m h36 h35 hP hM hF hctx hb2 hbL hbt hb2 hYc hYn hYF hXY h).elim
  have hYC : InCStar Y := by
    rcases hshape with h | h | h
    · exact s7f_inCStar_om5 h35 h36 h63 hsh hP hM hF hctx hHyp hb2 hbL hbt hb2 hYc hYF hXY h
    · exact s7f_inCStar_om6p hsh hS hb2 hYc h
    · exact s7f_inCStar_l281 hsh hS hb2 hYc hYF h
  refine ⟨Y, hYc, hYn, hYF, hYC, hXY, ?_, hEY,
    s7f_cent_A h36 hP hF h78 h79a hE hbB hb1 hbt hYc.1 hEY hXq hXY,
    sec63_isCyclic_inf h33 hS hYC hYF hE.sylow.2.1⟩
  rcases hshape with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr h))

end CFSG.OddStandard.SmallF3.Omega
