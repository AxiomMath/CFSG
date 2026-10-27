module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BHat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BKL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109BRank

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step109B_of (hKL : Asc82StepKL) (h3 : Asc82Sec3Res10) (h : Asc82Res10a)
    (hf : Asc82Facts10) (hfB : Asc82FactsB) (hb : Asc82Basic10) : Asc82Step109B := by
  intro G _ _ t L S z K1 K2 g hctx c hc hle
  have hmem := sec10B_t_mem_conj h3 h hf hfB.rank hb hctx hc hle
  obtain ⟨ht2, hz2, -, -, -, htz⟩ := sec10D_basic hb hctx.toSec10Ctx
  obtain ⟨-, htC, -, -, -, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨q, hqQ, hq⟩ := sec10J_mem_W hf.pockets5 hb hctx.toSec10Ctx _ hmem
  have hqL : q ∈ L := (sec10J_Q_le hf.pockets5 hb hctx.toSec10Ctx hqQ).2
  rcases hq with hq | hq
  · exfalso
    refine h.l108 G t L S z K1 K2 hctx.toSec10Ctx c⁻¹ ?_
    rw [inv_inv, hq]
    exact hqL
  · have hqt : q * t = t * q := Subgroup.mem_centralizer_iff.mp htC q hqL
    have hq2 : q * q = 1 := by
      have e : (q * t) * (q * t) = q * q := by
        calc (q * t) * (q * t) = q * (t * q) * t := by group
          _ = q * (q * t) * t := by rw [hqt]
          _ = q * q * (t * t) := by group
          _ = q * q := by rw [ht2, mul_one]
      have hct2 : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
        calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
          _ = 1 := by rw [ht2]; group
      rw [hq, e] at hct2
      exact hct2
    by_cases hqz : q ∈ zpowers z
    · refine sec10B_conjugate_eq_of_conj_t h3 h hf hb hctx.toSec10Ctx hc ?_
      rcases sec10D_eq_one_or_of_mem_zpowers hz2 hqz with h1 | h1
      · left
        rw [hq, h1, one_mul]
      · right
        rw [hq, h1]
        exact htz.symm
    · exfalso
      refine sec10B_no_conj_tq hKL h3 h hf hfB.q2m hb hctx hqQ hq2 hqz (k := c⁻¹) ?_
      rw [inv_inv, hq, hqt]

end CFSG.OddStandard.SmallF3.Omega
