module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118S6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma118_of (hp : Asc82Pre11) (r : Asc82Res11a) (h116 : Asc82Lemma116)
    (h117 : Asc82Lemma117) (hD2 : Asc82Step118D2) : Asc82Lemma118 := by
  intro G _ _ t L S z K1 K2 T R hctx h hh hs
  have h10 : Sec10Ctx G t L S z K1 K2 := hctx.toSec10Ctx
  have hP5 := hp.facts.pockets5
  have hC5 := hp.facts.centZ5
  have hpsp : IsPSp43 L := (hp.basic G t L S z hctx.toSec10Z).1
  obtain ⟨-, hz2, -, -, hz1⟩ := sec11_invols h10
  obtain ⟨hzQ, -, -, -, -⟩ := sec11_Q_facts hp h10
  have htD : t ∈ secD K1 K2 R := sec11_t_mem_D hp hctx
  have hzD : z ∈ secD K1 K2 R := sec11_z_mem_D hp hctx
  have hDQ : ∀ x ∈ secD K1 K2 R, ∀ y ∈ secQ K1 K2, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1 y hy).symm
  rcases r.l112 G t L S z K1 K2 T R hctx with ⟨hA6, hCT⟩ | ⟨-, -, -, -, hD8, -⟩
  ·
    have hRT : R = T := r.l115b G t L S z K1 K2 T R hctx hA6
    have hDle : secD K1 K2 R ≤ zpowers t ⊔ zpowers z := by
      intro x hx
      rw [← hCT]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, hRT ▸ (Subgroup.mem_inf.mp hx).2⟩
    have hle : secD K1 K2 R ⊔ secQ K1 K2 ≤ secW t K1 K2 := by
      refine sup_le (hDle.trans (sup_le ?_ ?_)) le_sup_left
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hzQ)
    have hsW : h⁻¹ * t * h ∈ secW t K1 K2 ⊔ zpowers z := Subgroup.mem_sup_left (hle hs)
    rcases sec11_strClosed_secW hp h10 hctx.hyp h hh hsW with e | e
    · rw [e]; exact htD
    · rw [e]; exact Subgroup.mul_mem _ htD hzD
  ·
    obtain ⟨d, hd, q, hq, hsdq⟩ := exists_mul_of_mem_sup_of_commute hDQ hs
    have hdq : d * q = q * d := hDQ d hd q hq
    have ht2' : (h⁻¹ * t * h) * (h⁻¹ * t * h) = 1 := by
      obtain ⟨ht2, -, -, -, -⟩ := sec11_invols h10
      calc (h⁻¹ * t * h) * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
        _ = 1 := by rw [ht2]; group
    have hdd_qq : (d * d) * (q * q) = 1 := by
      rw [hsdq] at ht2'
      calc (d * d) * (q * q) = d * (d * q) * q := by group
        _ = d * (q * d) * q := by rw [hdq]
        _ = (d * q) * (d * q) := by group
        _ = 1 := ht2'
    have hddQ : d * d ∈ secQ K1 K2 := by
      rw [eq_inv_of_mul_eq_one_left hdd_qq]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hq hq)
    have hddz : d * d ∈ zpowers z :=
      sec10KS_Q_center hP5 hC5 hpsp h10 (d * d) hddQ
        (fun y hy => hDQ (d * d) (Subgroup.mul_mem _ hd hd) y hy)
    rcases sec11_eq_one_or_of_mem_zpowers hz2 hddz with hdd | hdd
    ·
      have hqq : q * q = 1 := by rw [hdd, one_mul] at hdd_qq; exact hdd_qq
      by_cases hqz : q ∈ zpowers z
      · have hqD : q ∈ secD K1 K2 R := by
          rcases sec11_eq_one_or_of_mem_zpowers hz2 hqz with e | e
          · rw [e]; exact Subgroup.one_mem _
          · rw [e]; exact hzD
        rw [hsdq]
        exact Subgroup.mul_mem _ hd hqD
      · exact (sec11_118_S6 hp r h116 h117 hctx hD8 hd hq hdq hdd hqq hqz hh hsdq).elim
    ·
      have hqq : q * q = z := by
        rw [hdd] at hdd_qq
        rw [eq_inv_of_mul_eq_one_right hdd_qq]
        exact inv_eq_of_mul_eq_one_right hz2
      exact (hD2 G t L S z K1 K2 T R hctx d hd q hq hdd hqq h hh hsdq).elim

end CFSG.OddStandard.SmallF3.Omega
