module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PS6

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec11d2_mul_self_of_mem_sup {t z d : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) (hd : d ∈ zpowers t ⊔ zpowers z) : d * d = 1 := by
  obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute (H := zpowers t)
    (K := zpowers z)
    (fun a ha b hb => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((show Commute t z from htz).zpow_zpow m n).eq) hd
  rcases sec11d2_zpowers_cases ht2 hx with h1 | h1 <;>
    rcases sec11d2_zpowers_cases hz2 hy with h2 | h2
  · rw [h1, h2]
    simp
  · rw [h1, h2, one_mul]
    exact hz2
  · rw [h1, h2, mul_one]
    exact ht2
  · rw [h1, h2]
    calc t * z * (t * z) = t * (z * t) * z := by group
      _ = t * (t * z) * z := by rw [htz]
      _ = (t * t) * (z * z) := by group
      _ = 1 := by rw [ht2, hz2, one_mul]

theorem asc82Step118D2_of (hp : Asc82Pre11) (r : Asc82Res11a) (h116 : Asc82Lemma116)
    (h117 : Asc82Lemma117) : Asc82Step118D2 := by
  intro G _ _ t L S z K1 K2 T R hctx d hd q hq hd2 hq2 h hh hs
  rcases r.l112 G t L S z K1 K2 T R hctx with ⟨hA6, hCT⟩ | ⟨-, -, -, -, hD8, -⟩
  ·
    have hRT : R = T := r.l115b G t L S z K1 K2 T R hctx hA6
    obtain ⟨ht2, hz2, htz, -, hz1⟩ := sec11_invols hctx.toSec10Ctx
    have hdT : d ∈ zpowers t ⊔ zpowers z := by
      rw [← hCT]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hd).1, hRT ▸ (Subgroup.mem_inf.mp hd).2⟩
    exact hz1 (hd2.symm.trans (sec11d2_mul_self_of_mem_sup ht2 hz2 htz hdT))
  ·
    exact sec11d2_S6 hp r h116 h117 hctx hD8 hd hq hd2 hq2 hh hs

end CFSG.OddStandard.SmallF3.Omega
