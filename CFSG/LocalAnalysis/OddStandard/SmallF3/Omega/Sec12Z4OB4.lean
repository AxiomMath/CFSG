module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Z4ODefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82StepZ4NoOuterInv_of (hp : Asc82Pre11) (hC : Asc82StepZ4Cent)
    (hComp : Asc82StepZ4Comp) : Asc82StepZ4NoOuterInv := by
  intro G _ _ t L S z K1 K2 E hctx hZ s hsS hss
  by_contra hsK
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  obtain ⟨-, -, -, htS, -, -⟩ := hp.basic G t L S z hctx.toSec10Z
  have hs1 : s ≠ 1 := fun h => hsK (by rw [h]; exact one_mem _)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  rcases hC G t L S z K1 K2 E hctx hZ s hs2 hsS hsK with h | h
  · exact hComp G t L S z K1 K2 E hctx hZ s hs2 hsS hsK h
  ·
    have hts : t * s = s * t :=
      Subgroup.mem_centralizer_iff.mp (hctx.sylow.1 hsS) t (Set.mem_singleton t)
    have htt : t * t = 1 := by
      rw [← sq, ← F.ht2]
      exact pow_orderOf_eq_one t
    have hst2 : s * t * (s * t) = 1 := by
      calc s * t * (s * t) = s * (t * s) * t := by group
        _ = s * (s * t) * t := by rw [hts]
        _ = s * s * (t * t) := by group
        _ = 1 := by rw [hss, htt, one_mul]
    have hstK : s * t ∉ L ⊔ centralizer (L : Set G) := fun h1 => hsK (by
      have h2 := Subgroup.mul_mem _ h1 (Subgroup.mem_sup_right (inv_mem F.htC))
      rwa [mul_inv_cancel_right] at h2)
    have hst1 : s * t ≠ 1 := fun h1 => hstK (by rw [h1]; exact one_mem _)
    exact hComp G t L S z K1 K2 E hctx hZ (s * t)
      (orderOf_eq_prime (by rw [sq]; exact hst2) hst1) (mul_mem hsS htS) hstK h

end CFSG.OddStandard.SmallF3.Omega
