module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171InnerU6Trans

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171U6

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.KU6Cent
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

theorem stepPat_holds : StepPat := by
  intro hPat Ω _ _ B x L _ e hs hPR D K hpre _ hKsimple hKcard d hd hdx g hg
  haveI hLperf : Group.IsPerfect ↥L := isPerfect_of_cfg hs.cfg
  have hdB : d ∈ B := hpre.1 hd
  have hdCentK : d ∈ Subgroup.centralizer (K : Set Ω) := (hpre.2.2.2.2.2.2 ▸ hd).2
  have hcommd : ∀ k ∈ K, d * k = k * d := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp hdCentK k hk).symm
  have hg3 : g ^ 3 = 1 := by
    apply Psi_injective
    rw [map_pow, hg, ← map_pow, hs.cfg.elem.2 d hdB, map_one, map_one]
  have hgne : g ≠ 1 := by
    intro h1
    have htheta : theta L e d = 1 := by rw [← hg, h1, map_one]
    exact hdx ((hs.cfg.cent d hdB).mp ((theta_eq_one_iff e d).mp htheta))
  have hnotPR : ¬ IsPR g := hPR d hdB g hg
  have hKL : K ≤ L := fun k hk => (hpre.2.2.2.2.2.1.1 hk).1
  have hKq : CFSG.Open.IsQuasisimple ↥K := hpre.2.2.2.2.2.1.2.2
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨hKq.1⟩
  have hJperf : ⁅imL e K, imL e K⁆ = imL e K := imL_perfect e hKL hKperf
  have h5 : 5 ∣ Nat.card (imL e K) := by
    rw [card_imL e hKL hKsimple hKperf, hKcard]
    norm_num
  have hJfix : imL e K ≤ fixSubgroup (Psi g) := by
    rw [hg]
    exact imL_le_fixSubgroup e hcommd
  exact hPat g (imL e K) hg3 hgne hnotPR hJfix hJperf h5

end CFSG.LocalAnalysis.GLTheoremA.T171U6

end
