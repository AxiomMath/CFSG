module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10RSeitzEvenCentreLift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SplitTwistedA

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB


theorem noncentralWitness_twA {K : Type} [Group K] [Finite K] {lab : GLALabel}
    (hK : Rk2IsLabel K lab) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (htag : lab.tag = .twA)
    (hpq : p ∣ 2 ^ lab.n + 1) :
    NoncentralWitness K p (lab.rank - 2 + CFSG.Open.pRank p (Subgroup.center K)) := by
  obtain ⟨R, hR, θ, h, w, X, hpow, hcomm, hind, hinv, hcross, hX1, hX2, hNX⟩ :=
    exists_crossedInversionBasis_twA hK hp hp2 htag hpq
  letI := hR
  exact noncentralWitness_of_central_lift θ hp hp2 hpow hcomm hind hinv hcross hX1 hX2 hNX

theorem seitzEvenCentre_twA5 {K : Type} [Group K] [Finite K]
    (hK : Rk2IsLabel K ⟨.twA, 5, 1⟩) : NoncentralWitness K 3 3 := by
  have h := noncentralWitness_twA (p := 3) hK (by norm_num) (by norm_num) rfl (by norm_num)
  exact noncentralWitness_three (q := 3) (by norm_num) (Nat.le_add_right 3 _) h

end CFSG.LocalAnalysis.GLTheoremA.Y10F
