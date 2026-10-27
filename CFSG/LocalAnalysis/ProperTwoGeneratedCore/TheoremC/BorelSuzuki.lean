module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzukiAut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelSuzukiTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiCoverCentralizer
public import CFSG.StronglyEmbedded.MatrixGroups.SzModel
public import Certificates.Certificate113

public section

namespace CFSG.ProperTwoGeneratedCore.TheoremC

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups

theorem benderBorelFacts_suzukiCoverRoot (m : ℕ) (hm : 0 < m) :
    BenderBorelFacts (SuzukiMatrixGroup m) (suzukiCoverRoot m) where
  commutator_central _ ha _ hb := BorelSuzuki.inCenterOf_commutator m hm ha hb
  sq_central _ ha := BorelSuzuki.inCenterOf_mul_self m hm ha
  torus := ⟨suzukiCoverTorus m, suzukiCoverTorus_odd m hm, suzukiCoverTorus_le_normalizer m,
    (suzukiCoverRoot_normalizer m hm).symm, BorelSuzuki.torus_transitive m hm,
    BorelSuzuki.torus_forms m hm⟩
  center_card := by
    rw [BorelSuzuki.card_inCenterOf m hm]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  aut_inner := BorelSuzuki.aut_inner m hm

theorem suzukiBorelFacts : SuzukiBorelFacts := by
  intro n hn
  rw [show CFSG.Theory.Comparator.SzModel n = SuzukiMatrixGroup n from
    CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n]
  exact ⟨suzukiCoverSylow n (by omega), benderBorelFacts_suzukiCoverRoot n (by omega)⟩

end CFSG.ProperTwoGeneratedCore.TheoremC
