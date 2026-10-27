module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKxDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGDefs
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims138
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup

theorem kFact2024_of_kg2024 : KG2024 → KFact2024 := by
  intro hKG A _ _ L S z n p hLe hn hp hp5 hz hzL hrk hSL hS2 hS hzS
  obtain ⟨e⟩ := hLe
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpn : p ≤ n := by
    have h1 : orderOf (⟨z, hzL⟩ : ↥L) = p := by rw [Subgroup.orderOf_mk, hz]
    have h2 : p ∣ Nat.card ↥L := h1 ▸ orderOf_dvd_natCard _
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at h2
    exact (hp.dvd_factorial).mp (h2.trans (Nat.div_dvd_of_dvd (Nat.dvd_factorial two_pos
      (by omega))))
  have hnp : n < 2 * p := by
    have h1 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims138.le_pRank_of_mulEquiv_alt
      hp hp2 e
    have h2 : n / p ≤ 1 := h1.trans hrk
    by_contra hcon
    have : 2 ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
    omega
  obtain ⟨T, Y, hTS, hT, hzT, -, hY, hzY, hsimp, h3⟩ :=
    hKG A L S z n p (Or.inl ⟨e⟩) hn hp hp5 hpn hnp hz hzL hSL hS2 hS hzS
  refine ⟨T, hTS, hT, hzT, Y, rankThreePrimeCore p Y, hY, hsimp, hzY, ?_, h3⟩
  intro hzN
  have hdvd : orderOf (⟨z, hzN⟩ : ↥(rankThreePrimeCore p Y)) ∣
      Nat.card ↥(rankThreePrimeCore p Y) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hz] at hdvd
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.coprime_card_relPPrimeCore
      hp Y) hdvd)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
