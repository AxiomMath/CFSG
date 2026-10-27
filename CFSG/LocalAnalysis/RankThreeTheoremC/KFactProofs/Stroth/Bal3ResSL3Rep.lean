module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec12.Item128StepsProofSLFacts
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem pRank_le_two_of_isSLThreePi {K : Type} [Group K] [Finite K] (hK : IsSLThreePi K) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 :=
  CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => by
    have h := Sec12.Item128StepsProof.card_le_nine_of_isSLThreePi hK E
      (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
      (fun x hx => hE.2 x hx)
    simpa using h

theorem pow_three_eq_one_of_not_dvd_243 {K : Type} [Group K] [Finite K] (hK : IsSLThreePi K)
    (h243 : ¬ 243 ∣ Nat.card K) {s : K} (hs : s ^ 3 ∈ Subgroup.center K) : s ^ 3 = 1 := by
  obtain ⟨q, hXq⟩ := hK
  obtain ⟨π, p, f, K', _, hK', hq, hpq, ⟨e⟩⟩ := Sec12.Item128StepsProof.exists_model hXq
  have hcard : Nat.card K =
      (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) * cond π ((p ^ f) ^ 3 - 1) ((p ^ f) ^ 3 + 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact Sec13.card_slPi_three hK'
  have h9 : ¬ (q % 9 = 1 ∨ q % 9 = 8) := by
    intro h
    rw [← hpq] at h
    have hmn := Sec13.modNine_of_mod_nine hq h
    exact h243 (hcard ▸ (Sec13.modNine_iff_dvd hq).1 hmn)
  exact Sec12.Item128StepsProof.pow_three_eq_one_of_not_modNine hXq h9 hs

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
