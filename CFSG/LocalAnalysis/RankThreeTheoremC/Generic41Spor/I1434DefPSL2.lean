module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434DefClassical

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag StatedSL StatedProj
  StatedScalars)
open CFSG.EvenSmallLie.CatalogOrders (lieOrd lieExp lieMin card_eq_lieOrd_of_classical
  pow_lieExp_dvd)


theorem psl2_five_false {K : Type} [Group K] [Finite K] {f : ℕ}
    (hM : StatedClassicalModel K .PSL 2 5 f) {Q : Sylow 5 K} {x : K} {J₁ J₂ : Subgroup K}
    (hD : Data K Q x J₁ J₂) : False := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard := card_eq_lieOrd_of_classical hM
  obtain ⟨hadm, F, hFfield, hFfin, hF, ⟨e⟩⟩ := hM
  obtain ⟨-, hf1, -⟩ := hadm
  haveI := hFfin
  haveI : CharP F 5 := charP_five_of_card_eq_five_pow hF
  have hK1 : FiveExpLe K 1 :=
    FiveExpLe.of_mulEquiv e.symm
      (fiveExpLe_statedProj (StatedSL 2 F) (k := 1) (by simp))
  have hv := hD.le_of_fiveExpLe hK1
  have hdvd : 5 ^ f ∣ Nat.card K := by
    rw [hcard]
    have := pow_lieExp_dvd (t := .PSL) (n := 2) (by simp [lieMin]) (5 ^ f)
    simpa [lieExp] using this
  have hN : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hfv : f ≤ (Nat.card K).factorization 5 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_five hN).1 hdvd
  have hf3 : f ≤ 3 := by omega
  have h3600 : 3600 ∣ Nat.card K := by
    have := three_thousand_six_hundred_dvd_card hD.five
      (R := (⊤ : Subgroup K)) (fun P _ _ => le_top)
    rwa [Subgroup.card_top] at this
  rw [hcard] at h3600
  interval_cases f
  · revert h3600; decide +kernel
  · revert h3600; decide +kernel
  · revert h3600; decide +kernel

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
