module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TT1010
public import CFSG.HardMathSupport.Timmesfeld.LieRank.G2
public import CFSG.HardMathSupport.Timmesfeld.LieRank.Exc3Models
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Main
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeProof

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.LieRank CFSG.HardMathSupport.Timmesfeld.Tables.T1b
  CFSG.Blueprint.Chevalley

section Certs



theorem tables112Types_TG23_holds : ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    CFSG.Open.IsKGroup K → IsHatGTwoThree K →
      CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut K)) ≠ CFSG.Open.pRank 3 (⊤ : Subgroup K) + 1 := by
  intro K _ _ hq _ hG
  obtain ⟨-, hc3, q, d, hq3, hd, ⟨e⟩⟩ := hG
  have hqcard : q.p ^ q.exponent = 3 := by
    have := hq3
    rwa [TauCeti.PrimePower.card_def] at this
  obtain ⟨hp3, hf1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_three).1 hqcard
  have hM0 : CFSG.Models.LieModel (TauCeti.CFSGIndex.lie d).Group .G2 0 q.p q.exponent :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_lie (t := .G2)
      ⟨q.prime_p, q.exponent_pos, rfl, by omega⟩ d (by rw [hd]; exact ⟨rfl, rfl⟩)
  rw [hp3, hf1] at hM0
  have hM1 : CFSG.Models.LieModel (K ⧸ Subgroup.center K) .G2 0 3 1 :=
    models_lieModel_of_mulEquiv e.symm hM0
  have hB := blueprintLieModel_of_models hM1
  obtain ⟨eA⟩ := nonempty_mulEquiv_adjointGroup_G2_of_lieModel hB
  have hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ Subgroup.center K) .G2 3 1 := by
    rcases hB with ⟨ht, -⟩ | ⟨-, -, h⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact absurd ht (by decide)
    · exact h
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have hout := CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree.card_outer_G2_three (K ⧸ Subgroup.center K) hmodel
  have hcop : Nat.Coprime 3 (Nat.card (Outer (K ⧸ Subgroup.center K))) := by
    rw [hout]; norm_num
  have h1 := pRank_mulAut_le_of_quasisimple (p := 3) (by norm_num) hq
  have h2 := pRank_three_mulAut_le_of_coprime_outer
    (center_quotient_eq_bot_of_quasisimple hq) hcop
  have h3 := pRank_quotient_le_of_cover_G2 eA (by rw [hc3])
  omega

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator
