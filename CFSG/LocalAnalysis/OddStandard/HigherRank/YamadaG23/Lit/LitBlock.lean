module

public import CFSG.CharacterTheory.Burnside
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private instance instDecidableMemBlockStab : DecidablePred (· ∈ blockStab) := by
  intro σ
  change Decidable (∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔
    (σ i).val / 3 = (σ j).val / 3)
  infer_instance

private instance instFintypeBlockStab : Fintype ↥blockStab :=
  Fintype.ofFinset (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => σ ∈ blockStab))
    (by intro σ; simp)

theorem lit_card_blockStab : Nat.card ↥blockStab = 72 := by
  haveI : Fintype ↥blockStab := instFintypeBlockStab
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem lit_isSolvable_blockStab : Group.IsSolvable ↥blockStab := by
  haveI : Fintype ↥blockStab := instFintypeBlockStab
  refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    (p := 2) (q := 3) (a := 3) (b := 2) Nat.prime_two Nat.prime_three (by norm_num) ?_
  rw [← Nat.card_eq_fintype_card, lit_card_blockStab]
  norm_num

end CFSG.OddStandard.HigherRank.YamadaG23
