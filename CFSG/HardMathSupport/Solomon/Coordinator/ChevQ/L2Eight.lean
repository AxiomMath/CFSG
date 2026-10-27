module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsL2Eight
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem isLTwoEight_of_index {S : Type} [Group S] (d : TauCeti.ValidLieTypeIndex)
    (q : TauCeti.PrimePower) (hd : d.1 = .A 1 q) (hq : IsTwoPow q 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) : IsLTwoEight S := by
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  have hm := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA 1 q hv
  rcases hm.2 with hcm | ⟨hn, -⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨f⟩⟩ := hcm
    have hc8 : Nat.card F = 8 := by
      rw [hcard, hq.1, hq.2]
      norm_num
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 3)
      (by rw [← Nat.card_eq_fintype_card, hc8]; norm_num)
    have hZ := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F)
    let g : StatedProj (StatedSL 2 F) ≃* StatedSL 2 F :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨F, hF, hFin, hc8, ⟨(e.trans f).trans g⟩⟩
  · omega

theorem isStronglyBalanced_of_l2Eight {X : Type} [Group X] [Finite X]
    {K B : Subgroup X} (hH : I271Hyp 3 K B) (hNorm : I271Norm 3 K B)
    (hQ : IsLieQuot ↥K IsL2EightIndex) : IsStronglyBalancedIn 3 B K := by
  obtain ⟨d, hd, ⟨e⟩⟩ := hQ
  obtain ⟨q, hdq, hq3⟩ := hd.exists
  have hq : CFSG.Open.IsQuasisimple ↥K := i116e_isQuasisimple hH.core hH.comp
  have hS8 : IsLTwoEight (↥K ⧸ Subgroup.center ↥K) := isLTwoEight_of_index d q hdq hq3 e
  exact isStronglyBalancedIn_of_autBalanced hH.scp.2.1 hq.1 (MulEquiv.refl _)
    (by have := hNorm.2; simpa using this)
    (fun A hA hn T hT hAT => autLTwoEightBalance_holds _ hS8 A hA hn T hT hAT)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
