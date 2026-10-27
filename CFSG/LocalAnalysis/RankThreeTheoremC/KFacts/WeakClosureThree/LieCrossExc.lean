module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieDispatch
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankAny
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutTwE6
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsLocal
public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.SectionRank
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.RankThree.PartOne.StrongP (HasNoncommPair)

section Exceptional


theorem four_le_pRank_three_of_untwistedModel_any {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {q : ℕ}
    (h : UntwistedChevalleyModel S τ q) : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact CFSG.LieType.Chevalley.four_le_pRank_three_adjointQuotient_any hτ

theorem dichLieCross_F4 : DichLieCrossAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank
    (four_le_pRank_three_of_untwistedModel_any (Or.inl rfl) hm)

theorem dichLieCross_E6 : DichLieCrossAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank
    (four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inl rfl)) hm)

theorem dichLieCross_E7 : DichLieCrossAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank
    (four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inr (Or.inl rfl))) hm)

theorem dichLieCross_E8 : DichLieCrossAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  obtain ⟨-, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact dichThreeLieAt_of_four_le_pRank
    (four_le_pRank_three_of_untwistedModel_any (Or.inr (Or.inr (Or.inr rfl))) hm)

end Exceptional

section TwistedE6


theorem dichLieCross_twistedE6 : DichLieCrossAt .twistedE6 := by
  intro K _ _ _ _ n ℓ f _ hmodel _ _
  exact dichThreeLieAt_of_four_le_pRank
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.twistedE6ThreeRankFour_holds
      K ℓ f (hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])))

end TwistedE6

theorem dichLieCross_twistedG2 : DichLieCrossAt .twistedG2 := by
  intro K _ _ _ _ n ℓ f hadm _ hℓ _
  obtain ⟨_, _, _, h3, _⟩ := hadm
  exact absurd h3 hℓ

section Suzuki


private theorem not_three_dvd_suzuki {N f : ℕ} (hf : Odd f)
    (hN : N * lieOrderDivisor .twistedB2 0 (2 ^ f) = lieOrderNumerator .twistedB2 0 (2 ^ f)) :
    ¬ 3 ∣ N := by
  intro h
  simp only [lieOrderDivisor, lieOrderNumerator, mul_one] at hN
  obtain ⟨a, rfl⟩ := hf
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  set q := 2 ^ (2 * a + 1) with hqdef
  have h1 : (q - 1) % 3 = 1 := by omega
  have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have h3 : (q ^ 2 + 1) % 3 = 2 := by rw [Nat.add_mod, h2]
  have h4 : (q ^ 2 * (q ^ 2 + 1) * (q - 1)) % 3 = 2 := by
    rw [Nat.mul_mod, Nat.mul_mod (q ^ 2), h2, h3, h1]
  have : 3 ∣ q ^ 2 * (q ^ 2 + 1) * (q - 1) := hN ▸ h.mul_right 1 |>.trans (by rw [mul_one])
  omega

theorem dichLieCross_twistedB2 : DichLieCrossAt .twistedB2 := by
  intro K _ _ _ _ n ℓ f hadm hmodel hℓ h3
  have hN := (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput K .twistedB2 n ℓ f
    hadm hmodel).2.1
  obtain ⟨_, _, hn0, hℓ2, hfodd, -⟩ := hadm
  subst hn0 hℓ2
  exact absurd h3 (not_three_dvd_suzuki hfodd hN)

end Suzuki

section Tits


theorem dichLieCross_Tits : DichLieCrossAt .Tits := by
  intro K _ _ _ _ n ℓ f hadm hmodel _ _
  obtain ⟨-, hrt⟩ := hmodel.reeTitsModel (by simp [reeTitsTags])
  obtain ⟨-, -, -, hℓ2, -⟩ := hadm
  subst hℓ2
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv K 2 f hrt
  have hcard : Nat.card K = 17971200 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (ZMod 2) CFSG.LieType.Ree.ReeTag.F4.prime := ZMod.charP 2
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    Tits_sylow3_cubic_witness (K := ZMod 2) (by simp)
  have hpair := CFSG.RankThree.PartOne.CTP.hasNoncommPair_of_cubic Nat.prime_three hx hy hz hc
  refine dichThreeLieAt_of_pair_of_le ?_
    (hpair.map ((CFSG.Sporadic.Schreier.Tits.titsDerivedIso (K := ZMod 2)).trans
      e.symm).toMonoidHom (MulEquiv.injective _))
  have := factorization_lt_of_not_dvd (K := K) (k := 4) (by rw [hcard]; norm_num)
  omega

end Tits

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureThree
