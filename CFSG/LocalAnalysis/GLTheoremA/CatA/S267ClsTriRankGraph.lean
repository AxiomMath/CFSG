module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsTriRankFix
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Basic
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4OddMinus
import CFSG.RankThree.PartTwo.Sec15.Item1513Res2ProofPGL
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.ThreeRank
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)


variable {K : Type} [Field K] [Finite K]

section Classes


theorem fixRankTwo_d4Graph_one (h3 : ¬ 3 ∣ Nat.card K) (hK3 : 3 ≤ Nat.card K) :
    FixRankTwo (d4Graph K 1) :=
  FixRankTwo.of_mulEquiv (CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroupEquivG2
    K hK3) fun F hF =>
      CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.card_le_nine_of_isElemAbelian_three K h3
        F hF

theorem fixRankTwo_d4Graph_two (h3 : ¬ 3 ∣ Nat.card K) (hK3 : 3 ≤ Nat.card K) :
    FixRankTwo (d4Graph K 2) := by
  intro E hE hEa
  rw [CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.fixSubgroup_d4Graph_two] at hE
  exact fixRankTwo_d4Graph_one h3 hK3 E hE hEa

end Classes

omit [Finite K] in
private theorem three_dvd_card_sub_one_of_piField {π : Bool} {p f : ℕ} {K' : Type} [Field K']
    (hK : CFSG.RankThree.PartTwo.Sec4.PiField π p f K')
    (hq : CFSG.RankThree.PartTwo.Sec4.ModThree π (p ^ f)) : 3 ∣ Nat.card K' - 1 := by
  rw [hK.card]
  cases π with
  | true =>
    change (p ^ f) % 3 = 1 at hq
    change 3 ∣ p ^ f - 1
    omega
  | false =>
    change (p ^ f) % 3 = 2 at hq
    change 3 ∣ (p ^ f) ^ 2 - 1
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by
      rw [Nat.pow_mod, hq]
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by have := hK.prime.pos; positivity)
    omega

omit [Finite K] in
private theorem three_ne_zero_of_piField {π : Bool} {p f : ℕ} {K' : Type} [Field K']
    (hK : CFSG.RankThree.PartTwo.Sec4.PiField π p f K')
    (hq : CFSG.RankThree.PartTwo.Sec4.ModThree π (p ^ f)) : (3 : K') ≠ 0 := by
  haveI : Fact p.Prime := ⟨hK.prime⟩
  haveI : Finite K' := hK.finite
  haveI : Fintype K' := Fintype.ofFinite K'
  have hcard : Fintype.card K' = p ^ (cond π f (2 * f)) := by
    rw [← Nat.card_eq_fintype_card, hK.card]
    cases π
    · change (p ^ f) ^ 2 = p ^ (2 * f)
      rw [← pow_mul, mul_comm]
    · rfl
  haveI : CharP K' p := charP_of_card_eq_prime_pow hcard
  intro h
  have hp3 : p ∣ 3 := (CharP.cast_eq_zero_iff K' p 3).mp (by exact_mod_cast h)
  have hp : p = 3 := (Nat.prime_dvd_prime_iff_eq hK.prime Nat.prime_three).mp hp3
  have h0 : (p ^ f) % 3 = 0 := by
    rw [hp]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 3 (by have := hK.one_le; omega))
  cases π
  · change (p ^ f) % 3 = 2 at hq
    omega
  · change (p ^ f) % 3 = 1 at hq
    omega

section A2


theorem fixRankTwo_gammaP (hK2 : ringChar K ≠ 2) (hK3 : ringChar K ≠ 3) (hK5 : 5 ≤ Nat.card K)
    {B : SL2 K} (hB3 : B ^ 3 = 1) (hB1 : B ≠ 1) : FixRankTwo (gammaP K B) := by
  obtain ⟨π, p, f, K', _, hPi, hpq, hq, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighD4Odd.d4GraphA2FixIsoOdd_holds K hK2
      hK3 hK5 B hB3 hB1
  haveI : Finite K' := hPi.finite
  rw [← hpq] at hq
  have h3 : (3 : K') ≠ 0 := three_ne_zero_of_piField hPi hq
  obtain ⟨τ, hτ3, hτ1⟩ : ∃ τ : K', τ ^ 3 = 1 ∧ τ ≠ 1 := by
    have hdvd := three_dvd_card_sub_one_of_piField hPi hq
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K'ˣ) 3 (by rwa [Nat.card_units])
    refine ⟨(x : K'), ?_, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
    · intro h
      have hx1 : x = 1 := Units.ext h
      rw [hx1, orderOf_one] at hx
      norm_num at hx
  have hfix : fixSubgroup (gammaP K B) = CFSG.RankThree.PartOne.CTP.fixedSubgroup (gammaP K B) :=
    Subgroup.ext fun _ => Iff.rfl
  refine FixRankTwo.of_mulEquiv ((MulEquiv.subgroupCongr hfix).trans e) fun F hF => ?_
  rw [← Subgroup.card_map_of_injective
    (f := (CFSG.PGLModel.projImage (CFSG.RankThree.PartTwo.Sec4.glPi π 3 (Nat.card K) K')).subtype)
    Subtype.val_injective]
  exact CFSG.RankThree.PartTwo.Sec15.Proof1513Res2.card_le_nine_pgl h3 hτ3 hτ1 (hF.map _)

theorem fixRankTwo_d4_graph (hp5 : 5 ≤ ringChar K) (hK5 : 5 ≤ Nat.card K)
    (h3 : ¬ 3 ∣ Nat.card K) {α : MulAut (adjointGroup Tag.D4 K)} (hα3 : α ^ 3 = 1)
    (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) (hε3 : ε < 3) (hε0 : ε ≠ 0)
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) :
    FixRankTwo α := by
  have hK2 : ringChar K ≠ 2 := by omega
  have hK3 : ringChar K ≠ 3 := by omega
  have hT : CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1 :=
    ⟨g, a, 1, ε, hε3, one_pow 3, ⟨hε0, rfl⟩, hα⟩
  rcases ClassOdd.d4GraphClassOdd_of (ClassOdd.graphShintaniNF_of ClassOdd.threeD4FixedNF_holds)
      ClassOdd.g2ThreeClass_holds K hp5 α hα3 hT with ⟨ψ, hψ⟩ | ⟨ψ, B, hB3, hB1, hψ⟩
  · refine FixRankTwo.of_conj ψ ?_
    rcases hψ with h | h
    · rw [h]
      exact fixRankTwo_d4Graph_one h3 (by omega)
    · rw [h]
      exact fixRankTwo_d4Graph_two h3 (by omega)
  · refine FixRankTwo.of_conj ψ ?_
    rcases hψ with h | h
    · rw [h]
      exact fixRankTwo_gammaP hK2 hK3 hK5 hB3 hB1
    · rw [h]
      refine FixRankTwo.of_inv ?_
      rw [inv_inv]
      exact fixRankTwo_gammaP hK2 hK3 hK5 hB3 hB1

end A2

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
