module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporPc
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporM7
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import Certificates.Certificate425001

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open _root_.Timmesfeld.PcFive _root_.Timmesfeld.PcReg _root_.Timmesfeld.PcFus CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus

theorem rankThreeWitness_five_of
    {G : Type} [Group G] [Finite G]
    {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hpow : ∀ i : Fin 9, g i ^ 5 = prodAsc g pw[i.val]!)
    (hcomm : ∀ i j : Fin 9, i < j → g i * g j * (g i)⁻¹ = prodAsc g cw[i.val * 9 + j.val]!)
    (hz : g 8 ≠ 1)
    (hN : ∀ j < auts.size, ∃ c : G, ∀ (i : ℕ) (hi : i < 9),
      c * g ⟨i, hi⟩ * c⁻¹ = prodAsc g (digitsOf 5 9 (auts[j]!)[i]!)) :
    ∀ s : G, orderOf s = 5 → RankThreeWitness 5 s := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hE3 := Certificates.certificate425001 g hpow hcomm hz
  refine fiveCover_of_invariant hcard hm g hpow hcomm hz hN
    (fun x c h => h.conj_eq c rfl) (fun x k hx hk h => h.pow Nat.prime_five hx hk) ?_
  intro k hk
  obtain ⟨A, hA, hcA, hmA⟩ := hE3 k hk
  exact Or.inr (Or.inr ⟨A, hA, hcA, hmA⟩)

theorem rankThreeWitness_five_of_rel
    {G : Type} [Group G]
    [Finite G] {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) (g : Fin 9 → G)
    (hg : ∀ r ∈ relSet 5 (pwF 9 pw) (cwF 9 cw), FreeGroup.lift g r = 1) (hz : g 8 ≠ 1)
    (V : Array (Array (Array ℕ)))
    (hV : ∀ j < auts.size, ∀ i < 9, digitsOf 5 9 (auts[j]!)[i]! = (V[j]!)[i]!)
    (cN : ℕ → G)
    (hN : ∀ j < auts.size, ∀ (i : ℕ) (hi : i < 9),
      cN j * g ⟨i, hi⟩ * (cN j)⁻¹ = FreeGroup.lift g (wordF 9 (V[j]!)[i]!)) :
    ∀ s : G, orderOf s = 5 → RankThreeWitness 5 s := by
  obtain ⟨hp, hc⟩ := rel_of_relSet g hg
  refine rankThreeWitness_five_of hcard hm g hp hc hz (fun j hj => ⟨cN j, fun i hi => ?_⟩)
  rw [hN j hj i hi, lift_wordF_eq, hV j hj i hi]

section CertificateInstances

open CFSG.Monster CFSG.Monster.Generated CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat CFSG.AGLEmbedding.Norton.MON5_7

theorem rankThreeWitness_five_Gmat (s : Gmat) (hs : orderOf s = 5) : RankThreeWitness 5 s := by
  have hcard0 : Nat.card Gmat = monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have : Finite Gmat := Nat.finite_of_card_ne_zero (by rw [hcard0]; norm_num [monsterOrder])
  have hcard : Nat.card Gmat = 5 ^ 9 * (monsterOrder / 5 ^ 9) := by
    rw [hcard0]; norm_num [monsterOrder]
  have hm : ¬ 5 ∣ monsterOrder / 5 ^ 9 := by norm_num [monsterOrder]
  refine rankThreeWitness_five_of_rel hcard hm (fun i : Fin 9 => gw fiveGens[i.val]!) ?_ ?_
    fiveNImg fiveNImg_eq (fun j => gw fiveNW[j]!) ?_ s hs
  · rw [← fivePw_eq, ← fiveCw_eq]
    exact fiveRels_holds
  · exact fiveGen_eight_ne_one
  · intro j hj i hi
    exact fiveNorm_holds j (by have : _root_.Timmesfeld.PcFive.auts.size = 3 := rfl; omega) i hi

end CertificateInstances

section CertificateInstancesNative

theorem sporadicClassWitnessAt_M_five : SporadicClassWitnessAt .M 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine sporadicClassWitnessAt_of_native
    (sporadicClassWitnessNative_M_of_Gmat rankThreeWitness_five_Gmat ?_)
  intro T _ _ ⟨e⟩
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  haveI : IsSimpleGroup T := e.isSimpleGroup
  exact CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
