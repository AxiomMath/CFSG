module

public import CFSG.Yardstones.Md0ec50421ce4.Definitions
import CFSG.LieType.ChevTwo.Main
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123c
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicRadical
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)


section Certs

theorem t2021Fix_core {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (hC : IsChevSimple 2 S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Subgroup S} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hrad : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (T : Set S)) = T)
    {g : MulAut S} (hgp : g ^ p = 1) (hgT : ∀ t ∈ T, g t = t) : g = 1 := by
  have hC2 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.isChevTwo_of_isChevSimple_two hC
  have hOv := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPRad.overgroups_of_isChevSimple_two hC
  obtain ⟨-, -, -, hNtop, -, S₀, hS₀⟩ := CFSG.GH74.GLS.Stage2.OddAut.canonical_parabolic_tits
    (CFSG.LieType.ChevTwo.holdsTits_two_of_isChevTwo hs hna hC2) hT1 hT2
  rw [CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.radInf_eq_of_pCoreOf hrad] at hNtop hS₀
  have hS₀syl := CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S₀
  have hLI : ∀ x : S, (∀ t ∈ T, x * t = t * x) → x ∈ T := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (T : Set S) :=
      Subgroup.mem_centralizer_iff.mpr fun t ht => (hx t ht).symm
    have hchar := hOv _ _ hS₀syl hS₀ hNtop
    unfold CFSG.QuasithinUnique.CharTwo at hchar
    rw [hrad] at hchar
    exact hchar ⟨Subgroup.centralizer_le_normalizer _ hxC, hxC⟩
  have hfix := CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.fixes_normalizer_of_fixes T hT2
    hLI g ((Nat.coprime_primes hp Nat.prime_two).mpr hp2) hgp hgT
  by_contra hg1
  have hRp : IsPGroup p (Subgroup.zpowers g) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hgp)
  have hcore := CFSG.LieType.ChevTwo.chev2CoreCent_of_leaves S hs hna hC2 p hp hp2 _ hRp
  have hNC : Subgroup.normalizer (T : Set S) ≤
      CFSG.LieType.ChevTwo.autCentralizer (Subgroup.zpowers g) := by
    intro y hy α hα
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (MulAut S) y :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (hfix y hy))
    exact MulAction.mem_stabilizer_iff.mp (hle hα)
  have hCtop : CFSG.LieType.ChevTwo.autCentralizer (Subgroup.zpowers g) ≠ ⊤ := by
    intro htop
    refine hg1 (MulEquiv.ext fun x => ?_)
    have hx : x ∈ CFSG.LieType.ChevTwo.autCentralizer (Subgroup.zpowers g) := by
      rw [htop]
      exact Subgroup.mem_top x
    exact hx g (Subgroup.mem_zpowers g)
  have hchar := hOv _ _ hS₀syl (hS₀.trans hNC) hCtop
  unfold CFSG.QuasithinUnique.CharTwo at hchar
  rw [hcore] at hchar
  have hCbot : CFSG.LieType.ChevTwo.autCentralizer (Subgroup.zpowers g) ≤ ⊥ := fun c hc =>
    hchar ⟨hc, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Subgroup.mem_bot.mp hh, one_mul, mul_one]⟩
  exact hT1 (le_bot_iff.mp ((Subgroup.le_normalizer.trans hNC).trans hCbot))

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T2021
