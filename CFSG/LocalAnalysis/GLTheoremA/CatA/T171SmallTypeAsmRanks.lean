module
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.U33Proved

import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalFieldOThree
import CFSG.GH74.GLS.IVK.Proofs2.GHInvOut
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanIdentOffCharAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09I133Small
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutRank
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.GorensteinWalter

theorem card_mulAut_lie_A1_seven (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 7) :
    Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group) = 336 := by
  have hp7 : q.p = 7 ∧ q.exponent = 1 := by
    have hpow : q.p ^ q.exponent = 7 := by
      rw [← TauCeti.PrimePower.card_def]; exact hq
    exact (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 hpow
  obtain ⟨hp, hexp⟩ := hp7
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩
  have hm := CFSG.Models.lieModel_A (G := d.Group) 1 q hv (MulEquiv.refl _)
  have hclass : StatedClassicalModel d.Group .PSL 2 7 1 := by
    rcases hm with ⟨-, hclass | ⟨hn0, -⟩⟩
    · simpa [hp, hexp] using hclass
    · omega
  have hcardG : Nat.card d.Group = 168 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hclass
  obtain ⟨-, K, _, hfinK, hK, ⟨e⟩⟩ := hclass
  haveI : Finite K := hfinK
  haveI : Finite d.Group := Finite.of_equiv _ e.symm.toEquiv
  let e1 : d.Group ≃* PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hK7 : Nat.card K = 7 := by
    rw [hK]; norm_num
  have hcardPGL : Nat.card (PGL2 K) = 336 := by
    rw [CFSG.GorensteinWalter.pgl2_card_formula, hK7]; norm_num
  have hbij := CFSG.Quasithin.A312U3.pgl2InnerAutPSL2_bijective hK7
    ⟨7, 1, by norm_num, by decide, le_rfl, by rw [hK7]; norm_num⟩ (by rw [hK7]; norm_num)
  have hcardAutPSL : Nat.card (MulAut (PSL2 K)) = 336 := by
    let φ : PGL2 K ≃* MulAut (PSL2 K) := MulEquiv.ofBijective _ hbij
    rw [← Nat.card_congr φ.toEquiv]
    exact hcardPGL
  have hcardAut : Nat.card (MulAut d.Group) = 336 := by
    rw [Nat.card_congr (MulAut.congr e1).toEquiv]
    exact hcardAutPSL
  simpa [d] using hcardAut

theorem pRank_mulAut_lie_A1_seven (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    [Finite (MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group)] :
    CFSG.Open.pRank 3
      (⊤ : Subgroup (MulAut
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 q, hv⟩).Group)) ≤ 1 := by
  have hcard := card_mulAut_lie_A1_seven q hv hq
  refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 1 ?_
  rw [hcard]
  norm_num

theorem card_mulAut_lie_U33
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (hq : q.card = 3) :
    Nat.card (MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group) =
      12096 := by
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩
  have hX : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsUThreeThree d.Group :=
    ⟨d, ⟨q, hq, rfl⟩, ⟨MulEquiv.refl _⟩⟩
  have hmodel : CFSG.Blueprint.LieModel d.Group .PSU 3 3 1 :=
    CFSG.AGLEmbeddingD2.McLaughlin.lieModel_of_isUThreeThree hX
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hmodel
  exact CFSG.GH74.KGroups.U33.card_mulAut e

theorem pRank_mulAut_lie_U33
    (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid)
    (hq : q.card = 3)
    [Finite (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group]
    [Finite (MulAut (TauCeti.CFSGIndex.lie
      ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group)] :
    CFSG.Open.pRank 3
      (⊤ : Subgroup (MulAut
        (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group)) ≤ 2 := by
  have hcard := card_mulAut_lie_U33 q hv hq
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩
  have hX : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsUThreeThree d.Group :=
    ⟨d, ⟨q, hq, rfl⟩, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hsimple, hcardG, hcen⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.u33_simple_card_center hX
  haveI : Finite d.Group := Nat.finite_of_card_ne_zero (by rw [hcardG]; norm_num)
  obtain ⟨-, hrank⟩ := CFSG.AGLEmbeddingD2.McLaughlin.u33FactsExact_proved d.Group hX
  have hperf : commutator d.Group = ⊤ := by
    have hnab : ∃ a b : d.Group, a * b ≠ b * a := by
      by_contra h
      push Not at h
      haveI : IsMulCommutative d.Group := isMulCommutative_iff.2 (fun a b => h a b)
      have hprime := (CommGroup.is_simple_iff_prime_card (α := d.Group)).1 hsimple
      rw [hcardG] at hprime
      norm_num at hprime
    exact Group.isPerfect_def.1
      (CFSG.HardMathSupport.Malle.E27Lie.isPerfect_of_simple_nonabelian hsimple hnab)
  have hcardOut : Nat.card (Outer d.Group) ≤ 2 := by
    refine CFSG.GH74.GLS.IVK.GHInv.card_outer_le_of_card_mulAut_le hcen (c := 2) ?_
    rw [hcard, hcardG]
  have hrankOut : CFSG.Open.pRank 3 (⊤ : Subgroup (Outer d.Group)) ≤ 0 := by
    refine CFSG.AGLEmbedding.openPRank_top_le_of_not_dvd 0 ?_
    intro h3
    have h31 : 3 ^ (0 + 1) ∣ Nat.card (Outer d.Group) := h3
    norm_num at h31
    obtain ⟨k, hk⟩ := h31
    rw [hk] at hcardOut
    have hpos : 0 < k := by
      by_contra hk0
      have : Nat.card (Outer d.Group) = 0 := by rw [hk]; omega
      exact Nat.card_pos.ne' this
    omega
  have hbound := CFSG.LocalAnalysis.RankFourTheoremC.pRank_mulAut_le_add_pRank_outer
    (K := d.Group) (p := 3) Nat.prime_three hcen
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup d.Group) = 2 := hrank
  rw [h2] at hbound
  omega

end CFSG.LocalAnalysis.GLTheoremA.T171S
