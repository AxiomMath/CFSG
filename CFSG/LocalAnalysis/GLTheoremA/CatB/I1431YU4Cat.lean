module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

abbrev K64 : Type := GaloisField 2 6

theorem K64_card : Nat.card K64 = 64 := by
  rw [GaloisField.card 2 6 (by norm_num)]
  norm_num

noncomputable def statedProjSU4Eight :
    StatedProj (StatedSU 4 8 K64) ≃* StatedSU 4 8 K64 := by
  have h := (CFSG.LinearGroups.unitary_scalar_kernel (K := K64) (p := 2) (f := 3) Nat.prime_two
    (by rw [K64_card]; norm_num) (n := 4) (by norm_num)).2.2
  have h' : Nat.card ((StatedScalars (Fin 4) K64).subgroupOf (StatedSU 4 (2 ^ 3) K64)) = 1 := by
    rw [h]
    norm_num
  have hbot : (StatedScalars (Fin 4) K64).subgroupOf (StatedSU 4 (2 ^ 3) K64) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [h']
  exact (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot

theorem u4_eight_equiv_statedSU {G : Type} [Group G] (hG : catalogIs G (S8.isU4of 8)) :
    Nonempty (G ≃* StatedSU 4 8 K64) := by
  obtain ⟨j, hj, ⟨eU⟩⟩ := hG
  cases j with
  | lie d =>
    obtain ⟨d', hv⟩ := d
    cases d' with
    | twistedA r q =>
      have hr : r = 3 := by
        rcases r with _ | _ | _ | _ | r
        · simp [S8.isU4of, onLie] at hj
        · simp [S8.isU4of, onLie] at hj
        · simp [S8.isU4of, onLie] at hj
        · rfl
        · simp [S8.isU4of, onLie] at hj
      subst hr
      have hq8 : q.card = 8 := by
        have h' : (S8.isU4of 8 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 3 q, hv⟩)) := hj
        simpa [S8.isU4of, onLie] using h'
      obtain ⟨p, e, hpp, he⟩ := q
      have hcard : p ^ e = 2 ^ 3 := by
        rw [← show TauCeti.PrimePower.card ⟨p, e, hpp, he⟩ = p ^ e from TauCeti.PrimePower.card_def _]
        simpa using hq8
      obtain ⟨hp2, he3⟩ := Nat.Prime.pow_inj' hpp Nat.prime_two he.ne' (by norm_num) hcard
      subst hp2
      subst he3
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨e1⟩ : Nonempty _ := ⟨CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 3
        ⟨2, 3, hpp, he⟩ hv⟩
      have e2 := CFSG.PGLModel.projSUEquivStatedProj (3 + 1) 2 3
      exact ⟨eU.trans (e1.trans (e2.trans statedProjSU4Eight))⟩
    | _ => exact hj.elim
  | _ => exact hj.elim

end CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YU4

end
