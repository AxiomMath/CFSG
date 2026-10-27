module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiBenderSL2
import CFSG.GroupTheory.SylowIntersectionControl.AlternatingNotBender
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.Quasithin.Background.KnownMultTypes
public import CFSG.Models.BenderSuzuki

public section

namespace CFSG.GroupTheory

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

private theorem not_fusionIsBenderGroup_quotient_of_mulEquiv_alt {K : Type} [Group K] [Finite K]
    {n : ℕ} (hn : 6 ≤ n) (e : K ≃* alternatingGroup (Fin n)) :
    ¬ CFSG.Open.fusionIsBenderGroup (K ⧸ Subgroup.center K) := by
  have hcenter : Subgroup.center K = ⊥ := by
    have hmap : (Subgroup.center K).map (e : K →* alternatingGroup (Fin n)) = ⊥ := by
      rw [Subgroup.map_center_eq e,
        alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))]
    exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center K) e.injective).mp hmap
  have eQ : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans e
  exact not_fusionIsBenderGroup_of_mulEquiv_alternatingGroup hn eQ

private theorem isGomiU3_of_mulEquiv_psu3 {Y : Type} [Group Y] {f : ℕ} (hf : 2 ≤ f)
    (e : Y ≃* CFSG.Open.PSU3 2 f) : IsGomiU3 Y := by
  have hf1 : 1 ≤ f := by omega
  have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
    CFSG.Models.benderPSU3Model_eq_psu3 f
  obtain ⟨eSU⟩ := CFSG.CGT.PushingUp.benderBridge_psu (n := f) hf
    (e.trans (MulEquiv.subgroupCongr hmodel.symm))
  let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, hf1⟩
  have hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    dsimp only
    have hcard : q.card = 2 ^ f := by
      rw [TauCeti.PrimePower.card_def]
    have hpow : 3 ≤ 2 ^ f := by
      calc 3 ≤ 4 := by norm_num
        _ = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    rw [hcard]
    refine ⟨⟨by norm_num, fun _ => hpow⟩, by simp⟩
  have : Fact (Nat.Prime q.p) := ⟨Nat.prime_two⟩
  exact ⟨⟨.twistedA 2 q, hv⟩, ⟨q, rfl, rfl⟩,
    ⟨eSU.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv).symm⟩⟩

private theorem isGomiSz_of_mulEquiv_sz {Y : Type} [Group Y] {a : ℕ} (ha : 1 ≤ a)
    (e : Y ≃* CFSG.Open.Sz a) : IsGomiSz Y := by
  obtain ⟨m, hm, ⟨eL⟩⟩ := CFSG.CGT.PushingUp.benderBridge_suzuki ha
    (e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a).symm))
  exact ⟨⟨.suzuki m, hm⟩, ⟨m, rfl⟩, ⟨eL⟩⟩

private theorem isSLn_of_mulEquiv_psl_two_even {K : Type} [Group K] [Finite K]
    (hperf : Group.IsPerfect K) (hO : CFSG.pCore 2 K = ⊥) {f : ℕ} (hf : 2 ≤ f)
    (e : K ⧸ Subgroup.center K ≃* PSL(2, GaloisField 2 f)) :
    ∃ m : ℕ, 2 ≤ m ∧ IsSLn K 2 m := by
  have hf0 : f ≠ 0 := by omega
  have hFcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  let F := GaloisField 2 f
  have : Group.IsPerfect K := hperf
  have hZ2 : IsPGroup 2 (Subgroup.center K) :=
    CFSG.Quasithin.isPGroup_two_of_mulEquiv_stated_psl_two_even (Subgroup.center K) le_rfl hf
      hFcard (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F))
  have hZle : Subgroup.center K ≤ CFSG.pCore 2 K := le_sSup ⟨inferInstance, hZ2⟩
  have hZ : Subgroup.center K = ⊥ := le_bot_iff.mp (hO ▸ hZle)
  have hZSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro A hA
    obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := CharTwo.sq_injective (hr2.trans (one_pow 2).symm)
    exact Subtype.ext (by rw [← hA, hr1]; simp)
  have eSL : PSL(2, F) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZSL.symm)).symm
  have eQ : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have eKSL : K ≃* CFSG.Open.StatedSL 2 F :=
    (eQ.trans e).trans (eSL.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
  exact ⟨f, hf, F, inferInstance, inferInstance, hFcard, ⟨eKSL⟩⟩

theorem gomiBenderSL2_holds : GomiBenderSL2 := by
  intro K _ _ hK hB
  rcases hK with ⟨hq, hU, hS⟩ | ⟨n, hn7, ⟨eAlt⟩⟩
  · rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact isSLn_of_mulEquiv_psl_two_even hq.1.1 hq.2.1 hf e
    · exact absurd (isGomiU3_of_mulEquiv_psu3 hf e) hU
    · exact absurd (isGomiSz_of_mulEquiv_sz ha e) hS
  · exact absurd hB (not_fusionIsBenderGroup_quotient_of_mulEquiv_alt (by omega) eAlt)

end CFSG.GroupTheory
