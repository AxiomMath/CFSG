module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434Heis
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SporM5

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

open CFSG.Blueprint CFSG.Monster.Generated

namespace SporS1

open _root_.Timmesfeld.PcReg CFSG.Sporadic.Th
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular

theorem hasNonabelianFiveSubgroup_of_surjective {G H : Type} [Group G] [Group H] [Finite G]
    {f : G →* H} (hf : Function.Surjective f) (h : HasNonabelianFiveSubgroup H) :
    HasNonabelianFiveSubgroup G := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite H := Finite.of_surjective f hf
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 5 G))
  refine ⟨S, S.isPGroup', fun hS => ?_⟩
  obtain ⟨P, hP, hnc⟩ := h
  have hT : IsMulCommutative ((S.mapSurjective hf : Sylow 5 H) : Subgroup H) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_isMulCommutative _ _
  exact hnc (isMulCommutative_of_isPGroup hT hP)

end SporS1

open _root_.Timmesfeld.PcFive CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive CFSG.AGLEmbedding.Norton.MON5_7

theorem gmat_hasNonabelianFiveSubgroup :
    HasNonabelianFiveSubgroup Gmat := by
  let g : Fin 9 → Gmat := fun i => gw fiveGens[i.val]!
  have hg : ∀ r ∈ relSet 5 (pwF 9 pw) (cwF 9 cw), FreeGroup.lift g r = 1 := by
    rw [← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.fivePw_eq,
      ← CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveGmat.fiveCw_eq]
    exact fiveRels_holds
  obtain ⟨hp, hc⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveCensus.rel_of_relSet g hg
  have H := CFSG.KC.MonPcFive.pcHyp_of_rel hp hc
  have hexp := CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis.SporM5.rSub_pow_five H.rel
  refine ⟨Subgroup.closure (Set.range (CFSG.KC.MonPcFive.bG g)),
    fun x => ⟨1, Subtype.ext (by simpa using hexp x x.2)⟩, fun hS => ?_⟩
  have h21 : CFSG.KC.MonPcFive.bG g 2 * CFSG.KC.MonPcFive.bG g 1 =
      CFSG.KC.MonPcFive.bG g 1 * CFSG.KC.MonPcFive.bG g 2 := by
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val
      (mul_comm' (⟨_, Subgroup.subset_closure ⟨2, rfl⟩⟩ :
        Subgroup.closure (Set.range (CFSG.KC.MonPcFive.bG g)))
        ⟨_, Subgroup.subset_closure ⟨1, rfl⟩⟩)
  have e := H.rel.bcomm_eq 2 1
  have e1 : (CFSG.KC.MonPcFive.Mz 2 1).val = 1 := rfl
  rw [e1, pow_one, CFSG.Monster.B.Pinned.bcomm_eq_one_iff.2 h21] at e
  exact fiveGen_eight_ne_one e.symm

theorem m_hasNonabelianFiveSubgroup_of_finite [Finite NativeSporadic.M] :
    HasNonabelianFiveSubgroup NativeSporadic.M := by
  have hs : Function.Surjective (CFSG.YGroups.Y443.fM.comp
      CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.toMonoidHom) :=
    (CFSG.YGroups.Y443.y443_native_surjective_homomorphism.1 _
      CFSG.YGroups.Y443.fM_isFM).1.comp CFSG.Sporadic.Bridge.Y443.commutatorMulEquiv.surjective
  exact SporS1.hasNonabelianFiveSubgroup_of_surjective hs gmat_hasNonabelianFiveSubgroup

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
