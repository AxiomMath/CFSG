module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Nine
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

open CFSG.Open CFSG.Fischer CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem isSimple_S6 : IsSimpleGroup S6 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 hF4card 6
    (by norm_num) (by norm_num)

theorem downLe_S6_of (hk : kLevel 3 S6 ≤ 2) : DownLe 3 2 S6 := by
  haveI := isSimple_S6
  intro β hβ I hI
  obtain ⟨B, hB, ⟨c, hBc⟩, hβB⟩ := exists_unitary_of_pow_three β hβ
  by_cases hsc : ∃ c : F4ˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 6) c
  ·
    obtain ⟨c₀, hc₀⟩ := hsc
    have hβ1 : β = 1 := by
      ext x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      rw [MulAut.one_apply]
      refine hβB u u ?_
      rw [hc₀, ← (commute_scalar c₀ (u : GL (Fin 6) F4)).eq, mul_inv_cancel_right]
    have hfix : fixSubgroup β = ⊤ := by
      ext x
      simp [mem_fixSubgroup, hβ1]
    rw [hfix] at hI
    rcases CFSG.Open.IsSubnormal.eq_bot_or_top hI.2.1 with h | h
    · exact absurd h (glaPComponent_ne_bot' hI)
    · subst h
      haveI : IsSimpleGroup ↥(⊤ : Subgroup S6) := Subgroup.topEquiv.isSimpleGroup
      obtain ⟨e⟩ := nonempty_pSimple_equiv_of_simple hI
      rw [kLevel_congr 3 e, kLevel_congr 3 Subgroup.topEquiv]
      exact hk
  · obtain ⟨J, hJ, ⟨e⟩⟩ := exists_component_transfer β ⟨B, hB⟩ hβB hI
    rw [kLevel_congr 3 e]
    by_cases h3 : (B : GL (Fin 6) F4) ^ 3 = 1
    · exact level_of_cube_one ⟨B, hB⟩ (Subtype.ext h3) hsc hJ
    · have hc1 : c ≠ 1 := fun h => h3 (by rw [hBc, h, map_one])
      exact level_of_nine ⟨B, hB⟩ hc1 hBc hJ

theorem bridge_u6two_stated {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) (hq : q.card = 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) : Nonempty (S ≃* S6) := by
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 5 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, _, _, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF4card]
  exact ⟨e'.trans (CFSG.Open.StatedSUFieldChange.statedProjSUEquiv
    (FiniteField.ringEquivOfCardEq hc) 6 (2 ^ 1))⟩

end CFSG.LocalAnalysis.GLTheoremA.LevelLieU6

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Yardstones.Md0ec50421ce4

theorem kdLieRowU6Two_holds : KDLieRowU6Two := by
  intro q hv hq
  obtain ⟨e⟩ := LevelLieU6.bridge_u6two_stated hv hq (MulEquiv.refl _)
  have hk2 : catalogIs (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 5 q, hv⟩).Group
      (k2 3) :=
    ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 5 q, hv⟩,
      (show (3 : ℕ) = 3 ∧ q.card = 2 from ⟨rfl, hq⟩), ⟨MulEquiv.refl _⟩⟩
  have hk : kLevel 3 LevelLieU6.S6 ≤ 2 := by
    rw [← kLevel_congr 3 e]
    exact LevelLieU.kLevel_le_two_of_k2 hk2
  exact downLe_of_mulEquiv e.symm (LevelLieU6.downLe_S6_of hk)

end CFSG.LocalAnalysis.GLTheoremA
