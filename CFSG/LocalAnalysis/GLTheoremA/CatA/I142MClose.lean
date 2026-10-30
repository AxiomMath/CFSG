module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NInd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142M

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.I142N CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement


theorem titsCentSolv_holds : TitsCentSolv := by
  intro T _ _ hcat p hp hp2 F hF hF1
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    change d1 = TauCeti.LieTypeIndex.tits at hi
    subst hi
    obtain ⟨eD⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv T 2 1
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := T) ⟨hv, ⟨e⟩⟩)
    haveI : IsSimpleGroup CFSG.Sporadic.Schreier.Tits.titsD := CFSG.Sporadic.Schreier.Tits.titsD_simple
    haveI : IsSimpleGroup T := eD.isSimpleGroup
    haveI : Nontrivial CFSG.Sporadic.Schreier.Tits.titsD := CFSG.Sporadic.Schreier.Tits.titsD_nontrivial
    have hncD := CFSG.HardMathSupport.Dickson.Sec6.I923.exists_noncomm_of_center_bot
      CFSG.Sporadic.Schreier.Tits.titsD_center
    have hnc : ∃ a b : T, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hncD
      exact ⟨eD.symm a, eD.symm b, fun h => hab (eD.symm.injective (by simpa using h))⟩
    obtain ⟨β, hβ1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    have hβp : (β : MulAut T) ^ p = 1 := hF.2 β β.2
    have hβ1' : (β : MulAut T) ≠ 1 := fun h => hβ1 (Subtype.ext h)
    haveI := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.isSolvable_fixSubgroup_tits hv hnc ⟨e⟩ hp hp2
      hβp hβ1'
    have hle : I142.centFix F ≤ fixSubgroup (β : MulAut T) := fun x hx =>
      mem_fixSubgroup.2 ((I142.mem_centFix).1 hx _ β.2)
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hle)
  | _ => simp [onLie] at hi

theorem exists_noncomm_quot_center {K : Type*} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    ∃ a b : K ⧸ Subgroup.center K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hnt := hK.2.toNontrivial
  have hker : commutator K ≤ (QuotientGroup.mk' (Subgroup.center K)).ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h _ _
  rw [hK.1] at hker
  obtain ⟨q, hq⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center K) q
  exact hq (hker (Subgroup.mem_top k))

theorem isChevSimple_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : IsChevSimple 2 Y) :
    IsChevSimple 2 X := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

theorem compTypesCyc_holds : CompTypesCyc := by
  intro S _ _ hS hnc hchev p hp hp2 β hβ K hK
  have hQ := hK.2.2
  refine ⟨hQ.2, exists_noncomm_quot_center hQ, Or.inl ?_⟩
  by_cases hβ1 : β = 1
  · subst hβ1
    have htop : I142.centFix (Subgroup.zpowers (1 : MulAut S)) = ⊤ := by
      rw [CFSG.LocalAnalysis.GLTheoremA.I142C.centFix_zpowers']
      ext x
      simp [mem_fixSubgroup]
    rw [htop] at hK
    haveI := hS
    haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
    have hKnt : Nontrivial ↥K := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      haveI := h
      exact (not_subsingleton_iff_nontrivial.2 hQ.2.toNontrivial) inferInstance
    have hKtop : K = ⊤ := CFSG.LocalAnalysis.GLTheoremA.AltDown.eq_of_isSubnormal_of_isSimpleGroup hK.2.1
      ((Subgroup.nontrivial_iff_ne_bot K).1 hKnt)
    have eK : ↥K ≃* S := (MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv
    haveI : IsSimpleGroup ↥K := eK.isSimpleGroup
    have hncK : ∃ a b : ↥K, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnc
      exact ⟨eK.symm a, eK.symm b, fun h => hab (eK.symm.injective (by simpa using h))⟩
    have hZ : Subgroup.center ↥K = ⊥ :=
      CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hncK
    exact isChevSimple_of_equiv
      (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eK) hchev
  · exact CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds S hS hnc hchev p hp hp2 β hβ hβ1 K hK

theorem residualNonCyc_holds : I142.ResidualNonCyc :=
  residualNonCyc_of_K compTypesCyc_holds titsCentSolv_holds

end CFSG.LocalAnalysis.GLTheoremA.I142M
