module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107GSurvBr
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpForm
public import CFSG.LargeExtraspecial.S45QPhi
public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem perm6_component_eq_alt {K : Subgroup (Equiv.Perm (Fin 6))}
    (hK : CFSG.Open.IsComponentOf K ⊤) : K = alternatingGroup (Fin 6) := by
  have hle : K ≤ alternatingGroup (Fin 6) := by
    have hperf : ⁅K, K⁆ = K := commutator_self_eq_of_quasisimple_sub hK.2.2
    rw [← hperf]
    show ⁅K, K⁆ ≤ _
    rw [Subgroup.commutator_le]
    intro a _ b _
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hsub : CFSG.Open.IsSubnormal K (alternatingGroup (Fin 6)) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hK.2.1 (le_top : alternatingGroup (Fin 6) ≤ ⊤)
    rwa [inf_eq_left.mpr hle] at h
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance with h | h
  · exfalso
    haveI := hK.2.2.2
    have hnt : Nontrivial ↥K :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot K).mp hnt h
  · exact h

theorem sp2_component_alt {G : Type} [Group G] (e : G ≃* StatedSp 2 (ZMod 2)) {K : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K ⊤) : Nonempty (↥K ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.exists_stdIso 2
  obtain ⟨e2⟩ := CFSG.LargeExtraspecial.S45Q.nonempty_isometryGroup_equiv_perm
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.stdForm_isAlt 2)
    (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.stdForm_nondeg 2)
    (by rw [CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp.stdForm_finrank])
  let f : G ≃* Equiv.Perm (Fin 6) := e.trans (e1.trans e2)
  have hK' : CFSG.Open.IsComponentOf (K.map (f : G →* Equiv.Perm (Fin 6))) ⊤ := by
    have h := isComponentOf_map_mulEquiv hK f
    rwa [Subgroup.map_top_of_surjective _ f.surjective] at h
  have heq := perm6_component_eq_alt hK'
  exact ⟨(Subgroup.equivMapOfInjective K (f : G →* Equiv.Perm (Fin 6)) f.injective).trans
    (MulEquiv.subgroupCongr heq)⟩

theorem sp1_solvable : Group.IsSolvable (StatedSp 1 (ZMod 2)) := by
  obtain ⟨e⟩ := CFSG.RankThree.GF2n.Stroth80.nonempty_statedSp_one_mulEquiv_statedSL_two (ZMod 2)
  have hcard : Nat.card (StatedSL 2 (ZMod 2)) = 2 ^ 1 * 3 ^ 1 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, Nat.card_zmod 2]
    norm_num
  have hsol : Group.IsSolvable ↥(StatedSL 2 (ZMod 2)) :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
      Nat.prime_two Nat.prime_three (by norm_num) hcard
  haveI := hsol
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem catalogIs_sp6_of_equiv {X : Type} [Group X] (e : X ≃* StatedSp 3 (ZMod 2)) :
    catalogIs X S9.isSp6two := by
  have hP0 : S9.isSp6two (TauCeti.CFSGIndex.lie
      ⟨TauCeti.LieTypeIndex.B 3 CFSG.LocalAnalysis.GLTheoremA.I107G.pp2,
        CFSG.LocalAnalysis.GLTheoremA.I107G.valid_B3⟩) := by
    show CFSG.LocalAnalysis.GLTheoremA.I107G.pp2.card = 2
    simp [CFSG.LocalAnalysis.GLTheoremA.I107G.pp2, TauCeti.PrimePower.card_def]
  exact CFSG.LocalAnalysis.GLTheoremA.I107G.catalogIs_of_model _ hP0
    (fun {S} _ h => CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_sp6two h) e

theorem catalogIs_alt6_of_equiv {X : Type} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    catalogIs X CFSG.LocalAnalysis.GLTheoremA.S10.isA6 := by
  have h6 : 5 ≤ 6 := by norm_num
  exact ⟨TauCeti.CFSGIndex.alternating 6 h6, rfl, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
