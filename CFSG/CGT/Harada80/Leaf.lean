module

public import CFSG.CGT.Harada80.WeakClosure
public import CFSG.CGT.Harada80.CaseA
public import CFSG.CGT.HaradaParrott80.Catalog
public import CFSG.CGT.Harada80.Tight
public import CFSG.CGT.Harada80.H1Eight
public import CFSG.CGT.Foote82.T66.CertProofsH1OmegaMinusSix
public import CFSG.Milestones.CL_LIT_classical_involution_theorem
public import CFSG.Yardstones.M50b1bb4a7c08.SlotInputs
public import CFSG.RankThree.PartOne.S12.SolInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HResidual
public import CFSG.CGT.PushingUpLit.SolKNA.RankGe2Sz
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieInspection
import CFSG.LocalAnalysis.ComponentClassification.HallQ8Main

public section

namespace CFSG.CGT.Harada80

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.RankThree.PartTwo

namespace Setting

variable {G : Type} [Group G] [Finite G] {M J : Subgroup G} {m : ℕ}

theorem h1Natural
    (S : Setting G M J m) : H1Natural m := by
  rcases S.m_eq with rfl | rfl
  · exact h1Natural_two CFSG.CGT.Foote82.h1OmegaMinusSix_holds
  · exact h1Natural_three OmegaEight.h1OmegaMinusEight_holds

private theorem comm_of_cyclic_or_elemAbelian {W : Subgroup G}
    (h : (IsCyclic ↥W ∧ Nat.card ↥W = 4) ∨ IsElemAbelian 2 W) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  have hW : IsMulCommutative ↥W := by
    rcases h with ⟨h, -⟩ | h
    exacts [IsCyclic.isMulCommutative, h.1]
  intro a ha b hb
  exact congrArg Subtype.val (hW.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem quadQ_beta_eq_zero_of_vec (S : Setting G M J m) (hZ : blockZ J = ⊥)
    {u : ↥(blockU J)} (hu1 : u ≠ 1) (hu : quadQ m (S.vec u) = 0) :
    quadQ m (Multiplicative.toAdd (S.beta u)) = 0 := by
  obtain ⟨a, ha⟩ := S.beta_surjective (Multiplicative.ofAdd (S.vec u))
  have hav : Multiplicative.toAdd (S.beta a) = S.vec u := by rw [ha, toAdd_ofAdd]
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hu1 ((S.vec_eq_zero_iff hZ).mp (by rw [← hav, map_one, toAdd_one]))
  have hau : a = u := S.vec_injective hZ
    ((CFSG.CGT.HaradaParrott80.vec_eq_of_singular S hZ ha1 (by rw [hav, hu])).trans hav)
  rw [← hau, hav, hu]

theorem inCatalog_of_smith
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    (hS : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP) (S : Setting G M J m) :
    CFSG.Assembly.InCatalog G := by
  have hH1 := S.h1Natural
  rcases S.inCatalog_or_tight hNode hSTT with h | hC | ⟨hne, hle, hab, -⟩
  · exact h
  · by_cases hA : ∀ u : ↥(blockU J), u ≠ 1 → quadQ m (S.vec u) = 0 →
        Subgroup.centralizer ({(u : G)} : Set G) ≤ M
    · exact inCatalog_of_caseA hNode S ⟨hH1, hC, hA⟩
    · push Not at hA
      obtain ⟨u, hu1, hu, hnot⟩ := hA
      exact S.inCatalog_of_not_le hS hH1 hC hu1
        (quadQ_beta_eq_zero_of_vec S (S.blockZ_eq_bot hH1) hu1 hu) hnot
  · exact inCatalog_of_evenCase hNode S
      ⟨⟨hH1, hle, comm_of_cyclic_or_elemAbelian hab⟩, hne⟩

end Setting

theorem lit316Harada_of_tight
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    (hS : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP) :
    CFSG.RankThree.PartTwo.Sec19.Lit316Harada :=
  lit316Harada_of_setting CFSG.CGT.PushingUpLit.LIT.Foote.footeNonsolvableSimple_holds
    fun _ _ _ _ _ _ S =>
      S.inCatalog_of_smith CFSG.RankThree.PartTwo.Sec19.SolSeven.nodeStatement_holds hSTT hS

theorem lit316Harada_of_smith
    (hS : CFSG.GF2Type.Smith1979WidthsFourSixCharTwoKP) :
    CFSG.RankThree.PartTwo.Sec19.Lit316Harada :=
  lit316Harada_of_tight (CFSG.RankThree.PartOne.SolIn.solomonTimmesfeldTight_of_inputs
      (CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof.asc76Lemma25_of_hallQ8Residual
          CFSG.ComponentClassification.Foote5.HallGen.hallQ8Residual)
      (⟨PushingUpLit.SolKNA.solomonTimmesfeldMainNonAbelian_of_cit_lie_sz
          CFSG.Milestones.cl_lit_classical_involution_theorem_models
          (PushingUpLit.SolKNA.quaternionInspectionLie_of_cit3
              (PushingUpLit.SolKNA.cit3Inductive_of_citInputs
                  CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots)
              (PushingUpLit.SolKNA.tightLiftSimple_of_citInputs
                  CFSG.Yardstones.M50b1bb4a7c08.citInputs_of_slots))
          PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate,
          PushingUpLit.SolKR2.solomonTimmesfeldMainRankTwo_holds⟩ :
          PushingUpLit.SolKAb.SolomonTimmesfeldMainResidue)) hS

end CFSG.CGT.Harada80
