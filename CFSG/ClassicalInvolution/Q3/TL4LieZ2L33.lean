module

public import CFSG.ClassicalInvolution.Q3.TL4LieZ2Ck
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Exit
public import CFSG.ClassicalInvolution.Q3.TL4OddLieZ2
public import CFSG.ClassicalInvolution.Q3.TA3SmallModels
public import Certificates.Certificate55123
public import CFSG.ClassicalInvolution.Q3.TA3SOLCore
public import CFSG.ClassicalInvolution.Q3.TA3SOLCoreRank
public import CFSG.ClassicalInvolution.Q3.TL4E3MuPass
public import CFSG.ClassicalInvolution.Q3.TL4MF163L3
public import CFSG.ClassicalInvolution.Q3.TL4MF163U3
public import CFSG.ClassicalInvolution.Q3.TL4MF164M11
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2B3
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LieZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups
open scoped MatrixGroups


theorem linkZ2Model_l33 {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}
    (hsec : LieLinkSection Φ) (hsh : SecIdQ8Shape (CompData.model .PSL 3) Φ) :
    LinkZ2Model X Φ := by
  obtain ⟨ψ, hψ, hker, -⟩ := hsh
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (le_of_eq TL4.center_sl3_eq_bot)
  have hpinj : Function.Injective (proj 3 (GaloisField 3 1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_center, TL4.center_sl3_eq_bot]
  let e : X ≃* projectiveSL 3 (GaloisField 3 1) :=
    (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).symm.trans
      (MulEquiv.ofBijective (proj 3 (GaloisField 3 1)) ⟨hpinj, proj_surjective 3 _⟩)
  have hcard : Nat.card (GaloisField 3 1) = 3 ^ 1 := GaloisField.card 3 1 one_ne_zero
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [hcard]
    decide
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 3 1)) :=
    (CFSG.LinearGroups.linear_projective_simple (by norm_num) (Or.inl le_rfl)).2.1
  have hs : IsSimpleGroup X :=
    (e.trans (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 _).symm).isSimpleGroup
  have : IsSimpleGroup (projectiveSL 3 (GaloisField 3 1)) := e.symm.isSimpleGroup
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hZ : Subgroup.center (projectiveSL 3 (GaloisField 3 1)) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => by
        have h1 := congrArg e (hc (e.symm y) (e.symm x))
        simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)] at hZ
    exact bot_ne_top hZ
  have hl : LieModel X .PSL 3 3 1 :=
    Or.inl ⟨by decide, ⟨Nat.prime_three, le_rfl, by decide⟩, GaloisField 3 1, inferInstance,
      inferInstance, hcard, ⟨e.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
        _).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 3 _))⟩⟩
  obtain ⟨eP⟩ := L33.equiv_of_lieModel hl
  obtain ⟨Mo, hMP, hMA⟩ := L33.autModel eP
  have hPA : Mo.P ≤ Mo.A := by
    rw [hMP, hMA, L33.QP_closure, TA3.l33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  have h163 := concl163_of_autModel Mo (LP := elemsT L33.QP) (LA := elemsT L33.QA)
    (reps := pickReps (elemsT L33.QP))
    (fun g => by
      rw [hMP]
      exact mem_elemsT _ L33.QP_ok g)
    (fun g hg => (mem_elemsT _ L33.QA_ok g).2 (hMA ▸ hg)) hPA
    Certificates.certificate55123.1 hsec.1
  have hF : genFittingFStar X = ⊤ :=
    ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnab
  let eF : ↥(genFittingFStar X) ≃* X := (MulEquiv.subgroupCongr hF).trans Subgroup.topEquiv
  have hα : AutAlphaPairs ↥(genFittingFStar X) :=
    autAlphaPairs_of_lieModel _ 3 1 Nat.prime_three (by norm_num)
      (Or.inl (MFMuZ2.lieModel_of_mulEquiv_classical eF (Or.inl rfl) hl))
  exact Z2Exit.linkZ2Model_of_mulEquiv hs hnab e hα
    (fun a b ha hb => E3S3Gen.exists_conj_psl3 hodd ha hb)
    (fun a b ha hb hab hne => E3C269G.sup_centralizer_eq_top_psl3 hodd ha hb hab hne) h163

end CFSG.ClassicalInvolution.Q3.TL4.LieZ2
