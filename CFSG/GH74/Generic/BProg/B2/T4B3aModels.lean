module

public import CFSG.GH74.Generic.BProg.B2.T4B3aGen
public import CFSG.GH74.Generic.BProg.B2.T4L5InvModels
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.B3aModels

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KFU
open CFSG.GH74.Generic.BProg.B2.T4.L5Inv CFSG.GH74.Generic.BProg.B2.T4.L5Count
open CFSG.GH74.Generic.BProg.B2.T4.B3aGen

section Linear

variable {F : Type} [Field F]

theorem blkP_projSL (I : Finset (Fin 5)) :
    blkP (StatedSL 5 F) (L5InvModels.projSL F) I = CFSG.SeitzReduction.LinearPilot.blockSL I := by
  rw [blkP, CFSG.SeitzReduction.LinearPilot.blockSL, L5InvModels.projSL, ← Subgroup.map_map]
  congr 1
  ext A
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_symm, Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL,
    CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear, specialLinearGroupEquivStatedSL_coe]

theorem card_erase_five (m : Fin 5) : (Finset.univ.erase m).card = 4 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ, Fintype.card_fin]

theorem isQuasisimple_blockSL (m : Fin 5) :
    CFSG.IsQuasisimple ↥(CFSG.SeitzReduction.LinearPilot.blockSL (K := F) (Finset.univ.erase m)) := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.blockSL_mulEquiv (K := F) (I := Finset.univ.erase m)
    (by rw [card_erase_five]; norm_num)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by rw [card_erase_five]; norm_num))

theorem model_projectiveSL [Finite F] (hF : ringChar F ≠ 2) :
    Model (StatedSL 5 F) (L5InvModels.projSL F) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hsgn : ∀ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1), ∏ i, ε i = 1 → sgnGL ε hε ∈ StatedSL 5 F :=
    fun ε hε hdet => (L5InvModels.mem_statedSL_iff' _).2 (by rw [coe_sgnGL, Matrix.det_diagonal, hdet])
  refine ⟨h2, fun s hs => (L5InvModels.mem_statedSL_iff' s).1 hs, ?_, ?_, hsgn, ?_, ?_⟩
  · intro x
    obtain ⟨A, rfl⟩ := LinearFlag.proj_surjective 5 F x
    refine ⟨specialLinearGroupEquivStatedSL 5 F A, ?_⟩
    show LinearFlag.proj 5 F ((specialLinearGroupEquivStatedSL 5 F).symm
      (specialLinearGroupEquivStatedSL 5 F A)) = _
    rw [MulEquiv.symm_apply_apply]
  · intro s hs
    have hs' : LinearFlag.proj 5 F ((specialLinearGroupEquivStatedSL 5 F).symm s) = 1 := hs
    rw [LinearFlag.proj_eq_one_iff, LinearFlag.mem_scalars] at hs'
    obtain ⟨c, -, hc⟩ := hs'
    refine ⟨c, ?_⟩
    have e : ((s : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        (((specialLinearGroupEquivStatedSL 5 F).symm s : SpecialLinearGroup (Fin 5) F) :
          Matrix (Fin 5) (Fin 5) F) := by
      rw [← specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
    rw [e, hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · intro m
    have e := blkP_projSL (F := F) (Finset.univ.erase m)
    rw [blkP] at e
    rw [e]
    exact isQuasisimple_blockSL m
  · intro v hv hv1
    have hstd : ∀ k, k = 2 ∨ k = 4 → sgnGL (stdSign (F := F) k) (stdSign_sq k) ∈ StatedSL 5 F :=
      fun k hk => hsgn _ _ (prod_stdSign hk)
    obtain ⟨k, hk, g, hg⟩ := exists_conj_std_of_model h2 (StatedSL 5 F) ⊤
      (fun s hs => (L5InvModels.mem_statedSL_iff' s).1 hs) (fun n _ hn => (L5InvModels.mem_statedSL_iff' n).2 hn)
      (fun _ => Subgroup.mem_top _) L5InvModels.adj_top (L5InvModels.projSL F)
      (L5InvModels.lift_projectiveSL hF) hstd v hv hv1
    exact ⟨k, hk, g, ⟨_, hstd k hk⟩, rfl, hg⟩

end Linear

section Unitary

variable {K : Type} [Field K] {p f : ℕ}

abbrev projSU (p f : ℕ) (K : Type) [Field K] :
    ↥(StatedSU 5 (p ^ f) K) →* StatedProj (StatedSU 5 (p ^ f) K) :=
  QuotientGroup.mk' _

theorem blkP_statedSU (h : UnitaryFieldData p f K) (I : Finset (Fin 5)) :
    blkP (StatedSU 5 (p ^ f) K) (projSU p f K) I =
      (CFSG.SeitzReduction.UnitaryPilot.blockSU h I).map
        (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num)).toMonoidHom := by
  rw [blkP, CFSG.SeitzReduction.UnitaryPilot.blockSU, Subgroup.map_map]
  have hcomp : (ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num : 1 ≤ 5)).toMonoidHom.comp
      (ClassicalGroups.UnitaryFlag.unitaryProj h 5) = QuotientGroup.mk' _ := by
    ext g
    exact ClassicalGroups.UnitaryFlag.unitaryPSUEquiv_unitaryProj h (by norm_num) g
  rw [hcomp]
  rfl

theorem sgnGL_mem_statedSU (h : UnitaryFieldData p f K) (ε : Fin 5 → K) (hε : ∀ i, ε i * ε i = 1)
    (hdet : ∏ i, ε i = 1) : sgnGL ε hε ∈ StatedSU 5 (p ^ f) K := by
  rw [ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h, coe_sgnGL, Matrix.det_diagonal]
  refine ⟨hdet, ?_⟩
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases L5Count.eq_one_or_neg_one (hε i) with hi | hi
  · rw [hi, map_one, mul_one]
  · rw [hi, map_neg, map_one, neg_mul_neg, mul_one]

theorem model_statedSU [Finite K] (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) :
    Model (StatedSU 5 (p ^ f) K) (projSU p f K) := by
  set h := GenLocDiagU.unitaryFieldData_of_card hp hK with hh
  have h2 : (2 : K) ≠ 0 := L5InvModels.two_ne_zero_of_card hp hp2 hK
  have hsgn : ∀ (ε : Fin 5 → K) (hε : ∀ i, ε i * ε i = 1), ∏ i, ε i = 1 →
      sgnGL ε hε ∈ StatedSU 5 (p ^ f) K := sgnGL_mem_statedSU h
  refine ⟨h2, fun s hs => ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 hs).1,
    QuotientGroup.mk'_surjective _, ?_, hsgn, ?_, ?_⟩
  · intro s hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars,
      MonoidHom.mem_range] at hs
    obtain ⟨c, hc⟩ := hs
    refine ⟨c, ?_⟩
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · intro m
    have e := blkP_statedSU (p := p) (f := f) h (Finset.univ.erase m)
    rw [blkP] at e
    rw [e]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num)).subgroupMap _)
      (CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_blockSU h (by rw [B3aModels.card_erase_five])
        (by rw [B3aModels.card_erase_five]; norm_num))
  · intro v hv hv1
    have hstd : ∀ k, k = 2 ∨ k = 4 → sgnGL (stdSign (F := K) k) (stdSign_sq k) ∈ StatedSU 5 (p ^ f) K :=
      fun k hk => hsgn _ _ (prod_stdSign hk)
    obtain ⟨k, hk, g, hg⟩ := exists_conj_std_of_model h2 (StatedSU 5 (p ^ f) K)
      (UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K))
      (fun s hs => ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).1 hs).1)
      (fun n hn hdet => (ClassicalGroups.UnitaryFlag.mem_unitarySU_iff h).2
        ⟨hdet, (L5InvModels.mem_formU_iff h n).1 hn⟩)
      (L5InvModels.permGL5_mem_unitary h) (L5InvModels.adj_unitary h) (projSU p f K)
      (L5InvModels.lift_statedSU hp hp2 hK) hstd v hv hv1
    exact ⟨k, hk, g, ⟨_, hstd k hk⟩, rfl, hg⟩

end Unitary

theorem b3aFact_of_puL5 {J : Type} [Group J] (hJ : PuL5 J) : B3aFact J := by
  obtain ⟨p, f, hp, hp2, hf, ⟨-, hm⟩ | ⟨-, hm⟩⟩ := hJ
  · obtain ⟨⟨hprime, hf', -⟩, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 5 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
    exact b3aFact_of_mulEquiv ψ
      (model_projectiveSL (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hprime hp2 hF)).b3aFact
  · obtain ⟨⟨hprime, hf', -⟩, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact b3aFact_of_mulEquiv e (model_statedSU hprime hp2 hK).b3aFact

end CFSG.GH74.Generic.BProg.B2.T4.B3aModels
