module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (blockSwapJ)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical (matrixIsometryGroup
  mem_matrixIsometryGroup det_eq_one_of_mem eq_one_of_mem_of_scalar)
open CFSG.ComponentClassification.OutcomeLocal (blockSwapIsometryEquivStatedSp
  coe_blockSwapIsometryEquivStatedSp sumFinEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.UnbalancedCatalog (IsCanonicalGram isCanonicalGram_blockSwapJ
  commute_pureGraph_conjAut_iff)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

section Generic

variable {P : Type*} [Group P]

theorem mulAut_mul_conj_eq_conj_apply_mul (β : MulAut P) (y : P) :
    β * MulAut.conj y = MulAut.conj (β y) * β := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem apply_eq_of_commute_mulAut_conj (hcj : Function.Injective (MulAut.conj : P →* MulAut P))
    {β : MulAut P} {y : P} (h : Commute β (MulAut.conj y)) : β y = y := by
  apply hcj
  have h1 := mulAut_mul_conj_eq_conj_apply_mul β y
  rw [h.eq] at h1
  exact (mul_right_cancel h1).symm

theorem commute_conj_of_apply_eq {β : MulAut P} {y : P} (h : β y = y) :
    Commute β (MulAut.conj y) := by
  change β * MulAut.conj y = MulAut.conj y * β
  rw [mulAut_mul_conj_eq_conj_apply_mul, h]

end Generic

section Embed

variable (n : ℕ) (F : Type) [Field F] [CharP F 2]

theorem blockSwapJ_two_mul_mul_self :
    (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) * blockSwapJ (2 * n) n = 1 :=
  (isCanonicalGram_blockSwapJ (K := F) (n := 2 * n) (r := n) (two_mul n).symm).sq

theorem det_blockSwapJ_two_mul_ne_zero :
    (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (blockSwapJ_two_mul_mul_self n F)
  rw [det_mul, h0, zero_mul, det_one] at h
  exact zero_ne_one h

@[expose] noncomputable def spModelIsoSL :
    matrixIsometryGroup (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) →*
      SpecialLinearGroup (Fin (2 * n)) F where
  toFun g := ⟨((g : GL (Fin (2 * n)) F) : Matrix (Fin (2 * n)) (Fin (2 * n)) F),
    det_eq_one_of_mem (det_blockSwapJ_two_mul_ne_zero n F) g.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

@[expose] noncomputable def spModelSL : StatedSp n F →* SpecialLinearGroup (Fin (2 * n)) F :=
  (spModelIsoSL n F).comp
    (blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm).symm.toMonoidHom

@[expose] noncomputable def spModelPSL : StatedSp n F →* projectiveSL (2 * n) F :=
  (proj (2 * n) F).comp (spModelSL n F)

abbrev spModelIdx : Fin n ⊕ Fin n ≃ Fin (2 * n) := sumFinEquiv (two_mul n).symm

variable {n F}

theorem spModelIdx_inl_val (i : Fin n) : ((spModelIdx n (Sum.inl i) : Fin (2 * n)) : ℕ) = i := by
  simp [spModelIdx, sumFinEquiv]

theorem spModelIdx_inr_val (i : Fin n) :
    ((spModelIdx n (Sum.inr i) : Fin (2 * n)) : ℕ) = n + i := by
  simp [spModelIdx, sumFinEquiv]
  omega

theorem spModelPSL_apply (x : StatedSp n F) :
    spModelPSL n F x = proj (2 * n) F (spModelSL n F x) := rfl

theorem coe_spModelSL (x : StatedSp n F) :
    ((spModelSL n F x : SpecialLinearGroup (Fin (2 * n)) F) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) F) =
      ((x : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).submatrix
        (spModelIdx n).symm (spModelIdx n).symm := by
  set g := (blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm).symm x with hg
  have h1 := coe_blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm g
  rw [hg, MulEquiv.apply_symm_apply] at h1
  rw [h1, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  rfl

theorem spModelSL_mem (x : StatedSp n F) :
    SpecialLinearGroup.toGL (spModelSL n F x) ∈
      matrixIsometryGroup (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) :=
  ((blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm).symm x).2

theorem spModelSL_injective : Function.Injective (spModelSL n F) := by
  intro x y h
  apply (blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm).symm.injective
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun g : SpecialLinearGroup (Fin (2 * n)) F =>
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) F)) h

theorem spModelPSL_injective (hn : 1 ≤ n) : Function.Injective (spModelPSL n F) := by
  have : NeZero (2 * n) := ⟨by omega⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, -, hc⟩ := proj_eq_one_iff.1 hx
  have hJ : (blockSwapJ (2 * n) n : Matrix (Fin (2 * n)) (Fin (2 * n)) F) ≠ 0 := by
    intro h0
    have h := blockSwapJ_two_mul_mul_self n F
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have h1 : SpecialLinearGroup.toGL (spModelSL n F x) = 1 :=
    eq_one_of_mem_of_scalar hJ (spModelSL_mem x) (c := (c : F)) hc
  have h2 : spModelSL n F x = spModelSL n F 1 := by
    rw [map_one]
    apply Subtype.ext
    exact congrArg (fun g : GL (Fin (2 * n)) F => (g : Matrix (Fin (2 * n)) (Fin (2 * n)) F)) h1
  exact spModelSL_injective h2

theorem conjAut_dualAut_spModelPSL [Finite F] (hn : 2 ≤ n) {C : GL (Fin (2 * n)) F}
    (hC : (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = blockSwapJ (2 * n) n) (x : StatedSp n F) :
    (conjAut (2 * n) F C * dualAut (2 * n) F) (spModelPSL n F x) = spModelPSL n F x := by
  have hCan : IsCanonicalGram (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) := by
    rw [hC]
    exact isCanonicalGram_blockSwapJ (two_mul n).symm
  have hmem : SpecialLinearGroup.toGL (spModelSL n F x) ∈
      matrixIsometryGroup (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) := by
    rw [hC]
    exact spModelSL_mem x
  have hcomm := (commute_pureGraph_conjAut_iff hCan (by omega : 3 ≤ 2 * n)
    (SpecialLinearGroup.toGL (spModelSL n F x))).2 ⟨_, hmem, rfl⟩
  rw [conjAut_toGL] at hcomm
  exact apply_eq_of_commute_mulAut_conj (ProjectivePlane.conj_injective_projectiveSL (by omega)) hcomm

theorem range_spModelPSL [Finite F] {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hn : 2 ≤ n)
    {C : GL (Fin (2 * n)) F}
    (hC : (C : Matrix (Fin (2 * n)) (Fin (2 * n)) F) = blockSwapJ (2 * n) n) :
    (spModelPSL n F).range = fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F) := by
  have hle : (spModelPSL n F).range ≤
      fixedSubgroup (conjAut (2 * n) F C * dualAut (2 * n) F) := by
    rintro _ ⟨x, rfl⟩
    exact conjAut_dualAut_spModelPSL hn hC x
  obtain ⟨E⟩ := CFSG.ComponentClassification.CatLeafProof.nonempty_fixed_canonical_equiv hf hF
    (by omega) C (Or.inr ⟨n, rfl, hC⟩)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr E.toEquiv, hC,
    Nat.card_congr (blockSwapIsometryEquivStatedSp (k := F) (two_mul n).symm).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective (spModelPSL_injective (by omega))).toEquiv]

end Embed

end CFSG.SeitzReduction.SymplecticPilot
