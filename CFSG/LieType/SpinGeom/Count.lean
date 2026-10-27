module

public import CFSG.LieType.SpinGeom.Law
public import CFSG.LieType.SpinGeom.Mem
public import CFSG.LieType.Sp6Spin.Model
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSubspaceCount

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open scoped Matrix

section Counts

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem coordinateQuadPlus_reindex (u : Fin 4 ⊕ Fin 4 → K) :
    coordinateQuadPlus 4 K (reindexVectorEquiv (plusIndexEquiv 4) u) =
      CFSG.LieType.Universal.Spin.quadPlus 4 K u := by
  rw [coordinateQuadPlus_apply, CFSG.LieType.Universal.Spin.quadPlus_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [reindexVectorEquiv_apply, reindexVectorEquiv_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem card_nonzero_singular_eight :
    Nat.card {v : Fin (2 * 4) → K // v ≠ 0 ∧ coordinateQuadPlus 4 K v = 0} =
      (Nat.card K ^ 4 - 1) * (Nat.card K ^ 3 + 1) := by
  have h := CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.card_quadPlus_nonzero_singular
    (K := K) 4
  rw [show (4 : ℕ) - 1 = 3 from rfl] at h
  rw [← h]
  refine Nat.card_congr
    ((reindexVectorEquiv (plusIndexEquiv 4)).toEquiv.symm.subtypeEquiv fun v => ?_)
  obtain ⟨u, rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv 4)).surjective v
  simp only [LinearEquiv.coe_toEquiv_symm]
  rw [coordinateQuadPlus_reindex]
  simp

end Counts

section Stab

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem xvec_frameE_zero : xvec K (frameE K 0) = 0 := by
  ext j
  unfold xvec
  rw [coordX_frameE, if_neg (Fin.succ_ne_zero j).symm]
  rfl

omit [Finite K] [CharP K 2] in
theorem coordY_frameE_zero : coordY K (frameE K 0) 0 = 0 :=
  coordY_frameE 0 0

omit [Finite K] [CharP K 2] in
theorem spinElt_frameE_zero (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K) :
    spinElt K c m g (frameE K 0) = frameE K 0 := by
  apply vec_ext
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordX_spinElt_zero, xvec_frameE_zero, yvec_frameE, coordY_frameE_zero]
      simp
    · rw [coordX_spinElt_succ, xvec_frameE_zero, coordY_frameE_zero, coordX_frameE,
        if_neg (Fin.succ_ne_zero l).symm]
      simp
  · intro k
    refine Fin.cases ?_ (fun l => ?_) k
    · rw [coordY_spinElt_zero]
    · rw [coordY_spinElt_succ, xvec_frameE_zero, yvec_frameE, coordY_frameE_zero, coordY_frameE]
      simp

end Stab

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable abbrev spinMulAction :
    MulAction (spinSeven K) (Fin (2 * 4) → K) where
  smul h v := (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v
  one_smul v := by
    show (((1 : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = v
    simp
  mul_smul h h' v := by
    show ((((h : Om8 K) * (h' : Om8 K) : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
      (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        ((((h' : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v)
    have e : ((((h : Om8 K) * (h' : Om8 K) : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
        (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          (((h' : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := rfl
    rw [e, ← Matrix.mulVec_mulVec]

omit [CharP K 2] [Finite K] in
theorem frameE_ne_zero : frameE K 0 ≠ 0 := by
  intro h
  have h1 := polar_frameE_frameF (K := K) 0 0
  rw [h] at h1
  simp at h1

omit [Finite K] [CharP K 2] in
theorem coordinateQuadPlus_mulVec_om8 (h : Om8 K) (v : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K
        (((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
      coordinateQuadPlus 4 K v :=
  (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ h.2) v

theorem card_spinSeven_eq :
    Nat.card (spinSeven K) = Nat.card K ^ 9 *
      ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 4 - 1) * (Nat.card K ^ 6 - 1))) := by
  rw [natCard_spinSeven, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 3 = {1, 2, 3} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  norm_num

end Main

section StabCount

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem spinStabNormalForm_of_count
    (hMem : ∀ (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K), g.det = 1 →
      ∃ h ∈ spinSeven K, ∀ v,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
          spinElt K c m g v)
    (hTrans : ∀ b : Fin (2 * 4) → K, b ≠ 0 → coordinateQuadPlus 4 K b = 0 →
      ∃ h ∈ spinSeven K,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = b) :
    ∀ h ∈ spinSeven K,
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 =
        frameE K 0 →
      ∃ (c m : Fin 3 → K) (g : Matrix (Fin 3) (Fin 3) K), g.det = 1 ∧ ∀ v,
        ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
          spinElt K c m g v := by
  classical
  let _ : MulAction (spinSeven K) (Fin (2 * 4) → K) := spinMulAction
  have hsmul : ∀ (h : spinSeven K) (v : Fin (2 * 4) → K),
      h • v = (((h : Om8 K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v :=
    fun _ _ => rfl
  set q := Nat.card K with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have horb : MulAction.orbit (spinSeven K) (frameE K 0) =
      {b | b ≠ 0 ∧ coordinateQuadPlus 4 K b = 0} := by
    ext b
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨fun h0 => frameE_ne_zero (K := K) ?_, ?_⟩
      · rw [hsmul] at h0
        have h1 := congrArg (fun w => ((((h⁻¹ : spinSeven K) : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w) h0
        simpa [Matrix.mulVec_mulVec] using h1
      · rw [hsmul, coordinateQuadPlus_mulVec_om8, quad_frameE]
    · rintro ⟨hb0, hbQ⟩
      obtain ⟨h, hm, hh⟩ := hTrans b hb0 hbQ
      exact ⟨⟨h, hm⟩, hh⟩
  have hN : (MulAction.orbit (spinSeven K) (frameE K 0)).ncard = (q ^ 4 - 1) * (q ^ 3 + 1) := by
    rw [horb, ← Nat.card_coe_set_eq]
    exact card_nonzero_singular_eight
  have hidx := MulAction.index_stabilizer (spinSeven K) (frameE K 0)
  have hcm := Subgroup.card_mul_index (MulAction.stabilizer (spinSeven K) (frameE K 0))
  rw [hidx, hN, card_spinSeven_eq] at hcm
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) =
      q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
    rw [← CFSG.Open.StatedAPI.card_statedSL]
    exact CFSG.Open.StatedAPI.card_statedSL_three K
  let Φ : ((Fin 3 → K) × (Fin 3 → K) × Matrix.SpecialLinearGroup (Fin 3) K) →
      MulAction.stabilizer (spinSeven K) (frameE K 0) := fun p =>
    ⟨⟨(hMem p.1 p.2.1 p.2.2.1 p.2.2.2).choose, (hMem p.1 p.2.1 p.2.2.1 p.2.2.2).choose_spec.1⟩,
      by
        rw [MulAction.mem_stabilizer_iff, hsmul]
        show ((((hMem p.1 p.2.1 p.2.2.1 p.2.2.2).choose : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ frameE K 0 = frameE K 0
        rw [(hMem p.1 p.2.1 p.2.2.1 p.2.2.2).choose_spec.2, spinElt_frameE_zero]⟩
  have hΦ : ∀ p v, ((((Φ p : spinSeven K) : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = spinElt K p.1 p.2.1 p.2.2.1 v :=
    fun p v => (hMem p.1 p.2.1 p.2.2.1 p.2.2.2).choose_spec.2 v
  have hinj : Function.Injective Φ := by
    intro p p' hpp'
    have h1 : ∀ v, spinElt K p.1 p.2.1 p.2.2.1 v = spinElt K p'.1 p'.2.1 p'.2.2.1 v := by
      intro v
      rw [← hΦ, ← hΦ, hpp']
    obtain ⟨hc, hm, hg⟩ := spinElt_injective h1
    exact Prod.ext hc (Prod.ext hm (Subtype.ext hg))
  have hD : Nat.card ((Fin 3 → K) × (Fin 3 → K) × Matrix.SpecialLinearGroup (Fin 3) K) =
      q ^ 3 * (q ^ 3 * (q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))) := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, Nat.card_fin, hSL]
  have hq6 : q ^ 6 - 1 = (q ^ 3 + 1) * (q ^ 3 - 1) := by
    have h3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
    zify [h3, h6]
    ring
  have hNpos : 0 < (q ^ 4 - 1) * (q ^ 3 + 1) := by
    have h4 : 1 < q ^ 4 := Nat.one_lt_pow (by omega) (by omega)
    exact Nat.mul_pos (by omega) (by omega)
  have hcard : Nat.card (MulAction.stabilizer (spinSeven K) (frameE K 0)) =
      Nat.card ((Fin 3 → K) × (Fin 3 → K) × Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [hD]
    refine Nat.eq_of_mul_eq_mul_right hNpos ?_
    rw [hcm, ← hq, hq6]
    ring
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  intro h hh hfix
  obtain ⟨p, hp⟩ := hbij.2 ⟨⟨h, hh⟩, by rw [MulAction.mem_stabilizer_iff, hsmul]; exact hfix⟩
  refine ⟨p.1, p.2.1, (p.2.2 : Matrix (Fin 3) (Fin 3) K), p.2.2.2, fun v => ?_⟩
  have hv := hΦ p v
  rw [hp] at hv
  exact hv

end StabCount

end CFSG.LieType.SpinGeom
