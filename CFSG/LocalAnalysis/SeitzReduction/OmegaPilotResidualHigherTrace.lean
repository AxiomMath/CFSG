module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFRSmallGraph
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_elt elt E)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

variable (r K) in
@[expose] noncomputable def spProjEquivCharTwo : StatedProj (StatedSp r K) ≃* StatedSp r K :=
  (QuotientGroup.quotientMulEquivOfEq
    (CFSG.Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot r)).trans
    QuotientGroup.quotientBot

@[expose] noncomputable def spTrace (x : StatedProj (StatedSp r K)) : K :=
  Matrix.trace (((spProjEquivCharTwo K r x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)

theorem spTrace_proj (g : StatedSp r K) :
    spTrace (proj r K g) =
      Matrix.trace (((g : GL (Fin r ⊕ Fin r) K)) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  rfl

theorem spTrace_conjAut (A : gsp r K) (x : StatedProj (StatedSp r K)) :
    spTrace (conjAut r K A x) = spTrace x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change spTrace (conjAut r K A (proj r K g)) = spTrace (proj r K g)
  rw [conjAut_proj, spTrace_proj, spTrace_proj, coe_conjSp, Units.val_mul, Units.val_mul,
    Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem spTrace_fieldAut (σ : K ≃+* K) (x : StatedProj (StatedSp r K)) :
    spTrace (fieldAut r K σ x) = σ (spTrace x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  change spTrace (fieldAut r K σ (proj r K g)) = σ (spTrace (proj r K g))
  rw [fieldAut_proj, spTrace_proj, spTrace_proj, coe_fieldSp, Matrix.trace, Matrix.trace,
    map_sum]
  rfl

theorem spTrace_surjective (hr : 1 ≤ r) (c : K) : ∃ x : StatedProj (StatedSp r K), spTrace x = c := by
  set i : Fin r := ⟨0, hr⟩
  refine ⟨proj r K (elt (.positiveLong i) c * elt (.negativeLong i) (1 : K)), ?_⟩
  rw [spTrace_proj, ← mat_apply, map_mul, mat_elt, mat_elt]
  simp only [E, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.trace_add,
    Matrix.smul_mul, Matrix.trace_smul, Matrix.single_mul_single_same,
    Matrix.trace_single_eq_of_ne _ _ _ Sum.inl_ne_inr, Matrix.trace_single_eq_of_ne _ _ _
      Sum.inr_ne_inl, Matrix.trace_single_eq_same, Matrix.trace_one, smul_eq_mul, mul_zero,
    mul_one, one_smul, add_zero, Fintype.card_sum, Fintype.card_fin]
  have h2 : ((r + r : ℕ) : K) = 0 := by
    rw [← two_mul, Nat.cast_mul, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_mul]
  rw [h2, zero_add, zero_add]

variable (r) in
@[expose] def SpTraceRead (θ : MulAut (StatedProj (StatedSp r K))) (σ : K ≃+* K) : Prop :=
  ∀ x, spTrace (θ x) = σ (spTrace x)

theorem spTraceRead_unique (hr : 1 ≤ r) {θ : MulAut (StatedProj (StatedSp r K))}
    {σ σ' : K ≃+* K} (h : SpTraceRead r θ σ) (h' : SpTraceRead r θ σ') : σ = σ' := by
  apply RingEquiv.ext
  intro c
  obtain ⟨x, rfl⟩ := spTrace_surjective hr c
  rw [← h x, h' x]

theorem spTraceRead_conjAut_mul_fieldAut (A : gsp r K) (σ : K ≃+* K) :
    SpTraceRead r (conjAut r K A * fieldAut r K σ) σ := fun x => by
  rw [MulAut.mul_apply, spTrace_conjAut, spTrace_fieldAut]

variable [Finite K]

theorem exists_spTraceRead (hr : 3 ≤ r) (θ : MulAut (StatedProj (StatedSp r K))) :
    ∃ σ, SpTraceRead r θ σ := by
  obtain ⟨A, σ, rfl⟩ := (automorphism_generation (K := K) hr).2 θ
  exact ⟨σ, spTraceRead_conjAut_mul_fieldAut A σ⟩

theorem spTraceRead_conj (hr : 3 ≤ r) (μ : MulAut (StatedProj (StatedSp r K)))
    {θ : MulAut (StatedProj (StatedSp r K))} {σ : K ≃+* K} (h : SpTraceRead r θ σ) :
    SpTraceRead r (μ * θ * μ⁻¹) σ := by
  obtain ⟨τ, hτ⟩ := exists_spTraceRead hr μ
  intro x
  have hinv : spTrace (μ⁻¹ x) = τ.symm (spTrace x) := by
    rw [RingEquiv.eq_symm_apply, ← hτ, MulAut.apply_inv_self]
  rw [MulAut.mul_apply, MulAut.mul_apply, hτ, h, hinv]
  change (τ * σ * τ⁻¹) (spTrace x) = σ (spTrace x)
  rw [LinearPilot.ringEquiv_mul_comm τ σ, mul_assoc, mul_inv_cancel, mul_one]

omit [Finite K] in
theorem spTrace_conj (x y : StatedProj (StatedSp r K)) :
    spTrace (MulAut.conj x y) = spTrace y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  change spTrace (proj r K g * proj r K h * (proj r K g)⁻¹) = spTrace (proj r K h)
  rw [← map_inv, ← map_mul, ← map_mul, spTrace_proj, spTrace_proj]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

omit [Finite K] in
theorem spTraceRead_conj_of_outerCommutative (hout : OuterCommutative (StatedProj (StatedSp r K)))
    (μ : MulAut (StatedProj (StatedSp r K))) {θ : MulAut (StatedProj (StatedSp r K))}
    {σ : K ≃+* K} (h : SpTraceRead r θ σ) : SpTraceRead r (μ * θ * μ⁻¹) σ := by
  obtain ⟨x, hx⟩ := hout μ θ
  have hμ : μ * θ * μ⁻¹ = MulAut.conj x * θ := by
    rw [hx]
    group
  intro y
  rw [hμ, MulAut.mul_apply, spTrace_conj, h]

theorem outerCommutative_statedProj_statedSp_two {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    OuterCommutative (StatedProj (StatedSp 2 K)) := by
  intro μ θ
  have h := LinearPilot.statedSp_two_outer_comm hK (μ : Outer _) (θ : Outer _)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have h' := (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _).conj_mem _
    (inv_mem h) (θ * μ)
  convert h' using 1
  group

theorem spTraceRead_conj_two {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (μ : MulAut (StatedProj (StatedSp 2 K))) {θ : MulAut (StatedProj (StatedSp 2 K))}
    {σ : K ≃+* K} (h : SpTraceRead 2 θ σ) : SpTraceRead 2 (μ * θ * μ⁻¹) σ :=
  spTraceRead_conj_of_outerCommutative (outerCommutative_statedProj_statedSp_two hK) μ h

theorem card_statedProj_statedSp_lt_succ (r : ℕ) :
    Nat.card (StatedProj (StatedSp r K)) < Nat.card (StatedProj (StatedSp (r + 1) K)) := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
    Finset.prod_Icc_succ_top (by omega)]
  set q := Nat.card K
  set P := ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)
  have hP : 0 < P := Finset.prod_pos fun j hj => by
    have : 2 ≤ q ^ (2 * j) := by
      calc 2 ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (2 * j) := Nat.pow_le_pow_right (by omega) (by simp at hj; omega)
    omega
  have h1 : 2 ≤ q ^ (2 * (r + 1)) - 1 := by
    have : 4 ≤ q ^ (2 * (r + 1)) := by
      calc 4 ≤ q ^ 2 := by nlinarith
        _ ≤ q ^ (2 * (r + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h2 : q ^ (r ^ 2) < q ^ ((r + 1) ^ 2) :=
    Nat.pow_lt_pow_right (by omega) (Nat.pow_lt_pow_left (Nat.lt_succ_self r) (by norm_num))
  calc q ^ (r ^ 2) * P < q ^ ((r + 1) ^ 2) * P := Nat.mul_lt_mul_of_pos_right h2 hP
    _ ≤ q ^ ((r + 1) ^ 2) * (P * (q ^ (2 * (r + 1)) - 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))

theorem rank_eq_of_mulEquiv {r r' : ℕ}
    (e : StatedProj (StatedSp r K) ≃* StatedProj (StatedSp r' K)) : r = r' := by
  have hmono : StrictMono fun r : ℕ => Nat.card (StatedProj (StatedSp r K)) :=
    strictMono_nat_of_lt_succ card_statedProj_statedSp_lt_succ
  exact hmono.injective (Nat.card_congr e.toEquiv)

end CFSG.SeitzReduction.OmegaPilot
