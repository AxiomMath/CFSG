module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54DBCore
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P54F3Spin

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P54.DB

open CFSG Subgroup Matrix Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K]

theorem exists_commutator_eq_neg_one_sl2 {a b : K} (h : a ^ 2 + b ^ 2 = -1) :
    ∃ A B : SL(2, K), ⁅A, B⁆ = -1 := by
  have hA : Matrix.det !![(0 : K), 1; -1, 0] = 1 := by simp [Matrix.det_fin_two]
  have hB : Matrix.det !![a, b; b, -a] = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination -h
  let A : SL(2, K) := ⟨_, hA⟩
  let B : SL(2, K) := ⟨_, hB⟩
  have hA' : (A : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl
  have hB' : (B : Matrix (Fin 2) (Fin 2) K) = !![a, b; b, -a] := rfl
  refine ⟨A, B, ?_⟩
  change A * B * A⁻¹ * B⁻¹ = -1
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hA', hB',
    Matrix.adjugate_fin_two_of, Matrix.mul_fin_two, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination h

theorem sq_add_sq_eq_neg_one_of_card_three [Finite K] (hK : Nat.card K = 3) :
    (1 : K) ^ 2 + 1 ^ 2 = -1 := by
  have := Fintype.ofFinite K
  have h3 : ((Fintype.card K : ℕ) : K) = 0 := FiniteField.cast_card_eq_zero K
  rw [← Nat.card_eq_fintype_card, hK] at h3
  push_cast at h3
  linear_combination h3

theorem la_neg_one_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ₀ : ⇑Q = Q₀) (fr : Frame Q)
    (hAB : ∃ A B : SL(2, K), ⁅A, B⁆ = -1) :
    (toLinEquiv ι K).symm (fr.La (-1)) ∈ StatedOmega Q₀ := by
  obtain ⟨A, B, hAB⟩ := hAB
  rw [statedOmega_eq_comap hQ₀, mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    ← hAB, map_commutatorElement]
  exact commutator_mem_commutator (Frame.La_mem_orthogonalGroup _ A)
    (Frame.La_mem_orthogonalGroup _ B)

section Block

variable {σ : Type} [Fintype σ] [DecidableEq σ] {Q : QuadraticForm K (σ → K)} {m : ℕ}
  (F : HypFrame Q m)

theorem rawF3_of_block [Finite K] (hK3 : Nat.card K = 3) (hQ : Q ≠ 0) [Finite (spinGroup Q)]
    (hker : ∀ x, x ∈ (spinMatrix Q).ker ↔ x = 1 ∨ (x : CliffordAlgebra Q) = -1)
    (hrange : (spinMatrix Q).range = StatedOmega ⇑Q)
    (hrangeE : (spinAction Q).range ≤ elementaryGroup Q)
    (hcen : center (spinGroup Q) ≤ (StatedScalars σ K).comap (spinMatrix Q))
    {i j k i' j' : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hi'j' : i' ≠ j')
    {ι₁ ι₂ : Type} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂] [Nonempty ι₂]
    (e : ι₁ ⊕ ι₂ ≃ σ) {Q₁ : (ι₁ → K) → K} {Q₂ : (ι₂ → K) → K}
    (hQe : pullQ e ⇑Q = sumQ Q₁ Q₂)
    (hu : spinMatrix Q (F.longSL2 hij true true (-1)) = uMat e)
    (hx₀ : spinMatrix Q (F.longSL2 hi'j' true true (-1)) ∈ rblock e Q₁)
    (hBq : IsQuasisimple (StatedOmega Q₁))
    (hneg : (-1 : GL σ K) ∈ StatedOmega ⇑Q → (-1 : GL ι₁ K) ∈ StatedOmega Q₁)
    (hlie : ∃ (τ' : StatedLieTag) (n' : ℕ),
      Blueprint.LieModel (StatedOmega Q₁ ⧸ center (StatedOmega Q₁)) τ' n' 3 1)
    {t : spinGroup Q} (htZ : t ∈ center (spinGroup Q)) (ht1 : t ≠ 1)
    (htn : (t : CliffordAlgebra Q) ≠ -1) : F3.RawF3 (spinGroup Q) t := by
  have hodd : Odd (Nat.card K) := by
    rw [hK3]
    decide
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hZ := DA.smul_of_le_comap hcen
  have hkerc : (spinMatrix Q).ker ≤ center (spinGroup Q) := by
    rw [ker_spinMatrix]
    exact ker_spinAction_le_center Q
  have hB : rblock e Q₁ ≤ (spinMatrix Q).range := by
    rw [hrange]
    exact rblock_le_statedOmega e hQe
  have hBq' : IsQuasisimple (rblock e Q₁) :=
    LocalCores.isQuasisimple_of_mulEquiv (rblockEquiv e).symm hBq
  have hBu : rblock e Q₁ ≤ centralizer {spinMatrix Q (F.longSL2 hij true true (-1))} := by
    rw [hu]
    exact rblock_le_centralizer e
  have hc : ∀ c ∈ centralizer {F.longSL2 hij true true (-1)}, ∀ b ∈ rblock e Q₁,
      spinMatrix Q c * b * (spinMatrix Q c)⁻¹ ∈ rblock e Q₁ := by
    intro c hc b hb
    have hcΩ : spinMatrix Q c ∈ StatedOmega ⇑Q := hrange ▸ MonoidHom.mem_range.mpr ⟨c, rfl⟩
    have hcu : spinMatrix Q c * uMat e = uMat e * spinMatrix Q c := by
      rw [← hu, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hc]
    exact conj_mem_rblock e h2 hQe (statedOmega_le_isoGroup _ hcΩ) hcu hb
  have hJq := isQuasisimple_liftJ hkerc hB hBq'
  obtain ⟨z, hz, hzx⟩ := exists_ker_mul_mem_liftJ hB hBq'.1 hx₀
  obtain ⟨s', hs'⟩ := ker_mul_longSL2 F hQ hker hi'j' hz
  rw [hs'] at hzx
  have hx2 := T1.orderOf_longSL2_neg_one F hi'j' hodd true s'
  have h2J : 2 ∣ Nat.card (liftJ (spinMatrix Q) (rblock e Q₁)) := by
    have h1 := orderOf_dvd_natCard (⟨_, hzx⟩ : liftJ (spinMatrix Q) (rblock e Q₁))
    rwa [Subgroup.orderOf_mk, hx2] at h1
  have hJc := isTwoComponentIn_of_normal_of_even (liftJ_le_centralizer hkerc hBu)
    (normal_liftJ hc) hJq h2J
  have hv₀ : Q (F.vec i true + F.vec i false) = 1 := by
    have h1 := F.polar_vec_not i true
    rw [QuadraticMap.polar, F.map_vec, F.map_vec, sub_zero, sub_zero] at h1
    exact h1
  have hπt := spinMatrix_eq_neg_one hker hcen hv₀ htZ ht1 htn
  have htu : spinMatrix Q (t * F.longSL2 hij true true (-1)) ∈ rblock e Q₁ := by
    rw [map_mul, hπt, hu]
    refine neg_one_mul_uMat_mem_rblock e (hneg ?_)
    rw [← hπt, ← hrange]
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  obtain ⟨z', hz', hz'J⟩ := exists_ker_mul_mem_liftJ hB hBq'.1 htu
  obtain ⟨s, hs⟩ := ker_mul_longSL2 F hQ hker hij hz'
  have htuJ : t * F.longSL2 hij true s (-1) ∈ liftJ (spinMatrix Q) (rblock e Q₁) := by
    rw [← hs, ← mul_assoc, (mem_center_iff.mp (hkerc hz') t), mul_assoc]
    exact hz'J
  have hJl : ∃ (τ' : StatedLieTag) (n' : ℕ), Blueprint.LieModel
      (liftJ (spinMatrix Q) (rblock e Q₁) ⧸ center (liftJ (spinMatrix Q) (rblock e Q₁)))
      τ' n' 3 1 := by
    obtain ⟨τ', n', h⟩ := hlie
    obtain ⟨e₁⟩ := nonempty_liftJ_quotCenter hkerc hB hBq'.1
    have e₂ : rblock e Q₁ ⧸ center (rblock e Q₁) ≃*
        StatedOmega Q₁ ⧸ center (StatedOmega Q₁) :=
      QuotientGroup.congr _ _ (rblockEquiv e) (Subgroup.map_center_eq _)
    exact ⟨τ', n', LieType.CurtisTits.lieModel_of_mulEquiv (e₁.trans e₂).symm h⟩
  have huZ := DA.longSL2_neg_one_not_mem_center F hodd hZ hij hki hkj true s
  have hJc' : IsTwoComponentIn (liftJ (spinMatrix Q) (rblock e Q₁))
      (centralizer {F.longSL2 hij true s (-1)}) := by
    rw [centralizer_longSL2_neg_one F hQ hij s]
    exact hJc
  obtain ⟨eK⟩ := F3.nonempty_sl2_equiv_zmod_three hK3
  exact ⟨F.longSL2 hij true s (-1), T1.orderOf_longSL2_neg_one F hij hodd true s, huZ,
    (F.longSL2 hij true s).range, _, T1.range_longSL2_le_centralizer F hij true s,
    F3.isSubnormal_range_longSL2_of_odd F hij hodd hrangeE true s,
    MonoidHom.mem_range.mpr ⟨-1, rfl⟩, F3.range_longSL2_inf_center F hij true s huZ,
    ⟨(MonoidHom.ofInjective (T1.longSL2_injective F hij true s)).symm.trans eK⟩,
    .inl ⟨hJc', hJq, hJl⟩, .inr htuJ⟩

end Block

end CFSG.ComponentClassification.HarrisLit.T1.P54.DB
