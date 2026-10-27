module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.LieType.HighestRoot

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

theorem hypFrame_vec_ne_zero (F₀ : HypFrame Q m) (i : Fin m) (s : Bool) : F₀.vec i s ≠ 0 := by
  intro h
  have := F₀.polar_vec_not i s
  rw [h, polar_zero_left] at this
  exact zero_ne_one this

theorem coe_ne_neg_coe (h2 : (2 : K) ≠ 0) (x : spinGroup Q) :
    (x : CliffordAlgebra Q) ≠ -(x : CliffordAlgebra Q) := by
  intro h
  have h0 : (2 : K) • (x : CliffordAlgebra Q) = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel _
  have hx0 : (x : CliffordAlgebra Q) = 0 := (smul_eq_zero.mp h0).resolve_left h2
  have h1 := coe_mul_coe_inv Q x
  rw [hx0, zero_mul] at h1
  exact zero_ne_one h1

theorem mul_self_eq_of_spinAction_eq [FiniteDimensional K V] [Invertible (2 : K)] [Nontrivial V]
    (hQ : Q.Nondegenerate) {x y : spinGroup Q} (h : spinAction Q x = spinAction Q y) :
    x * x = y * y := by
  have hk : x * y⁻¹ ∈ (spinAction Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hc := Subgroup.mem_center_iff.mp (ker_spinAction_le_center Q hk)
  have hsq : (x * y⁻¹) * (x * y⁻¹) = 1 := by
    rcases (mem_ker_spinAction_iff Q hQ _).mp hk with h1 | h1
    · rw [h1, one_mul]
    · rw [h1, spinGroup.negOne_mul_self]
  calc x * x = (x * y⁻¹) * (y * (x * y⁻¹)) * y := by group
    _ = (x * y⁻¹) * ((x * y⁻¹) * y) * y := by rw [hc y]
    _ = (x * y⁻¹) * (x * y⁻¹) * (y * y) := by group
    _ = y * y := by rw [hsq, one_mul]

variable (F₀ : HypFrame Q m) {i j : Fin m} (hij : i ≠ j) (s t : Bool)

theorem spinAction_longSL2 (M : SL(2, K)) :
    spinAction Q (F₀.longSL2 hij s t M) = (F₀.toFrame hij s t).La M :=
  DFunLike.congr_fun (spinAction_comp_longSL2 F₀ hij s t) M

theorem longSL2_injective : Function.Injective (F₀.longSL2 hij s t) := fun M N h =>
  (F₀.toFrame hij s t).La_injective (by rw [← spinAction_longSL2, ← spinAction_longSL2, h])

theorem nonempty_mulEquiv_range_longSL2 :
    Nonempty ((F₀.longSL2 hij s t).range ≃* SL(2, K)) :=
  ⟨(MonoidHom.ofInjective (longSL2_injective F₀ hij s t)).symm⟩

theorem toFrame_not : F₀.toFrame hij s (!t) = (F₀.toFrame hij s t).swap := by
  cases t <;> rfl

theorem longPair_sum_eq_one :
    (F₀.longPair hij s t).X * (F₀.longPair hij s t).Y +
        (F₀.longPair hij s t).Y * (F₀.longPair hij s t).X +
      ((F₀.longPair hij s (!t)).X * (F₀.longPair hij s (!t)).Y +
        (F₀.longPair hij s (!t)).Y * (F₀.longPair hij s (!t)).X) = 1 := by
  simp only [HypFrame.longPair, Bool.not_not]
  have hcd_a := ι_mul_ι_mul_ι_comm Q (F₀.polar_vec_of_ne hij s t) (F₀.polar_vec_of_ne hij s (!t))
  have hdc_a := ι_mul_ι_mul_ι_comm Q (F₀.polar_vec_of_ne hij s (!t)) (F₀.polar_vec_of_ne hij s t)
  have hba_c := ι_mul_ι_mul_ι_comm Q (F₀.polar_vec_of_ne hij.symm t (!s))
    (F₀.polar_vec_of_ne hij.symm t s)
  have hba_d := ι_mul_ι_mul_ι_comm Q (F₀.polar_vec_of_ne hij.symm (!t) (!s))
    (F₀.polar_vec_of_ne hij.symm (!t) s)
  have hab := ι_mul_ι_add_ι_mul_ι_eq_one Q (F₀.polar_vec_not i s)
  have hcd := ι_mul_ι_add_ι_mul_ι_eq_one Q (F₀.polar_vec_not j t)
  set a := ι Q (F₀.vec i s)
  set b := ι Q (F₀.vec i (!s))
  set c := ι Q (F₀.vec j t)
  set d := ι Q (F₀.vec j (!t))
  have e1 : a * c * (d * b) = c * d * (a * b) := by
    rw [show a * c * (d * b) = a * (c * d) * b by noncomm_ring, hcd_a]
    noncomm_ring
  have e2 : d * b * (a * c) = d * c * (b * a) := by
    rw [show d * b * (a * c) = d * (b * a * c) by noncomm_ring, ← hba_c]
    noncomm_ring
  have e3 : a * d * (c * b) = d * c * (a * b) := by
    rw [show a * d * (c * b) = a * (d * c) * b by noncomm_ring, hdc_a]
    noncomm_ring
  have e4 : c * b * (a * d) = c * d * (b * a) := by
    rw [show c * b * (a * d) = c * (b * a * d) by noncomm_ring, ← hba_d]
    noncomm_ring
  rw [e1, e2, e3, e4]
  calc c * d * (a * b) + d * c * (b * a) + (d * c * (a * b) + c * d * (b * a)) =
      (c * d + d * c) * (a * b + b * a) := by noncomm_ring
    _ = 1 := by rw [hab, hcd, one_mul]

theorem coe_longSL2_neg_one :
    (F₀.longSL2 hij s t (-1) : CliffordAlgebra Q) =
      1 - (2 : K) • ((F₀.longPair hij s t).X * (F₀.longPair hij s t).Y +
        (F₀.longPair hij s t).Y * (F₀.longPair hij s t).X) := by
  rw [HypFrame.coe_longSL2, SL2Pair.toFun]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), neg_zero, zero_smul, add_zero]
  module

theorem coe_longSL2_not_neg_one :
    (F₀.longSL2 hij s (!t) (-1) : CliffordAlgebra Q) =
      -(F₀.longSL2 hij s t (-1) : CliffordAlgebra Q) := by
  have h := longPair_sum_eq_one F₀ hij s t
  rw [coe_longSL2_neg_one, coe_longSL2_neg_one, eq_sub_of_add_eq' h]
  module

theorem centralizer_longSL2_not_neg_one :
    Subgroup.centralizer ({F₀.longSL2 hij s (!t) (-1)} : Set (spinGroup Q)) =
      Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)) := by
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← Subtype.coe_inj, ← Subtype.coe_inj, Submonoid.coe_mul, Submonoid.coe_mul,
    Submonoid.coe_mul, Submonoid.coe_mul, coe_longSL2_not_neg_one, mul_neg, neg_mul, neg_inj]

theorem orderOf_longSL2_neg_one (h2 : (2 : K) ≠ 0) : orderOf (F₀.longSL2 hij s t (-1)) = 2 := by
  rw [orderOf_injective _ (longSL2_injective F₀ hij s t)]
  exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf K h2

theorem eq_of_mem_range_longSL2_of_orderOf_eq_two (h2 : (2 : K) ≠ 0) {z : spinGroup Q}
    (hz : z ∈ (F₀.longSL2 hij s t).range) (hz2 : orderOf z = 2) :
    z = F₀.longSL2 hij s t (-1) := by
  obtain ⟨M, rfl⟩ := hz
  rw [orderOf_injective _ (longSL2_injective F₀ hij s t)] at hz2
  rw [(CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff K h2 M).mp hz2]
  rfl

theorem conj_mem_range_longSL2 [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (hQ : Q.Nondegenerate)
    {c : spinGroup Q}
    (hc : c ∈ Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)))
    {x : spinGroup Q} (hx : x ∈ (F₀.longSL2 hij s t).range) :
    c * x * c⁻¹ ∈ (F₀.longSL2 hij s t).range := by
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have : Nontrivial V := ⟨⟨F₀.vec i s, 0, hypFrame_vec_ne_zero F₀ i s⟩⟩
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hgO : spinAction Q c ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction Q c)
  have hg : spinAction Q c * (F₀.toFrame hij s t).La (-1) =
      (F₀.toFrame hij s t).La (-1) * spinAction Q c := by
    rw [← spinAction_longSL2, ← map_mul, ← map_mul, hc']
  have hsq : ∀ y : spinGroup Q, spinAction Q y ∈ (F₀.toFrame hij s t).La.range →
      y * y ∈ (F₀.longSL2 hij s t).range := by
    rintro y ⟨N, hN⟩
    rw [mul_self_eq_of_spinAction_eq hQ (y := F₀.longSL2 hij s t N)
      (by rw [spinAction_longSL2, hN]), ← map_mul]
    exact ⟨_, rfl⟩
  have hconj : ∀ M : SL(2, K), spinAction Q (c * F₀.longSL2 hij s t M * c⁻¹) =
      spinAction Q c * (F₀.toFrame hij s t).La M * (spinAction Q c)⁻¹ := fun M => by
    rw [map_mul, map_mul, map_inv, spinAction_longSL2]
  rcases Frame.conjSubgroup_La_range h2 hgO hg with ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  ·
    have hmem : ∀ M : SL(2, K), spinAction Q (c * F₀.longSL2 hij s t M * c⁻¹) ∈
        (F₀.toFrame hij s t).La.range := fun M => by
      rw [hconj, ← h1, mem_conjSubgroup]
      exact ⟨M, by group⟩
    have hhalf : ∀ U : SL(2, K), (MulAut.conj c).toMonoidHom.comp (F₀.longSL2 hij s t) (U * U) =
        (c * F₀.longSL2 hij s t U * c⁻¹) * (c * F₀.longSL2 hij s t U * c⁻¹) := fun U => by
      simp only [MonoidHom.comp_apply, map_mul, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨M, rfl⟩ := hx
    refine Frame.sl2_apply_mem ((MulAut.conj c).toMonoidHom.comp (F₀.longSL2 hij s t)) _
      (fun a => ?_) (fun a => ?_) M
    · rw [← coe_upperSL2_eq_transvection,
        show upperSL2 a = upperSL2 (a / 2) * upperSL2 (a / 2) by rw [← upperSL2_add, add_halves],
        hhalf]
      exact hsq _ (hmem _)
    · rw [← coe_lowerSL2_eq_transvection,
        show lowerSL2 a = lowerSL2 (a / 2) * lowerSL2 (a / 2) by rw [← lowerSL2_add, add_halves],
        hhalf]
      exact hsq _ (hmem _)
  ·
    exfalso
    have hw : weylSL2 (1 : Kˣ) * weylSL2 1 = -1 := by
      rw [weylSL2_one_mul_self]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [coe_diagSL2]
    have hmem : spinAction Q (c * F₀.longSL2 hij s t (weylSL2 1) * c⁻¹) ∈
        (F₀.toFrame hij s (!t)).La.range := by
      rw [toFrame_not, ← h1, hconj, mem_conjSubgroup]
      exact ⟨weylSL2 1, by group⟩
    obtain ⟨N, hN⟩ := hmem
    have hsq' := mul_self_eq_of_spinAction_eq hQ (x := c * F₀.longSL2 hij s t (weylSL2 1) * c⁻¹)
      (y := F₀.longSL2 hij s (!t) N) (by rw [spinAction_longSL2, hN])
    have hl : (c * F₀.longSL2 hij s t (weylSL2 1) * c⁻¹) *
        (c * F₀.longSL2 hij s t (weylSL2 1) * c⁻¹) = F₀.longSL2 hij s t (-1) := by
      calc _ = c * F₀.longSL2 hij s t (weylSL2 1 * weylSL2 1) * c⁻¹ := by rw [map_mul]; group
        _ = F₀.longSL2 hij s t (-1) := by rw [hw, hc']; group
    rw [hl, ← map_mul] at hsq'
    have hNN : N * N = -1 := (F₀.toFrame hij s (!t)).La_injective (by
      rw [← spinAction_longSL2, ← hsq', spinAction_longSL2, toFrame_not, Frame.La_swap_neg_one])
    rw [hNN] at hsq'
    exact coe_ne_neg_coe h2 _
      ((congrArg Subtype.val hsq').trans (coe_longSL2_not_neg_one F₀ hij s t))

theorem centralizer_le_normalizer_longSL2 [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : Q.Nondegenerate) :
    Subgroup.centralizer ({F₀.longSL2 hij s t (-1)} : Set (spinGroup Q)) ≤
      Subgroup.normalizer ((F₀.longSL2 hij s t).range : Set (spinGroup Q)) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_range_longSL2 F₀ hij s t h2 hQ hc hx, fun hx => ?_⟩
  have := conj_mem_range_longSL2 F₀ hij s t h2 hQ (inv_mem hc) hx
  rwa [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at this

end CFSG.LieType.HighestRoot
