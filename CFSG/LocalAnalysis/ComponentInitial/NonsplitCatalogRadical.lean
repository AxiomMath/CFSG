module

public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalTorusMaps
public import CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthogonalTail NormTail
open scoped commutatorElement

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (T : NormTailData K F) {r : ℕ}

section Diag

theorem psi_eq_dMap (A : SpecialLinearGroup (Fin r) K) :
    psi F r A = dMap (SpecialLinearGroup.toGL A) (1 : F ≃ₗ[K] F) := by
  refine LinearEquiv.ext fun v => ?_
  rw [psi_apply, dMap_apply]
  rfl

theorem torusMap_eq_dMap (a : Fin r → Kˣ) :
    torusMap F a 1 = dMap (OrthogonalSplit.diagGL a) (1 : F ≃ₗ[K] F) := by
  refine LinearEquiv.ext fun v => Prod.ext (funext fun c => ?_) ?_
  · rw [torusMap_apply, dMap_apply]
    have hinv : (((OrthogonalSplit.diagGL a)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) =
        diagonal fun i => (((a i)⁻¹ : Kˣ) : K) := rfl
    rcases c with i | i
    · change torusScal a (.inl i) * v.1 (.inl i) =
        (diagonal (fun i => (a i : K)) *ᵥ (v.1 ∘ Sum.inl)) i
      rw [mulVec_diagonal]
      rfl
    · change torusScal a (.inr i) * v.1 (.inr i) =
        ((((OrthogonalSplit.diagGL a)⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)ᵀ *ᵥ
          (v.1 ∘ Sum.inr)) i
      rw [hinv, diagonal_transpose, mulVec_diagonal]
      rfl
  · rw [torusMap_apply, dMap_apply, Units.val_one, one_mul]
    rfl

end Diag

section Radical

variable (r) in
@[expose] def radN : Subgroup (G0 T r) where
  carrier := {g | ∃ (L : Fin r → F) (C : Matrix (Fin r) (Fin r) K), Cᵀ = -C ∧
    (∀ i, C i i = 0) ∧ g.1 = uMap (normForm T) L C}
  mul_mem' := by
    rintro _ _ ⟨L, C, hC, hd, hg⟩ ⟨L', C', hC', hd', hg'⟩
    obtain ⟨hC'', hd''⟩ := mulParam_alternating (qA := normForm T) L L' hC hd hC' hd'
    exact ⟨L + L', _, hC'', hd'', by rw [Subgroup.coe_mul, hg, hg', uMap_mul_uMap]⟩
  one_mem' := ⟨0, 0, by simp, fun _ => rfl, by rw [OneMemClass.coe_one, uMap_zero_zero]⟩
  inv_mem' := by
    rintro _ ⟨L, C, hC, hd, hg⟩
    obtain ⟨hC0, hd0⟩ := mulParam_alternating (qA := normForm T) L (-L) hC hd
      (C' := 0) (by simp) (fun _ => rfl)
    refine ⟨-L, -mulParam (normForm T) L (-L) C 0, by rw [transpose_neg, hC0],
      fun i => by rw [Matrix.neg_apply, hd0, neg_zero], ?_⟩
    rw [Subgroup.coe_inv, hg, inv_eq_iff_mul_eq_one, uMap_mul_uMap, add_neg_cancel]
    have h0 : mulParam (normForm T) L (-L) C (-mulParam (normForm T) L (-L) C 0) = 0 := by
      simp only [mulParam]
      abel
    rw [h0, uMap_zero_zero]

theorem mk_mem_radN (L : Fin r → F) {C : Matrix (Fin r) (Fin r) K} (hC : Cᵀ = -C)
    (hd : ∀ i, C i i = 0) :
    (⟨uMap (normForm T) L C, NonsplitOrthogonalCover.uMap_mem_orthElementaryGroup L hC hd⟩ :
      G0 T r) ∈ radN T r :=
  ⟨L, C, hC, hd, rfl⟩

variable (r) in
@[expose] def radCoord (g : G0 T r) : Fin r → F :=
  fun j => (g.1 (hypVec K F (.inr j))).2

theorem radCoord_eq {g : G0 T r} {L : Fin r → F} {C : Matrix (Fin r) (Fin r) K}
    (hg : g.1 = uMap (normForm T) L C) : radCoord T r g = L := by
  funext j
  rw [radCoord, hg]
  exact NonsplitOrthogonalCover.uMap_hypVec_inr_snd L C j

theorem radCoord_mul {m n : G0 T r} (hm : m ∈ radN T r) (hn : n ∈ radN T r) :
    radCoord T r (m * n) = radCoord T r m + radCoord T r n := by
  obtain ⟨L, C, -, -, hmL⟩ := hm
  obtain ⟨L', C', -, -, hnL⟩ := hn
  rw [radCoord_eq T hmL, radCoord_eq T hnL,
    radCoord_eq T (by rw [Subgroup.coe_mul, hmL, hnL, uMap_mul_uMap])]

theorem radCoord_one : radCoord T r 1 = 0 :=
  radCoord_eq T (g := 1) (L := 0) (C := 0) (by rw [OneMemClass.coe_one, uMap_zero_zero])

theorem radCoord_inv {n : G0 T r} (hn : n ∈ radN T r) : radCoord T r n⁻¹ = -radCoord T r n := by
  have h := radCoord_mul T hn (inv_mem hn)
  rw [mul_inv_cancel, radCoord_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem exists_radCoord (L : Fin r → F) : ∃ n ∈ radN T r, radCoord T r n = L :=
  ⟨_, mk_mem_radN T L (C := 0) (by simp) fun _ => rfl, radCoord_eq T rfl⟩

variable (r) in
@[expose] def radTau : Multiplicative (OrthogonalSplit.altSubgroup r K) →* G0 T r where
  toFun B := ⟨uMap (normForm T) 0 (B.toAdd : Matrix (Fin r) (Fin r) K),
    NonsplitOrthogonalCover.uMap_mem_orthElementaryGroup 0 B.toAdd.2.1 B.toAdd.2.2⟩
  map_one' := Subtype.ext (by
    change uMap (normForm T) 0 (0 : Matrix (Fin r) (Fin r) K) = 1
    rw [uMap_zero_zero])
  map_mul' B B' := Subtype.ext (by
    change uMap (normForm T) 0 (((B.toAdd + B'.toAdd : OrthogonalSplit.altSubgroup r K)) :
      Matrix (Fin r) (Fin r) K) = uMap (normForm T) 0 _ * uMap (normForm T) 0 _
    rw [NonsplitOrthogonalCover.uMap_zero_mul_uMap_zero, AddSubgroup.coe_add])

theorem coe_radTau (B : Multiplicative (OrthogonalSplit.altSubgroup r K)) :
    (radTau T r B).1 = uMap (normForm T) 0 (B.toAdd : Matrix (Fin r) (Fin r) K) :=
  rfl

theorem radTau_mem (B : Multiplicative (OrthogonalSplit.altSubgroup r K)) :
    radTau T r B ∈ radN T r :=
  ⟨0, _, B.toAdd.2.1, B.toAdd.2.2, rfl⟩

theorem range_radTau_le : (radTau T r).range ≤ radN T r := by
  rintro _ ⟨B, rfl⟩
  exact radTau_mem T B

theorem radCoord_eq_zero_iff {n : G0 T r} (hn : n ∈ radN T r) :
    radCoord T r n = 0 ↔ n ∈ (radTau T r).range := by
  obtain ⟨L, C, hC, hd, hnL⟩ := hn
  rw [radCoord_eq T hnL]
  constructor
  · rintro rfl
    exact ⟨Multiplicative.ofAdd ⟨C, hC, hd⟩, Subtype.ext (by rw [coe_radTau, hnL]; rfl)⟩
  · rintro ⟨B, hB⟩
    rw [← hB, coe_radTau] at hnL
    exact (NonsplitOrthogonalCover.uMap_injective hnL).1.symm

theorem commutatorElement_mem_range_radTau {m n : G0 T r} (hm : m ∈ radN T r)
    (hn : n ∈ radN T r) : ⁅m, n⁆ ∈ (radTau T r).range := by
  obtain ⟨L, C, -, -, hmL⟩ := hm
  obtain ⟨L', C', -, -, hnL⟩ := hn
  set M := crossMat (normForm T) L' L - crossMat (normForm T) L L' with hM
  have hMalt : M ∈ OrthogonalSplit.altSubgroup r K := by
    refine ⟨Matrix.ext fun i j => ?_, fun i => ?_⟩
    · simp only [hM, transpose_apply, Matrix.sub_apply, Matrix.neg_apply, crossMat, of_apply]
      rw [polar_comm _ (L' j), polar_comm _ (L j)]
      abel
    · simp only [hM, Matrix.sub_apply, crossMat, of_apply]
      rw [polar_comm, sub_self]
  refine ⟨Multiplicative.ofAdd ⟨M, hMalt⟩, Subtype.ext ?_⟩
  rw [coe_radTau]
  change uMap (normForm T) 0 M = (m * n * m⁻¹ * n⁻¹).1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
    hmL, hnL, ← commutatorElement_def, NonsplitOrthogonalCover.commutatorElement_uMap]

theorem radTau_mul_comm (B : Multiplicative (OrthogonalSplit.altSubgroup r K)) {n : G0 T r}
    (hn : n ∈ radN T r) : radTau T r B * n = n * radTau T r B := by
  obtain ⟨L, C, -, -, hnL⟩ := hn
  have h : ⁅radTau T r B, n⁆ = 1 := by
    apply Subtype.ext
    have h0 : crossMat (normForm T) L (0 : Fin r → F) - crossMat (normForm T) 0 L = 0 := by
      ext i j
      simp [crossMat]
    change (radTau T r B * n * (radTau T r B)⁻¹ * n⁻¹).1 = 1
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv, coe_radTau, hnL, ← commutatorElement_def,
      NonsplitOrthogonalCover.commutatorElement_uMap, h0, uMap_zero_zero]
  exact commutatorElement_eq_one_iff_mul_comm.mp h

end Radical

section Roots

theorem upperSL_mul (z w : F) : upperSL F z * upperSL F w = upperSL F (z + w) :=
  Matrix.SpecialLinearGroup.ext _ _ fun a b => by
    change ((upperSL F z : Matrix (Fin 2) (Fin 2) F) *
      (upperSL F w : Matrix (Fin 2) (Fin 2) F)) a b = (upperSL F (z + w) : Matrix _ _ F) a b
    rw [coe_upperSL, coe_upperSL, coe_upperSL, Matrix.mul_fin_two]
    fin_cases a <;> fin_cases b <;> simp [add_comm]

variable [CharP K 2]

@[expose] def xRt (k : Fin r) (z : F) : G0 T r :=
  rhoG T k (upperSL F z)

theorem coe_xRt (k : Fin r) (z : F) : (xRt T k z).1 = uMap (normForm T) (Pi.single k z) 0 := by
  rw [xRt, coe_rhoG, rho_upperSL, eichler_inl_tail_eq_uMap]

theorem xRt_add (k : Fin r) (z w : F) : xRt T k (z + w) = xRt T k z * xRt T k w := by
  rw [xRt, xRt, xRt, ← map_mul, upperSL_mul]

theorem xRt_mem_radN (k : Fin r) (z : F) : xRt T k z ∈ radN T r :=
  ⟨Pi.single k z, 0, by simp, fun _ => rfl, coe_xRt T k z⟩

omit [CharP K 2] in
@[expose] def zRt (i j : Fin r) (a : K) : G0 T r :=
  radTau T r (Multiplicative.ofAdd ⟨a • OrthogonalSplit.altUnit i j,
    OrthogonalSplit.smul_altUnit_mem_altSubgroup i j a⟩)

omit [CharP K 2] in
theorem coe_zRt (i j : Fin r) (a : K) :
    (zRt T i j a).1 = uMap (normForm T) 0 (a • OrthogonalSplit.altUnit i j) :=
  rfl

omit [CharP K 2] in
theorem zRt_add (i j : Fin r) (a b : K) : zRt T i j (a + b) = zRt T i j a * zRt T i j b := by
  rw [zRt, zRt, zRt, ← map_mul, ← ofAdd_add]
  congr 2
  exact Subtype.ext (add_smul a b _)

theorem commutatorElement_xRt {i j : Fin r} (hij : i ≠ j) (z w : F) :
    ⁅xRt T i z, xRt T j w⁆ = zRt T i j (-polar (normForm T) z w) := by
  apply Subtype.ext
  change (xRt T i z * xRt T j w * (xRt T i z)⁻¹ * (xRt T j w)⁻¹).1 = _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
    coe_xRt, coe_xRt, ← commutatorElement_def, NonsplitOrthogonalCover.commutatorElement_uMap,
    coe_zRt]
  congr 1
  ext p q
  simp only [crossMat, of_apply, Matrix.sub_apply, Matrix.smul_apply, OrthogonalSplit.altUnit,
    Matrix.single_apply, Pi.single_apply, smul_eq_mul]
  rcases eq_or_ne p i with rfl | hpi
  · rcases eq_or_ne q j with rfl | hqj
    · simp [hij, Ne.symm hij]
    · simp [hij, Ne.symm hij, hqj, Ne.symm hqj]
  · rcases eq_or_ne p j with rfl | hpj
    · rcases eq_or_ne q i with rfl | hqi
      · simp [hij, Ne.symm hij, polar_comm]
      · simp [hpi, Ne.symm hpi, hqi, Ne.symm hqi]
    · simp [hpi, Ne.symm hpi, hpj, Ne.symm hpj]

theorem xRt_commute (k : Fin r) (z w : F) : Commute (xRt T k z) (xRt T k w) := by
  rw [Commute, SemiconjBy, ← xRt_add, ← xRt_add, add_comm]

end Roots

section Generation

theorem range_radTau_le_closure :
    (radTau T r).range ≤ Subgroup.closure {g | ∃ i j a, i < j ∧ zRt T i j a = g} := by
  rintro _ ⟨B, rfl⟩
  set S := Finset.univ.filter fun p : Fin r × Fin r => p.1 < p.2
  have hB : B = ∏ p ∈ S, Multiplicative.ofAdd
      (⟨(B.toAdd : Matrix (Fin r) (Fin r) K) p.1 p.2 • OrthogonalSplit.altUnit p.1 p.2,
        OrthogonalSplit.smul_altUnit_mem_altSubgroup p.1 p.2 _⟩ :
          OrthogonalSplit.altSubgroup r K) := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rw [toAdd_prod, AddSubgroup.val_finsetSum]
    exact OrthogonalSplit.eq_sum_of_alternating B.toAdd.2.1 B.toAdd.2.2
  have hmem : B ∈ (Subgroup.closure {g | ∃ i j a, i < j ∧ zRt T i j a = g}).comap
      (radTau T r) := by
    rw [hB]
    exact Subgroup.prod_mem _ fun p hp => Subgroup.subset_closure
      ⟨p.1, p.2, _, (Finset.mem_filter.1 hp).2, rfl⟩
  exact hmem

variable [CharP K 2]

theorem radN_le_closure (hF : Module.finrank K F = 2) :
    radN T r ≤ Subgroup.closure {g | ∃ k z, xRt T k z = g} := by
  set H := Subgroup.closure {g | ∃ k z, xRt T k z = g} with hH
  have hx : ∀ k z, xRt T k z ∈ H := fun k z => Subgroup.subset_closure ⟨k, z, rfl⟩
  have hpol : ∀ a : K, ∃ z w : F, -polar (normForm T) z w = a := by
    intro a
    obtain ⟨z, hz⟩ : ∃ z : F, z ≠ 0 := exists_ne 0
    have hnd := nondegenerate_polarBilin_normForm T hF
    obtain ⟨w, hw⟩ : ∃ w, polar (normForm T) z w ≠ 0 := by
      by_contra! h
      exact hz (hnd.1 z fun w => by rw [polarBilin_apply_apply]; exact h w)
    refine ⟨z, (-a / polar (normForm T) z w) • w, ?_⟩
    rw [polar_smul_right, smul_eq_mul, div_mul_cancel₀ _ hw, neg_neg]
  have hV : (radTau T r).range ≤ H := by
    refine (range_radTau_le_closure T).trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨i, j, a, hij, rfl⟩
    obtain ⟨z, w, hzw⟩ := hpol a
    rw [← hzw, ← commutatorElement_xRt T hij.ne]
    exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator (hx i z) (hx j w))
  let S : AddSubmonoid (Fin r → F) :=
    { carrier := {L | ∃ (C : Matrix (Fin r) (Fin r) K) (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0),
        (⟨uMap (normForm T) L C, NonsplitOrthogonalCover.uMap_mem_orthElementaryGroup L hC hd⟩ :
          G0 T r) ∈ H}
      zero_mem' := ⟨0, by simp, fun _ => rfl, by
        convert H.one_mem using 1
        exact Subtype.ext uMap_zero_zero⟩
      add_mem' := by
        rintro L L' ⟨C, hC, hd, hL⟩ ⟨C', hC', hd', hL'⟩
        obtain ⟨hC'', hd''⟩ := mulParam_alternating (qA := normForm T) L L' hC hd hC' hd'
        refine ⟨_, hC'', hd'', ?_⟩
        convert H.mul_mem hL hL' using 1
        exact Subtype.ext (uMap_mul_uMap L L' C C').symm }
  have hS : ∀ L, L ∈ S := by
    intro L
    rw [← Finset.univ_sum_single L]
    refine AddSubmonoid.sum_mem _ fun k _ => ⟨0, by simp, fun _ => rfl, ?_⟩
    convert hx k (L k) using 1
    exact Subtype.ext (coe_xRt T k (L k)).symm
  rintro g ⟨L, C, hC, hd, hg⟩
  obtain ⟨C₀, hC₀, hd₀, hL⟩ := hS L
  have hCC : (C - C₀)ᵀ = -(C - C₀) := by rw [transpose_sub, hC, hC₀]; abel
  have hdd : ∀ i, (C - C₀) i i = 0 := fun i => by rw [Matrix.sub_apply, hd, hd₀, sub_zero]
  have hv : radTau T r (Multiplicative.ofAdd ⟨C - C₀, hCC, hdd⟩) ∈ H := hV ⟨_, rfl⟩
  convert H.mul_mem hL hv using 1
  apply Subtype.ext
  rw [hg, Subgroup.coe_mul, coe_radTau]
  change uMap (normForm T) L C = uMap (normForm T) L C₀ * uMap (normForm T) 0 (C - C₀)
  rw [uMap_mul_uMap, add_zero]
  congr 1
  have h0 : crossMat (normForm T) L (0 : Fin r → F) = 0 := by
    ext i j
    simp [crossMat]
  simp only [mulParam, sMat_zero, h0, add_zero, sub_zero]
  abel

end Generation

section Torus

theorem conjL_diagGL (a : Fin r → Kˣ) (L : Fin r → F) :
    conjL (OrthogonalSplit.diagGL a) (1 : F ≃ₗ[K] F) L = fun j => (a j : K) • L j := by
  funext j
  change (1 : F ≃ₗ[K] F) (∑ i, (diagonal (fun i => (a i : K))) j i • L i) = _
  rw [LinearEquiv.coe_one, id, Finset.sum_eq_single j (fun i _ hij => by
    rw [diagonal_apply_ne _ (Ne.symm hij), zero_smul]) (by simp), diagonal_apply_eq]

theorem sMat_smul (a : Fin r → Kˣ) (L : Fin r → F) :
    sMat (normForm T) (fun j => (a j : K) • L j) =
      diagonal (fun i => (a i : K)) * sMat (normForm T) L * diagonal (fun i => (a i : K)) := by
  ext p q
  rw [mul_diagonal, diagonal_mul]
  simp only [sMat, of_apply]
  by_cases hpq : p = q
  · subst hpq
    simp only [↓reduceIte, QuadraticMap.map_smul, smul_eq_mul]
    ring
  · by_cases hlt : p < q
    · simp only [hpq, hlt, ↓reduceIte, polar_smul_left, polar_smul_right, smul_eq_mul]
      ring
    · simp only [hpq, hlt, ↓reduceIte, mul_zero, zero_mul]

theorem torusMap_conj_uMap (a : Fin r → Kˣ) (L : Fin r → F) (C : Matrix (Fin r) (Fin r) K) :
    torusMap F a 1 * uMap (normForm T) L C * (torusMap F a 1)⁻¹ =
      uMap (normForm T) (fun j => (a j : K) • L j)
        (diagonal (fun i => (a i : K)) * C * diagonal (fun i => (a i : K))) := by
  rw [torusMap_eq_dMap, dMap_conj_uMap (one_mem _), conjL_diagGL]
  congr 1
  rw [conjC, conjL_diagGL, sMat_smul]
  change diagonal (fun i => (a i : K)) * (sMat (normForm T) L + C) *
      (diagonal (fun i => (a i : K)))ᵀ - _ = _
  rw [diagonal_transpose, Matrix.mul_add, Matrix.add_mul]
  abel

variable [CharP K 2] [Finite K]

theorem torusMap_mem (a : Fin r → Kˣ) :
    torusMap F a 1 ∈ orthElementaryGroup (quadTail r (normForm T)) := by
  set φ : (Fin r → Kˣ) →* ((Fin r ⊕ Fin r → K) × F) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × F) :=
    (torusHom F r).comp (MonoidHom.inl _ _) with hφ
  have hsingle : ∀ i (b : Kˣ),
      Pi.mulSingle i b ∈ (orthElementaryGroup (quadTail r (normForm T))).comap φ := by
    intro i b
    have h := rho_diagSL_eq_torusMap T i (Units.map (algebraMap K F : K →* F) (sqrtHom K b))
    rw [normUnits_algebraMap, sqrtHom_sq, barQuot_algebraMap] at h
    change torusMap F (Pi.mulSingle i b) 1 ∈ orthElementaryGroup (quadTail r (normForm T))
    rw [← h]
    exact rho_mem T i _
  have hmem : a ∈ (orthElementaryGroup (quadTail r (normForm T))).comap φ := by
    rw [← Finset.univ_prod_mulSingle a]
    exact Subgroup.prod_mem _ fun i _ => hsingle i (a i)
  exact hmem

variable (r) in
@[expose] def torusE : (Fin r → Kˣ) →* G0 T r :=
  ((torusHom F r).comp (MonoidHom.inl _ _)).codRestrict _ (torusMap_mem T)

theorem coe_torusE (a : Fin r → Kˣ) : (torusE T r a).1 = torusMap F a 1 :=
  rfl

theorem torusE_commute (a b : Fin r → Kˣ) : Commute (torusE T r a) (torusE T r b) :=
  (Commute.all a b).map _

theorem torusE_conj_mem_radN (a : Fin r → Kˣ) {g : G0 T r} (hg : g ∈ radN T r) :
    torusE T r a * g * (torusE T r a)⁻¹ ∈ radN T r ∧
      radCoord T r (torusE T r a * g * (torusE T r a)⁻¹) =
        fun j => (a j : K) • radCoord T r g j := by
  obtain ⟨L, C, hC, hd, hgL⟩ := hg
  have hcoe : (torusE T r a * g * (torusE T r a)⁻¹).1 = uMap (normForm T)
      (fun j => (a j : K) • L j)
        (diagonal (fun i => (a i : K)) * C * diagonal (fun i => (a i : K))) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, hgL,
      torusMap_conj_uMap]
  have hC' : (diagonal (fun i => (a i : K)) * C * diagonal (fun i => (a i : K)))ᵀ =
      -(diagonal (fun i => (a i : K)) * C * diagonal (fun i => (a i : K))) := by
    rw [transpose_mul, transpose_mul, diagonal_transpose, hC, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc]
  have hd' : ∀ i, (diagonal (fun i => (a i : K)) * C * diagonal (fun i => (a i : K))) i i = 0 :=
    fun i => by rw [mul_diagonal, diagonal_mul, hd, mul_zero, zero_mul]
  exact ⟨⟨_, _, hC', hd', hcoe⟩, by rw [radCoord_eq T hcoe, radCoord_eq T hgL]⟩

theorem torusE_conj_xRt (a : Fin r → Kˣ) (k : Fin r) (z : F) :
    torusE T r a * xRt T k z * (torusE T r a)⁻¹ = xRt T k ((a k : K) • z) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_xRt, coe_xRt,
    torusMap_conj_uMap, Matrix.mul_zero, Matrix.zero_mul]
  congr 1
  funext j
  by_cases hj : j = k
  · subst hj
    simp
  · simp [hj]

theorem torusE_conj_zRt (a : Fin r → Kˣ) (i j : Fin r) (c : K) :
    torusE T r a * zRt T i j c * (torusE T r a)⁻¹ = zRt T i j ((a i : K) * a j * c) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_zRt, coe_zRt,
    torusMap_conj_uMap, OrthogonalSplit.diagonal_mul_altUnit_mul_diagonal]
  congr 1
  funext l
  simp

theorem torusE_const_conj_radTau (s : Kˣ) (B : OrthogonalSplit.altSubgroup r K) :
    torusE T r (fun _ => s) * radTau T r (Multiplicative.ofAdd B) * (torusE T r (fun _ => s))⁻¹ =
      radTau T r (Multiplicative.ofAdd ⟨((s : K) * s) • (B : Matrix (Fin r) (Fin r) K),
        OrthogonalSplit.smul_mem_altSubgroup _ B.2⟩) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_radTau, coe_radTau,
    torusMap_conj_uMap]
  congr 1
  · funext j
    simp
  · ext p q
    rw [mul_diagonal, diagonal_mul, toAdd_ofAdd, toAdd_ofAdd]
    change (s : K) * (B : Matrix (Fin r) (Fin r) K) p q * s = ((s : K) * s) * _
    ring

theorem torusE_const_commute_psiG (s : Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    torusE T r (fun _ => s) * psiG T A = psiG T A * torusE T r (fun _ => s) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_torusE, coe_psiG, torusMap_eq_dMap, psi_eq_dMap,
    dMap_mul_dMap, dMap_mul_dMap, one_mul]
  congr 1
  refine Units.ext ?_
  change diagonal (fun _ => (s : K)) * A.1 = A.1 * diagonal (fun _ => (s : K))
  ext p q
  rw [diagonal_mul, mul_diagonal, mul_comm]

@[expose] def diagConj (a : Fin r → Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    SpecialLinearGroup (Fin r) K :=
  ⟨(OrthogonalSplit.diagGL a : Matrix (Fin r) (Fin r) K) * A *
      ((OrthogonalSplit.diagGL a)⁻¹ : GL (Fin r) K), by
    rw [det_mul, det_mul, A.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, det_one]⟩

omit [CharP K 2] [Finite K] in
theorem coe_diagConj (a : Fin r → Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    (diagConj a A : Matrix (Fin r) (Fin r) K) =
      (OrthogonalSplit.diagGL a : Matrix (Fin r) (Fin r) K) * A *
        ((OrthogonalSplit.diagGL a)⁻¹ : GL (Fin r) K) :=
  rfl

theorem torusE_conj_psiG (a : Fin r → Kˣ) (A : SpecialLinearGroup (Fin r) K) :
    torusE T r a * psiG T A * (torusE T r a)⁻¹ = psiG T (diagConj a A) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_torusE, coe_psiG, coe_psiG,
    torusMap_eq_dMap, psi_eq_dMap, psi_eq_dMap, dMap_inv, dMap_mul_dMap, dMap_mul_dMap, one_mul,
    inv_one, mul_one]
  congr 1
  exact Units.ext rfl

end Torus

section Levi

theorem psiG_conj {g : G0 T r} {L : Fin r → F} {C : Matrix (Fin r) (Fin r) K}
    (hg : g.1 = uMap (normForm T) L C) (A : SpecialLinearGroup (Fin r) K) :
    (psiG T A * g * (psiG T A)⁻¹).1 = uMap (normForm T)
      (conjL (SpecialLinearGroup.toGL A) 1 L)
        (conjC (normForm T) (SpecialLinearGroup.toGL A) 1 L C) := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_psiG, psi_eq_dMap, hg]
  exact dMap_conj_uMap (one_mem _) _ _ _

theorem psiG_conj_mem_radN (A : SpecialLinearGroup (Fin r) K) {g : G0 T r}
    (hg : g ∈ radN T r) : psiG T A * g * (psiG T A)⁻¹ ∈ radN T r := by
  obtain ⟨L, C, hC, hd, hgL⟩ := hg
  obtain ⟨hC', hd'⟩ := conjC_alternating (qA := normForm T) (one_mem _)
    (SpecialLinearGroup.toGL A) L hC hd
  exact ⟨_, _, hC', hd', psiG_conj T hgL A⟩

theorem psiG_conj_mem_range_radTau (A : SpecialLinearGroup (Fin r) K) {g : G0 T r}
    (hg : g ∈ (radTau T r).range) : psiG T A * g * (psiG T A)⁻¹ ∈ (radTau T r).range := by
  have hN := psiG_conj_mem_radN T A (range_radTau_le T hg)
  refine (radCoord_eq_zero_iff T hN).1 ?_
  obtain ⟨B, rfl⟩ := hg
  rw [radCoord_eq T (psiG_conj T (coe_radTau T B) A)]
  funext j
  simp [conjL]

end Levi

section Sylow

variable [CharP K 2] [Finite K]

theorem exists_sylow (hF : Module.finrank K F = 2) (hr : 3 ≤ r) :
    ∃ S : Sylow 2 (G0 T r), ∀ g ∈ (S : Subgroup (G0 T r)),
      ∃ a ∈ (LinearFlag.unitriangular r K).map (psiG T), ∃ b ∈ radN T r, g = a * b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : FiniteDimensional K F := Module.finite_of_finrank_pos (by omega)
  obtain ⟨⟨S, hS⟩, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hr
    (normForm_anisotropic T) (nondegenerate_polarBilin_normForm T hF) (Or.inr hF)
  refine ⟨S, fun g hg => ?_⟩
  rw [hS, Subgroup.mem_subgroupOf] at hg
  obtain ⟨D, L, C, hD, h1, hC, hd, hgD⟩ := (mem_tailUnipotent_iff (normForm_anisotropic T)).1 hg
  have hdet : (D : Matrix (Fin r) (Fin r) K).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hD]
    exact Finset.prod_eq_one fun i _ => h1 i
  set A : SpecialLinearGroup (Fin r) K := ⟨D, hdet⟩
  have hA : A ∈ LinearFlag.unitriangular r K := ⟨fun i j hij => hD hij, h1⟩
  refine ⟨psiG T A, ⟨A, hA, rfl⟩, _, mk_mem_radN T L hC hd, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, coe_psiG, psi_eq_dMap, hgD]
  congr 2
  exact Units.ext rfl

omit [CharP K 2] [Finite K] in
theorem inf_radN_eq_bot :
    (LinearFlag.unitriangular r K).map (psiG T) ⊓ radN T r = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨A, -, rfl⟩, ⟨L, C, -, -, hx⟩⟩
  rw [Subgroup.mem_bot]
  rw [coe_psiG, psi_eq_dMap] at hx
  have hA : SpecialLinearGroup.toGL A = 1 := NonsplitOrthogonalCover.dMap_eq_uMap hx
  have hA1 : A = 1 := SpecialLinearGroup.toGL_injective (by rw [hA, map_one])
  rw [hA1, map_one]

end Sylow

end CFSG.LocalAnalysis.ComponentInitial.NonsplitCatalog
