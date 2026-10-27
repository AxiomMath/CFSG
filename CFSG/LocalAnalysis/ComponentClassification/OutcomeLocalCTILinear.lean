module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLFlagKernel

public noncomputable section

namespace CFSG.ComponentClassification.OutcomeLocal

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_one_of_mul_self_charTwo [CharP K 2] {c : K} (h : c * c = 1) : c = 1 := by
  have h2 : (c - 1) * (c - 1) = 0 := by
    linear_combination h + (1 - c) * (CharTwo.two_eq_zero : (2 : K) = 0)
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h2)

theorem sl_mul_mulVec (g h : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    ((g * h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      (g : Matrix (Fin n) (Fin n) K) *ᵥ ((h : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, mulVec_mulVec]

theorem sl_mulVec_inv_mulVec (g : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [← sl_mul_mulVec, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem sl_inv_mulVec_mulVec (g : SpecialLinearGroup (Fin n) K) (v : Fin n → K) :
    ((g⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = v := by
  rw [← sl_mul_mulVec, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem matrix_eq_of_mulVec {M M' : Matrix (Fin n) (Fin n) K} (h : ∀ v, M *ᵥ v = M' *ᵥ v) :
    M = M' :=
  Matrix.toLin'.injective (LinearMap.ext fun v => by rw [toLin'_apply, toLin'_apply, h v])

theorem exists_sl_lift [Finite K] [CharP K 2] (t : projectiveSL n K) (ht : t * t = 1) :
    ∃ s : SpecialLinearGroup (Fin n) K, proj n K s = t ∧ s * s = 1 := by
  obtain ⟨s₀, rfl⟩ := proj_surjective n K t
  have h2 : s₀ * s₀ ∈ scalars n K := by
    rw [← proj_eq_one_iff, map_mul, ht]
  obtain ⟨c, hcn, hc⟩ := h2
  obtain ⟨μ, hμ⟩ := isSquare_of_charTwo' ((c⁻¹ : Kˣ) : K)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hμ
    exact (c⁻¹).ne_zero hμ
  set b : Kˣ := Units.mk0 μ hμ0 with hbdef
  have hbb : (b : K) * b = ((c⁻¹ : Kˣ) : K) := by rw [hbdef, Units.val_mk0, ← hμ]
  have hbn : b ^ n = 1 := by
    have h1 : (b : K) ^ n * (b : K) ^ n = 1 := by
      rw [← mul_pow, hbb, Units.val_inv_eq_inv_val, inv_pow, ← Units.val_pow_eq_pow_val, hcn,
        Units.val_one, inv_one]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact
      eq_one_of_mul_self_charTwo h1)
  refine ⟨scalarElement b hbn * s₀, ?_, ?_⟩
  · rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars b hbn), one_mul]
  · apply Subtype.ext
    have hc' : (s₀ : Matrix (Fin n) (Fin n) K) * s₀ = scalar (Fin n) (c : K) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul]
      exact hc
    have hcomm : scalar (Fin n) (b : K) * (s₀ : Matrix (Fin n) (Fin n) K) =
        (s₀ : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (b : K) :=
      (scalar_commute (b : K) (fun _ => Commute.all _ _) _).eq
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement,
      Matrix.SpecialLinearGroup.coe_one]
    calc scalar (Fin n) (b : K) * (s₀ : Matrix (Fin n) (Fin n) K) *
          (scalar (Fin n) (b : K) * s₀)
        = scalar (Fin n) (b : K) * (((s₀ : Matrix (Fin n) (Fin n) K) *
          scalar (Fin n) (b : K)) * s₀) := by simp only [Matrix.mul_assoc]
      _ = scalar (Fin n) (b : K) * ((scalar (Fin n) (b : K) *
          (s₀ : Matrix (Fin n) (Fin n) K)) * s₀) := by rw [← hcomm]
      _ = scalar (Fin n) (b : K) * scalar (Fin n) (b : K) *
          ((s₀ : Matrix (Fin n) (Fin n) K) * s₀) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hc', ← (scalar (Fin n)).map_mul, ← (scalar (Fin n)).map_mul, hbb,
            Units.val_inv_eq_inv_val, inv_mul_cancel₀ c.ne_zero, map_one]

theorem commute_of_proj_commute [CharP K 2] [NeZero n] {A s : SpecialLinearGroup (Fin n) K}
    (hs : s * s = 1) (h : proj n K A * proj n K s = proj n K s * proj n K A) :
    A * s = s * A := by
  have hz : (A * s)⁻¹ * (s * A) ∈ scalars n K := by
    rw [← proj_eq_proj_iff, map_mul, map_mul, h]
  set z := (A * s)⁻¹ * (s * A) with hzdef
  have hzc : z ∈ center (SpecialLinearGroup (Fin n) K) := scalars_le_center n K hz
  have h1 : A⁻¹ * s * A = s * z := by rw [hzdef]; group
  have hzz : z * z = 1 := by
    have h2 : (A⁻¹ * s * A) * (A⁻¹ * s * A) = 1 := by
      calc (A⁻¹ * s * A) * (A⁻¹ * s * A) = A⁻¹ * (s * s) * A := by group
        _ = 1 := by rw [hs, mul_one, inv_mul_cancel]
    rw [h1] at h2
    have hcomm : z * s = s * z := (mem_center_iff.mp hzc s).symm
    calc z * z = s * s * (z * z) := by rw [hs, one_mul]
      _ = s * (s * z) * z := by group
      _ = s * (z * s) * z := by rw [hcomm]
      _ = (s * z) * (s * z) := by group
      _ = 1 := h2
  obtain ⟨c, -, hcz⟩ := hz
  have hc1 : (c : K) = 1 := by
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
        ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩) hzz
    simp only [Matrix.SpecialLinearGroup.coe_mul, hcz, Matrix.SpecialLinearGroup.coe_one] at h3
    rw [← map_mul, scalar_apply, diagonal_apply_eq, one_apply_eq] at h3
    exact eq_one_of_mul_self_charTwo h3
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [hcz, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hzdef, inv_mul_eq_one] at hz1
  exact hz1

section Flag

variable (s : SpecialLinearGroup (Fin n) K)

abbrev dispMat : Matrix (Fin n) (Fin n) K := (s : Matrix (Fin n) (Fin n) K) - 1

@[expose] def dispRange : Submodule K (Fin n → K) := LinearMap.range (mulVecLin (dispMat s))

@[expose] def dispKer : Submodule K (Fin n → K) := LinearMap.ker (mulVecLin (dispMat s))

variable {s}

theorem mem_dispRange {w : Fin n → K} : w ∈ dispRange s ↔ ∃ v, dispMat s *ᵥ v = w := by
  simp only [dispRange, LinearMap.mem_range, mulVecLin_apply]

theorem mem_dispKer {v : Fin n → K} : v ∈ dispKer s ↔ dispMat s *ᵥ v = 0 := by
  simp only [dispKer, LinearMap.mem_ker, mulVecLin_apply]

theorem dispMat_mul_self [CharP K 2] (hs : s * s = 1) : dispMat s * dispMat s = 0 := by
  have hs' : (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hs, Matrix.SpecialLinearGroup.coe_one]
  have h2 : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := fun M => by
    rw [← two_smul K M, CharTwo.two_eq_zero, zero_smul]
  calc dispMat s * dispMat s
      = (s : Matrix (Fin n) (Fin n) K) * (s : Matrix (Fin n) (Fin n) K) + 1 -
        ((s : Matrix (Fin n) (Fin n) K) + (s : Matrix (Fin n) (Fin n) K)) := by noncomm_ring
    _ = 0 := by rw [hs', h2, h2, sub_zero]

theorem dispRange_le_dispKer [CharP K 2] (hs : s * s = 1) : dispRange s ≤ dispKer s := by
  intro w hw
  obtain ⟨v, rfl⟩ := mem_dispRange.mp hw
  rw [mem_dispKer, mulVec_mulVec, dispMat_mul_self hs, zero_mulVec]

theorem exists_dispMat_ne_zero (hs1 : s ≠ 1) : ∃ v, dispMat s *ᵥ v ≠ 0 := by
  by_contra hall
  apply hs1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  refine matrix_eq_of_mulVec fun v => ?_
  have h : dispMat s *ᵥ v = 0 := by
    by_contra hv
    exact hall ⟨v, hv⟩
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at h
  rw [h, one_mulVec]

theorem dispRange_ne_bot (hs1 : s ≠ 1) : dispRange s ≠ ⊥ := by
  obtain ⟨v, hv⟩ := exists_dispMat_ne_zero hs1
  intro h
  have hmem : dispMat s *ᵥ v ∈ dispRange s := mem_dispRange.mpr ⟨v, rfl⟩
  rw [h, Submodule.mem_bot] at hmem
  exact hv hmem

theorem dispKer_ne_top (hs1 : s ≠ 1) : dispKer s ≠ ⊤ := by
  obtain ⟨v, hv⟩ := exists_dispMat_ne_zero hs1
  intro h
  have hmem : v ∈ dispKer s := h ▸ Submodule.mem_top
  exact hv (mem_dispKer.mp hmem)

theorem mulVec_dispMat_of_commute {A : SpecialLinearGroup (Fin n) K} (hAs : A * s = s * A)
    (v : Fin n → K) :
    (A : Matrix (Fin n) (Fin n) K) *ᵥ (dispMat s *ᵥ v) =
      dispMat s *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
  have h := congrArg (fun g : SpecialLinearGroup (Fin n) K =>
    (g : Matrix (Fin n) (Fin n) K) *ᵥ v) hAs
  simp only [sl_mul_mulVec] at h
  rw [sub_mulVec, one_mulVec, mulVec_sub, h, sub_mulVec, one_mulVec]

theorem mapsTo_of_commute {A : SpecialLinearGroup (Fin n) K} (hAs : A * s = s * A) :
    (∀ w ∈ dispRange s, (A : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ dispRange s) ∧
      ∀ v ∈ dispKer s, (A : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ dispKer s := by
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨v, rfl⟩ := mem_dispRange.mp hw
    exact mem_dispRange.mpr ⟨_, (mulVec_dispMat_of_commute hAs v).symm⟩
  · rw [mem_dispKer] at hv ⊢
    rw [← mulVec_dispMat_of_commute hAs, hv, mulVec_zero]

variable [CharP K 2]

theorem commute_of_mem_flagKernel (hs : s * s = 1) {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs)) :
    u * s = s * u := by
  obtain ⟨hu1, -, hu3⟩ := hu
  apply Subtype.ext
  have huN : (u : Matrix (Fin n) (Fin n) K) * dispMat s = dispMat s := by
    refine matrix_eq_of_mulVec fun v => ?_
    rw [← mulVec_mulVec]
    have h := hu1 (dispMat s *ᵥ v) (mem_dispRange.mpr ⟨v, rfl⟩)
    rwa [sub_mulVec, one_mulVec, sub_eq_zero] at h
  have hNu : dispMat s * (u : Matrix (Fin n) (Fin n) K) = dispMat s := by
    refine matrix_eq_of_mulVec fun v => ?_
    rw [← mulVec_mulVec, mulVec_eq_add_sub_one (u : Matrix (Fin n) (Fin n) K) v, mulVec_add]
    have h : dispMat s *ᵥ (((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ v) = 0 :=
      mem_dispKer.mp (hu3 v)
    rw [h, add_zero]
  have hs' : (s : Matrix (Fin n) (Fin n) K) = 1 + dispMat s := by rw [add_sub_cancel]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hs', Matrix.mul_add,
    Matrix.add_mul, huN, hNu, Matrix.mul_one, Matrix.one_mul]

theorem conj_mem_flagKernel (hs : s * s = 1) {A : SpecialLinearGroup (Fin n) K}
    (hAs : A * s = s * A) {u : SpecialLinearGroup (Fin n) K}
    (hu : u ∈ flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs)) :
    A * u * A⁻¹ ∈ flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) := by
  have hAs' : A⁻¹ * s = s * A⁻¹ := by
    calc A⁻¹ * s = A⁻¹ * (s * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * s) * A⁻¹ := by rw [hAs]
      _ = s * A⁻¹ := by group
  obtain ⟨hAW, hAL⟩ := mapsTo_of_commute hAs
  obtain ⟨hAW', hAL'⟩ := mapsTo_of_commute hAs'
  obtain ⟨hu1, hu2, hu3⟩ := hu
  have hform : ∀ x, (((A * u * A⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) - 1) *ᵥ x = (A : Matrix (Fin n) (Fin n) K) *ᵥ
        (((u : Matrix (Fin n) (Fin n) K) - 1) *ᵥ (((A⁻¹ : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ x)) := by
    intro x
    rw [sub_mulVec, one_mulVec, sl_mul_mulVec, sl_mul_mulVec, sub_mulVec, one_mulVec, mulVec_sub,
      sl_mulVec_inv_mulVec]
  refine ⟨fun w hw => ?_, fun x hx => ?_, fun x => ?_⟩
  · rw [hform, hu1 _ (hAW' w hw), mulVec_zero]
  · rw [hform]
    exact hAW _ (hu2 _ (hAL' x hx))
  · rw [hform]
    exact hAL _ (hu3 _)

end Flag

theorem proj_eq_of_conj_eq [Finite K] (hn : 3 ≤ n) {g h : SpecialLinearGroup (Fin n) K}
    (H : MulAut.conj (proj n K g) = MulAut.conj (proj n K h)) : proj n K g = proj n K h := by
  have h1 : conjAut n K (SpecialLinearGroup.toGL (g⁻¹ * h)) = 1 := by
    have h2 : MulAut.conj (proj n K (g⁻¹ * h)) =
        (MulAut.conj (proj n K g))⁻¹ * MulAut.conj (proj n K h) := by
      simp only [map_mul, map_inv]
    rw [conjAut_toGL, h2, H, inv_mul_cancel]
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff hn _).mp h1
  have hcm : ((g⁻¹ * h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      scalar (Fin n) (c : K) := by
    have h2 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) hc
    simp only [GeneralLinearGroup.coe_scalar] at h2
    rw [h2]
    rfl
  rw [proj_eq_proj_iff]
  refine ⟨c, ?_, hcm⟩
  apply Units.ext
  have hdet := (g⁻¹ * h).2
  rw [hcm, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    at hdet
  rw [Units.val_pow_eq_pow_val, hdet, Units.val_one]

theorem mem_map_flagKernel_of_commute {f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {W L : Submodule K (Fin n → K)} (hW : W ≠ ⊥) (hWL : W ≤ L)
    (hL : L ≠ ⊤) {A : SpecialLinearGroup (Fin n) K}
    (hA : ∀ u ∈ flagKernel W L hWL, proj n K A * proj n K u = proj n K u * proj n K A) :
    proj n K A ∈ (flagKernel W L hWL).map (proj n K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨-, -, -, -, hιapp, -, -, hcentEq, -⟩ :=
    even_linear_flag_kernel_projective_centralizer hn hf hK hW hWL hL
  have hmem : conjAut n K (SpecialLinearGroup.toGL A) ∈ semilinearAutGroup n K ⊓
      centralizer ((flagKernelInner W L hWL).range : Set (MulAut (projectiveSL n K))) := by
    refine mem_inf.mpr ⟨linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup _),
      mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [hιapp, conjAut_toGL, conjAut_toGL, ← map_mul MulAut.conj, ← map_mul MulAut.conj,
      hA u u.2]
  rw [hcentEq] at hmem
  obtain ⟨z, -, hz⟩ := hmem
  rw [hιapp, conjAut_toGL, conjAut_toGL] at hz
  exact ⟨z, z.2, proj_eq_of_conj_eq hn hz⟩

theorem mem_flagKernel_of_commute_two [CharP K 2] {s A : SpecialLinearGroup (Fin 2) K}
    (hs : s * s = 1) (hs1 : s ≠ 1) (hAs : A * s = s * A) :
    A ∈ flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) := by
  set W := dispRange s with hWdef
  set L := dispKer s with hLdef
  have hWL : W ≤ L := dispRange_le_dispKer hs
  have hrank := LinearMap.finrank_range_add_finrank_ker (mulVecLin (dispMat s))
  rw [Module.finrank_fin_fun] at hrank
  change Module.finrank K W + Module.finrank K L = 2 at hrank
  have hW1 : 1 ≤ Module.finrank K W :=
    Submodule.one_le_finrank_iff.mpr (dispRange_ne_bot hs1)
  have hWLr := Submodule.finrank_mono hWL
  have hWeq : Module.finrank K W = 1 := by omega
  have hWLeq : W = L := Submodule.eq_of_le_of_finrank_eq hWL (by omega)
  obtain ⟨w₀, hw₀W, hw₀⟩ := (Submodule.ne_bot_iff W).mp (dispRange_ne_bot hs1)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hWeq hw₀W hw₀
  obtain ⟨hAW, -⟩ := mapsTo_of_commute hAs
  have hAw₀ : (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w₀ ∈ W := hAW w₀ hw₀W
  rw [hspan] at hAw₀
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hAw₀
  have hAw : ∀ w ∈ W, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ w = a • w := by
    intro w hw
    rw [hspan] at hw
    obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [mulVec_smul, ← ha, smul_comm]
  have hAv : ∀ v, (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v - a • v ∈ W := by
    intro v
    rw [hWLeq, mem_dispKer, mulVec_sub, ← mulVec_dispMat_of_commute hAs,
      hAw _ (mem_dispRange.mpr ⟨v, rfl⟩), mulVec_smul, sub_self]
  have h2 : ∀ x : Fin 2 → K, x + x = 0 := fun x => funext fun i => CharTwo.add_self_eq_zero (x i)
  have hAA : (A : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
      scalar (Fin 2) (a * a) := by
    refine matrix_eq_of_mulVec fun v => ?_
    have h1 := hAw _ (hAv v)
    rw [mulVec_sub, mulVec_smul] at h1
    rw [← mulVec_mulVec, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
    calc (A : Matrix (Fin 2) (Fin 2) K) *ᵥ ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v)
        = a • ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v) +
          a • ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v - a • v) := by
          rw [← h1]
          abel
      _ = (a • ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v) +
          a • ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ v)) - (a * a) • v := by
          rw [smul_sub, smul_smul]
          abel
      _ = (a * a) • v := by rw [h2, zero_sub, neg_eq_of_add_eq_zero_left (h2 _)]
  have ha4 : a ^ 4 = 1 := by
    have h1 := congrArg Matrix.det hAA
    rw [det_mul, A.2, mul_one, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at h1
    calc a ^ 4 = (a * a) ^ 2 := by ring
      _ = 1 := h1.symm
  have ha1 : a = 1 := eq_one_of_pow_four ha4
  subst ha1
  refine ⟨fun w hw => ?_, fun v _ => ?_, fun v => ?_⟩
  · rw [sub_mulVec, one_mulVec, hAw w hw, one_smul, sub_self]
  · rw [sub_mulVec, one_mulVec]
    simpa only [one_smul] using hAv v
  · have hLW : dispKer s = dispRange s := hWLeq.symm
    rw [sub_mulVec, one_mulVec, hLW]
    simpa only [one_smul] using hAv v

theorem even_linear_involution_centralizers_component_free {f n : ℕ} (hf : 1 ≤ f) (hn : 2 ≤ n)
    {k : Type*} [Field k] (hk : Nat.card k = 2 ^ f) (t : projectiveSL n k) (ht : orderOf t = 2)
    (B : Subgroup (centralizer ({t} : Set (projectiveSL n k)))) : ¬ CFSG.IsComponent B := by
  classical
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := finite_field_prime_power_characteristic Nat.prime_two hf hk
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (SpecialLinearGroup (Fin n) k) := inferInstance
  have : Finite (centralizer ({t} : Set (projectiveSL n k))) := inferInstance
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨s, rfl, hs⟩ := exists_sl_lift t htt
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ht
    exact absurd ht (by norm_num)
  set U := flagKernel (dispRange s) (dispKer s) (dispRange_le_dispKer hs) with hUdef
  set Q := U.map (proj n k) with hQdef
  have hlift : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)),
      ∃ A : SpecialLinearGroup (Fin n) k, proj n k A = c ∧ A * s = s * A := by
    intro c hc
    obtain ⟨A, rfl⟩ := proj_surjective n k c
    exact ⟨A, rfl, commute_of_proj_commute hs (mem_centralizer_singleton_iff.mp hc)⟩
  have hQC : Q ≤ centralizer ({proj n k s} : Set (projectiveSL n k)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, commute_of_mem_flagKernel hs hu]
  have hQp : IsPGroup 2 Q := isPGroup_flagKernel.map (proj n k)
  have hnorm : ∀ c ∈ centralizer ({proj n k s} : Set (projectiveSL n k)), ∀ q ∈ Q,
      c * q * c⁻¹ ∈ Q := by
    intro c hc q hq
    obtain ⟨A, rfl, hAs⟩ := hlift c hc
    obtain ⟨u, hu, rfl⟩ := hq
    exact ⟨A * u * A⁻¹, conj_mem_flagKernel hs hAs hu, by rw [map_mul, map_mul, map_inv]⟩
  refine not_isComponent_of_le hQC hQp hnorm (fun c hc hcQ => ?_) B
  obtain ⟨A, rfl, hAs⟩ := hlift c hc
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  ·
    obtain rfl : n = 2 := by omega
    exact ⟨A, mem_flagKernel_of_commute_two hs hs1 hAs, rfl⟩
  · exact mem_map_flagKernel_of_commute hn3 hf hk (dispRange_ne_bot hs1)
      (dispRange_le_dispKer hs) (dispKer_ne_top hs1)
      fun u hu => hcQ _ ⟨u, hu, rfl⟩

end CFSG.ComponentClassification.OutcomeLocal
