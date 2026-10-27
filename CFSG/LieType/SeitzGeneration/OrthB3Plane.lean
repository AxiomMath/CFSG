module

public import CFSG.LieType.SeitzGeneration.OrthCubeM2
public import CFSG.LieType.SeitzGeneration.OrthEx
public import CFSG.LieType.SeitzGeneration.OrthLow

public noncomputable section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal OrthBlk

section Plane

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

variable (Q : QuadraticForm K V) in
@[expose] def planeCoord (a₁ a₂ : V) (τ : K) : V →ₗ[K] (Fin 2 → K) where
  toFun v := ![(2 * polar Q v a₁ - τ * polar Q v a₂) / (4 - τ ^ 2),
    (2 * polar Q v a₂ - τ * polar Q v a₁) / (4 - τ ^ 2)]
  map_add' v w := by
    ext i; fin_cases i <;> simp [polar_add_left] <;> ring
  map_smul' c v := by
    ext i; fin_cases i <;> simp [polar_smul_left] <;> ring

@[expose] def planeEmb (a₁ a₂ : V) : (Fin 2 → K) →ₗ[K] V where
  toFun y := y 0 • a₁ + y 1 • a₂
  map_add' x y := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

variable {Q : QuadraticForm K V}

theorem planeCoord_eq_zero {a₁ a₂ : V} {τ : K} (hτ : 4 - τ ^ 2 ≠ 0) {v : V}
    (hv : planeCoord Q a₁ a₂ τ v = 0) : polar Q v a₁ = 0 ∧ polar Q v a₂ = 0 := by
  have e0 := congrFun hv 0
  have e1 := congrFun hv 1
  simp only [planeCoord, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply, div_eq_zero_iff, hτ, or_false] at e0 e1
  refine ⟨?_, ?_⟩
  · have : (4 - τ ^ 2) * polar Q v a₁ = 0 := by linear_combination 2 * e0 + τ * e1
    exact (mul_eq_zero.mp this).resolve_left hτ
  · have : (4 - τ ^ 2) * polar Q v a₂ = 0 := by linear_combination 2 * e1 + τ * e0
    exact (mul_eq_zero.mp this).resolve_left hτ

theorem planeCoord_of_orth {a₁ a₂ : V} {τ : K} {v : V} (h1 : polar Q v a₁ = 0)
    (h2 : polar Q v a₂ = 0) : planeCoord Q a₁ a₂ τ v = 0 := by
  ext i; fin_cases i <;> simp [planeCoord, h1, h2]

theorem planeCoord_map_eq_zero {a₁ a₂ : V} {τ : K} (hτ : 4 - τ ^ 2 ≠ 0) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h1 : g a₁ = a₁) (h2 : g a₂ = a₂) {v : V}
    (hv : planeCoord Q a₁ a₂ τ v = 0) : planeCoord Q a₁ a₂ τ (g v) = 0 := by
  obtain ⟨e1, e2⟩ := planeCoord_eq_zero hτ hv
  refine planeCoord_of_orth ?_ ?_
  · rw [← h1, polar_map_of_mem hg, e1]
  · rw [← h2, polar_map_of_mem hg, e2]

@[expose] def planeBlock (a₁ a₂ : V) (τ : K) (h1 : Q a₁ = 1) (h2 : Q a₂ = 1)
    (h12 : polar Q a₁ a₂ = τ) (hτ : 4 - τ ^ 2 ≠ 0) : QBlock Q (Fin 2 → K) where
  ι := planeEmb a₁ a₂
  m := planeCoord Q a₁ a₂ τ
  qM y := y 0 ^ 2 + τ * y 0 * y 1 + y 1 ^ 2
  m_ι y := by
    have p11 : polar Q a₁ a₁ = 2 := by rw [polar_self, h1]; ring
    have p22 : polar Q a₂ a₂ = 2 := by rw [polar_self, h2]; ring
    have p21 : polar Q a₂ a₁ = τ := by rw [polar_comm, h12]
    ext i; fin_cases i <;>
      simp [planeCoord, planeEmb, polar_add_left, polar_smul_left, p11, p22, h12, p21] <;>
      field_simp <;> ring
  Q_add v y hv := by
    obtain ⟨hv1, hv2⟩ := planeCoord_eq_zero hτ hv
    change Q (v + (y 0 • a₁ + y 1 • a₂)) = Q v + (y 0 ^ 2 + τ * y 0 * y 1 + y 1 ^ 2)
    rw [QuadraticMap.map_add Q v, polar_add_right, polar_smul_right, polar_smul_right, hv1, hv2,
      QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, h1, h2,
      polar_smul_left, polar_smul_right, h12]
    simp only [smul_eq_mul]
    ring

theorem polarNondegOn_span_pair {a₁ a₂ : V} {τ : K} (h1 : Q a₁ = 1) (h2 : Q a₂ = 1)
    (h12 : polar Q a₁ a₂ = τ) (hτ : 4 - τ ^ 2 ≠ 0) :
    PolarNondegOn Q (Submodule.span K {a₁, a₂}) := by
  intro v hv hvy
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  have e1 := hvy a₁ (Submodule.subset_span (by simp))
  have e2 := hvy a₂ (Submodule.subset_span (by simp))
  have p11 : polar Q a₁ a₁ = 2 := by rw [polar_self, h1]; ring
  have p22 : polar Q a₂ a₂ = 2 := by rw [polar_self, h2]; ring
  have p21 : polar Q a₂ a₁ = τ := by rw [polar_comm, h12]
  simp only [polar_add_left, polar_smul_left, p11, p22, h12, p21, smul_eq_mul] at e1 e2
  have hα : (4 - τ ^ 2) * α = 0 := by linear_combination 2 * e1 - τ * e2
  have hβ : (4 - τ ^ 2) * β = 0 := by linear_combination 2 * e2 - τ * e1
  rw [(mul_eq_zero.mp hα).resolve_left hτ, (mul_eq_zero.mp hβ).resolve_left hτ, zero_smul,
    zero_smul, add_zero]

theorem mem_perp_span_pair {a₁ a₂ v : V} :
    v ∈ perp Q (Submodule.span K {a₁, a₂}) ↔ polar Q a₁ v = 0 ∧ polar Q a₂ v = 0 := by
  rw [mem_perp]
  refine ⟨fun h => ⟨h a₁ (Submodule.subset_span (by simp)),
    h a₂ (Submodule.subset_span (by simp))⟩, ?_⟩
  rintro ⟨h1, h2⟩ s hs
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hs
  rw [polar_add_left, polar_smul_left, polar_smul_left, h1, h2]
  simp

end Plane

section Sum

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {M M' : Type} [AddCommGroup M] [Module K M] [AddCommGroup M'] [Module K M']

@[expose] def QBlock.sum (C : QBlock Q M) (C' : QBlock Q M') (h1 : ∀ y, C.m (C'.ι y) = 0)
    (h2 : ∀ y, C'.m (C.ι y) = 0) : QBlock Q (M × M') where
  ι := C.ι.coprod C'.ι
  m := C.m.prod C'.m
  qM y := C.qM y.1 + C'.qM y.2
  m_ι y := by
    change (C.m (C.ι y.1 + C'.ι y.2), C'.m (C.ι y.1 + C'.ι y.2)) = y
    rw [map_add, map_add, C.m_ι, C'.m_ι, h1, h2, add_zero, zero_add]
  Q_add v y hv := by
    have hv1 : C.m v = 0 := congrArg Prod.fst hv
    have hv2 : C'.m v = 0 := congrArg Prod.snd hv
    change Q (v + (C.ι y.1 + C'.ι y.2)) = Q v + (C.qM y.1 + C'.qM y.2)
    have e : C'.m (v + C.ι y.1) = 0 := by rw [map_add, hv2, h2, add_zero]
    rw [← add_assoc, C'.Q_add _ _ e, C.Q_add _ _ hv1, add_assoc]

end Sum

section Matrix

variable {K : Type} [Field K]

@[expose] def polDet (X Y : Matrix (Fin 2) (Fin 2) K) : K :=
  (X + Y).det - X.det - Y.det

theorem polDet_eq (X Y : Matrix (Fin 2) (Fin 2) K) :
    polDet X Y = X.trace * Y.trace - (X * Y).trace := by
  simp only [polDet, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

theorem polDet_zero_left (Y : Matrix (Fin 2) (Fin 2) K) : polDet 0 Y = 0 := by
  simp [polDet]

theorem polDet_comm (X Y : Matrix (Fin 2) (Fin 2) K) : polDet X Y = polDet Y X := by
  rw [polDet, polDet, add_comm]
  ring

theorem polDet_smul_left (c : K) (X Y : Matrix (Fin 2) (Fin 2) K) :
    polDet (c • X) Y = c * polDet X Y := by
  rw [polDet_eq, polDet_eq, Matrix.trace_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul]
  ring

theorem polDet_self (X : Matrix (Fin 2) (Fin 2) K) : polDet X X = 2 * X.det := by
  simp only [polDet, Matrix.det_fin_two, Matrix.add_apply]
  ring

theorem sq_eq_trace_smul {x : Matrix (Fin 2) (Fin 2) K} (hdet : x.det = 1) :
    x * x = x.trace • x - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | linear_combination -hdet | ring

theorem mul_mul_eq_of_polDet {x X : Matrix (Fin 2) (Fin 2) K} (hdet : x.det = 1)
    (h1 : polDet X 1 = 0) (hx : polDet X x = 0) : x * X * x = X := by
  rw [polDet_eq, Matrix.trace_one, Matrix.mul_one, Fintype.card_fin, Matrix.trace_fin_two] at h1
  rw [polDet_eq, Matrix.trace_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two] at hx
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_ofNat] at h1 hx
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-x 0 0) * hx + X 0 0 * hdet + (x 0 0 ^ 2 + x 0 1 * x 1 0) * h1
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-x 0 1) * hx + X 0 1 * hdet + (x 0 0 * x 0 1 + x 0 1 * x 1 1) * h1
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-x 1 0) * hx + X 1 0 * hdet + (x 0 0 * x 1 0 + x 1 0 * x 1 1) * h1
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-x 1 1) * hx + X 1 1 * hdet + (x 1 1 ^ 2 + x 0 1 * x 1 0) * h1

theorem pow_mul_pow_eq_of_mul_mul_eq {x X : Matrix (Fin 2) (Fin 2) K} (h : x * X * x = X)
    (n : ℕ) : x ^ n * X * x ^ n = X := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc x ^ (n + 1) * X * x ^ (n + 1) = x * x ^ n * X * (x ^ n * x) := by
          rw [← pow_succ', ← pow_succ]
      _ = x * (x ^ n * X * x ^ n) * x := by simp only [Matrix.mul_assoc]
      _ = X := by rw [ih, h]

end Matrix

section M2Polar

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_m2Emb {P P' : HypPair Q} (v : V) (X : Matrix (Fin 2) (Fin 2) K) :
    polar Q v (m2Emb P P' X) = polDet (m2Proj P P' v) X := by
  simp [m2Emb, m2Proj, polDet, Matrix.det_fin_two, polar_add_right, polar_smul_right,
    polar_neg_right]
  ring

end M2Polar

section Sandwich

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def sw (A C : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K →ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun X := A * X * C
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem sw_apply (A C X : Matrix (Fin 2) (Fin 2) K) : sw A C X = A * X * C := rfl

theorem sw_comp (A C A' C' : Matrix (Fin 2) (Fin 2) K) :
    sw A C ∘ₗ sw A' C' = sw (A * A') (C' * C) :=
  LinearMap.ext fun X => by simp only [LinearMap.comp_apply, sw_apply, Matrix.mul_assoc]

theorem sw_one : sw (1 : Matrix (Fin 2) (Fin 2) K) 1 = LinearMap.id :=
  LinearMap.ext fun X => by simp [sw_apply]

open Matrix.SpecialLinearGroup in
theorem sw_inv_comp (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    sw (g : Matrix (Fin 2) (Fin 2) K) ↑h⁻¹ ∘ₗ sw ↑g⁻¹ ↑h = LinearMap.id := by
  rw [sw_comp, ← coe_mul, ← coe_mul, mul_inv_cancel, mul_inv_cancel, coe_one, sw_one]

open Matrix.SpecialLinearGroup in
theorem sw_inv_comp' (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    sw (↑g⁻¹ : Matrix (Fin 2) (Fin 2) K) ↑h ∘ₗ sw ↑g ↑h⁻¹ = LinearMap.id := by
  rw [sw_comp, ← coe_mul, ← coe_mul, inv_mul_cancel, inv_mul_cancel, coe_one, sw_one]

namespace QBlock

variable (B : QBlock Q (Matrix (Fin 2) (Fin 2) K))

open Matrix.SpecialLinearGroup in
@[expose] def sand :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* (V ≃ₗ[K] V) where
  toFun gh := B.blkEquivOf (sw gh.1 ↑gh.2⁻¹) (sw ↑gh.1⁻¹ gh.2) (sw_inv_comp gh.1 gh.2)
    (sw_inv_comp' gh.1 gh.2)
  map_one' := LinearEquiv.ext fun v => by
    change B.blk (sw ↑(1 : Matrix.SpecialLinearGroup (Fin 2) K)
      ↑(1 : Matrix.SpecialLinearGroup (Fin 2) K)⁻¹) v = v
    rw [inv_one, coe_one, sw_one, blk_id]
  map_mul' a b := LinearEquiv.ext fun v => by
    change B.blk (sw ↑(a.1 * b.1) ↑(a.2 * b.2)⁻¹) v =
      B.blk (sw a.1 ↑a.2⁻¹) (B.blk (sw b.1 ↑b.2⁻¹) v)
    rw [← blk_comp, sw_comp, mul_inv_rev, coe_mul, coe_mul]

theorem sand_apply (gh : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : V) : B.sand gh v = B.blk (sw gh.1 ↑gh.2⁻¹) v := rfl

theorem sand_ι (gh : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (X : Matrix (Fin 2) (Fin 2) K) :
    B.sand gh (B.ι X) =
      B.ι ((gh.1 : Matrix (Fin 2) (Fin 2) K) * X * (↑gh.2⁻¹ : Matrix (Fin 2) (Fin 2) K)) := by
  rw [sand_apply, blk_ι, sw_apply]

theorem sand_of_m_eq_zero
    (gh : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) {v : V}
    (hv : B.m v = 0) : B.sand gh v = v :=
  B.blk_of_m_eq_zero _ hv

open Matrix.SpecialLinearGroup in
theorem sand_mem_orthogonalGroup (hq : ∀ X, B.qM X = X.det)
    (gh : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    B.sand gh ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  B.blkEquivOf_mem_orthogonalGroup (sw gh.1 ↑gh.2⁻¹) (sw ↑gh.1⁻¹ gh.2) (sw_inv_comp gh.1 gh.2)
    (sw_inv_comp' gh.1 gh.2) fun X => by
    rw [hq, hq, sw_apply, Matrix.det_mul, Matrix.det_mul, det_coe, det_coe, one_mul, mul_one]

theorem sand_commute {M' : Type} [AddCommGroup M'] [Module K M'] (C : QBlock Q M')
    (h1 : ∀ y, B.m (C.ι y) = 0) (h2 : ∀ X, C.m (B.ι X) = 0) {T T' : M' →ₗ[K] M'}
    (hT : T ∘ₗ T' = LinearMap.id) (hT' : T' ∘ₗ T = LinearMap.id)
    (gh : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    Commute (B.sand gh) (C.blkEquivOf T T' hT hT') :=
  LinearEquiv.ext fun v => B.blk_comm C h1 h2 _ _ v

end QBlock

@[expose] def upT (μ : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, μ; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def loT (μ : K) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 0; μ, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_upT (μ : K) : (upT μ : Matrix (Fin 2) (Fin 2) K) = !![1, μ; 0, 1] := rfl

theorem coe_loT (μ : K) : (loT μ : Matrix (Fin 2) (Fin 2) K) = !![1, 0; μ, 1] := rfl

theorem upT_zero : upT (0 : K) = 1 :=
  Subtype.ext (by rw [coe_upT, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two])

theorem loT_zero : loT (0 : K) = 1 :=
  Subtype.ext (by rw [coe_loT, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two])

theorem coe_upT_inv (μ : K) : (↑(upT μ)⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![1, -μ; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_upT, Matrix.adjugate_fin_two_of]
  simp

theorem coe_loT_inv (μ : K) : (↑(loT μ)⁻¹ : Matrix (Fin 2) (Fin 2) K) = !![1, 0; -μ, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_loT, Matrix.adjugate_fin_two_of]
  simp

theorem upT_pow (μ : K) (n : ℕ) : upT μ ^ n = upT (n * μ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, upT_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_upT, coe_upT, coe_upT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem loT_pow (μ : K) (n : ℕ) : loT μ ^ n = loT (n * μ) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, loT_zero]
  | succ n ih =>
    rw [pow_succ, ih]
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_loT, coe_loT, coe_loT]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring

theorem upT_pow_ringChar (μ : K) : upT μ ^ ringChar K = 1 := by
  rw [upT_pow, ringChar.Nat.cast_ringChar, zero_mul, upT_zero]

theorem loT_pow_ringChar (μ : K) : loT μ ^ ringChar K = 1 := by
  rw [loT_pow, ringChar.Nat.cast_ringChar, zero_mul, loT_zero]

end Sandwich

section Elliptic

variable {K : Type} [Field K]

theorem one_add_pow_of_mul_self {R : Type*} [Ring R] {N : R} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + n • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN, smul_zero, add_zero,
      succ_nsmul]
    abel

theorem trace_sq_ne_zero [Finite K] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hpq : ¬ p ∣ Nat.card K - 1) {x : Matrix (Fin 2) (Fin 2) K} (hdet : x.det = 1)
    (hxp : x ^ p = 1) (hx1 : x ≠ 1) (t : K) : t ^ 2 - x.trace * t + 1 ≠ 0 := by
  intro ht
  have hdet' := hdet
  rw [Matrix.det_fin_two] at hdet'
  have ht2 : t ^ 2 - (x 0 0 + x 1 1) * t + 1 = 0 := by rw [← Matrix.trace_fin_two]; exact ht
  have hroot : ∃ s : K, s ^ 2 - x.trace * s + 1 = 0 ∧ s ^ p = 1 := by
    set t' := x.trace - t with ht'
    have ht'r : t' ^ 2 - x.trace * t' + 1 = 0 := by rw [ht']; linear_combination ht
    have hfac : (x - t • 1) * (x - t' • 1) = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, ht', Matrix.trace_fin_two] <;>
        first | linear_combination -ht2 - hdet' | ring
    by_cases hM : x - t' • 1 = 0
    · refine ⟨t', ht'r, ?_⟩
      have hx : x = t' • 1 := sub_eq_zero.mp hM
      have h00 := congrFun (congrFun hxp 0) 0
      rw [hx, smul_pow, one_pow] at h00
      simpa using h00
    · refine ⟨t, ht, ?_⟩
      have hxM : x * (x - t' • 1) = t • (x - t' • 1) := by
        have h := hfac
        rw [sub_mul, sub_eq_zero, smul_mul_assoc, Matrix.one_mul] at h
        exact h
      have hpow : ∀ n : ℕ, x ^ n * (x - t' • 1) = t ^ n • (x - t' • 1) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, hxM, smul_smul, ← pow_succ]
      have h1 := hpow p
      rw [hxp, Matrix.one_mul] at h1
      by_contra htp
      apply hM
      have h2 : (1 - t ^ p) • (x - t' • 1) = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (Ne.symm htp))
  obtain ⟨s, hs, hsp⟩ := hroot
  have hs1 : s = 1 := by
    by_contra hne
    exact hpq (dvd_card_sub_one_of_pow_eq_one hp hsp hne)
  subst hs1
  have hτ : x 0 0 + x 1 1 = 2 := by
    rw [Matrix.trace_fin_two] at hs
    linear_combination -hs
  have hN2 : (x - 1) * (x - 1) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination x 0 0 * hτ - hdet'
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination x 0 1 * hτ
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination x 1 0 * hτ
    · simp [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination x 1 1 * hτ - hdet'
  have hxN : x = 1 + (x - 1) := by rw [add_sub_cancel]
  rw [hxN, one_add_pow_of_mul_self hN2] at hxp
  have hpN : (p : K) • (x - 1) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact add_eq_left.mp hxp
  apply hx1
  rw [hxN, (smul_eq_zero.mp hpN).resolve_left hpK, add_zero]

theorem eq_one_of_central {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) (hgp : g ^ p = 1)
    (hc : ∀ Y : Matrix (Fin 2) (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) * Y = Y * g) : g = 1 := by
  have hsc := scalar_of_commute_fin_two hc
  set t := (g : Matrix (Fin 2) (Fin 2) K) 0 0 with htdef
  have hdet : t * t = 1 := by
    have h := congrArg Matrix.det hsc
    rw [Matrix.SpecialLinearGroup.det_coe, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
      mul_one, _root_.sq] at h
    exact h.symm
  have htp : t ^ p = 1 := by
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hgp, Matrix.SpecialLinearGroup.coe_one]
    rw [hsc, smul_pow, one_pow] at h1
    simpa using congrFun (congrFun h1 0) 0
  have ht1 : t = 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rw [hk, pow_succ, pow_mul, _root_.sq, hdet, one_pow, one_mul] at htp
    exact htp
  exact Subtype.ext (by rw [hsc, ht1, one_smul, Matrix.SpecialLinearGroup.coe_one])

end Elliptic

section Fix

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem dvd_of_zpow_apply {g : V ≃ₗ[K] V} {p : ℕ} (hp : p.Prime) (hgp : g ^ p = 1) {v : V}
    (hv : g v ≠ v) {k : ℤ} (hk : (g ^ k) v = v) : (p : ℤ) ∣ k := by
  by_contra hnd
  obtain ⟨u, w, huw⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).mpr hnd
  apply hv
  have hg : g = (g ^ (p : ℤ)) ^ u * (g ^ k) ^ w := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (p : ℤ) u, mul_comm k w, huw, zpow_one]
  rw [zpow_natCast, hgp, one_zpow, one_mul] at hg
  rw [hg]
  exact zpow_apply_of_fixed hk w

end Fix

end CFSG.LieType.SeitzGeneration
