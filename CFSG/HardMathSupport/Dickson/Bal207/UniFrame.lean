module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section Abstract

variable {k : Type*} [Field k] {σ : k →+* k} {M : Type*} [AddCommGroup M] [Module k M]

theorem frame_one_add_add_sq {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hω1)

theorem frame_three_ne_zero {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : (3 : k) ≠ 0 := by
  intro h3
  have hs := frame_one_add_add_sq hω hω1
  have h2 : (ω - 1) ^ 2 = 0 := by linear_combination hs - ω * h3
  exact hω1 (sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2))

@[expose] noncomputable def eigComp (x : M →ₗ[k] M) (c : k) (w : M) : M :=
  (3 : k)⁻¹ • (w + c ^ 2 • x w + c • x (x w))

theorem apply_eigComp {x : M →ₗ[k] M} (hx3 : ∀ v, x (x (x v)) = v) {c : k} (hc : c ^ 3 = 1)
    (w : M) : x (eigComp x c w) = c • eigComp x c w := by
  simp only [eigComp, map_smul, map_add, hx3]
  match_scalars <;> first | ring1 | linear_combination (-(3 : k)⁻¹) * hc

theorem eigComp_add (x : M →ₗ[k] M) {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (w : M) :
    eigComp x 1 w + eigComp x ω w + eigComp x (ω ^ 2) w = w := by
  have hs := frame_one_add_add_sq hω hω1
  have h33 : (3 : k)⁻¹ * 3 = 1 := inv_mul_cancel₀ (frame_three_ne_zero hω hω1)
  simp only [eigComp]
  match_scalars <;> first | linear_combination h33 |
    linear_combination (3 : k)⁻¹ * hs + (3 : k)⁻¹ * ω * hω | linear_combination (3 : k)⁻¹ * hs

theorem eigComp_eigen {x y : M →ₗ[k] M} (hxy : ∀ v, x (y v) = y (x v)) {w : M} {μ : k}
    (hw : y w = μ • w) (c : k) : y (eigComp x c w) = μ • eigComp x c w := by
  simp only [eigComp, map_smul, map_add, ← hxy, hw]
  module

variable {B : M →ₛₗ[σ] M →ₗ[k] k}

theorem form_eigComp_eq_zero {x : M →ₗ[k] M} (hxB : ∀ u v, B (x u) (x v) = B u v)
    (hx3 : ∀ v, x (x (x v)) = v) {b : M} {μ : k} (hb : x b = μ • b) {w : M} (hw : B b w = 0)
    (c : k) : B b (eigComp x c w) = 0 := by
  have h1 : B b (x w) = 0 := by
    rw [← hx3 b, hxB, hb, map_smul, hb, smul_smul, map_smulₛₗ, LinearMap.smul_apply, hw,
      smul_zero]
  have h2 : B b (x (x w)) = 0 := by
    rw [← hx3 b, hxB, hxB, hb, map_smulₛₗ, LinearMap.smul_apply, hw, smul_zero]
  simp only [eigComp, map_smul, map_add, hw, h1, h2, smul_zero, add_zero]

theorem form_eq_zero_of_eigen {x : M →ₗ[k] M} (hxB : ∀ u v, B (x u) (x v) = B u v) {u v : M}
    {c d : k} (hu : x u = c • u) (hv : x v = d • v) (hcd : σ c * d ≠ 1) : B u v = 0 := by
  have h := hxB u v
  rw [hu, hv] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h
  have h' : (σ c * d - 1) * B u v = 0 := by linear_combination h
  exact (mul_eq_zero.1 h').resolve_left (sub_ne_zero.2 hcd)

theorem form_add_three {x : M →ₗ[k] M} (hxB : ∀ u v, B (x u) (x v) = B u v) {ω : k}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2) {u₀ u₁ u₂ : M} (h₀ : x u₀ = (1 : k) • u₀)
    (h₁ : x u₁ = ω • u₁) (h₂ : x u₂ = ω ^ 2 • u₂) :
    B (u₀ + u₁ + u₂) (u₀ + u₁ + u₂) = B u₀ u₀ + B u₁ u₁ + B u₂ u₂ := by
  have hω2 : ω ^ 2 ≠ 1 := fun e => hω1 (by linear_combination hω - ω * e)
  have hω4 : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * hω
  have hσ2 : σ (ω ^ 2) = ω := by rw [map_pow, hσω, ← pow_mul]; linear_combination ω * hω
  have e01 := form_eq_zero_of_eigen hxB h₀ h₁ (by rwa [map_one, one_mul])
  have e02 := form_eq_zero_of_eigen hxB h₀ h₂ (by rwa [map_one, one_mul])
  have e10 := form_eq_zero_of_eigen hxB h₁ h₀ (by rwa [hσω, mul_one])
  have e12 := form_eq_zero_of_eigen hxB h₁ h₂ (by rwa [hσω, hω4])
  have e20 := form_eq_zero_of_eigen hxB h₂ h₀ (by rwa [hσ2, mul_one])
  have e21 := form_eq_zero_of_eigen hxB h₂ h₁ (by rw [hσ2, ← sq]; exact hω2)
  simp only [map_add, LinearMap.add_apply, e01, e02, e10, e12, e20, e21]
  ring

theorem exists_eigComp_ne_zero {x : M →ₗ[k] M} (hxB : ∀ u v, B (x u) (x v) = B u v)
    (hx3 : ∀ v, x (x (x v)) = v) {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2)
    {w : M} (hw : B w w ≠ 0) : ∃ c : k, c ^ 3 = 1 ∧ B (eigComp x c w) (eigComp x c w) ≠ 0 := by
  have hω6 : (ω ^ 2) ^ 3 = 1 := by linear_combination (ω ^ 3 + 1) * hω
  have hsum := eigComp_add x hω hω1 w
  rw [← hsum, form_add_three hxB hω hω1 hσω (apply_eigComp hx3 (one_pow 3) w)
    (apply_eigComp hx3 hω w) (apply_eigComp hx3 hω6 w)] at hw
  by_cases h₀ : B (eigComp x 1 w) (eigComp x 1 w) = 0
  · by_cases h₁ : B (eigComp x ω w) (eigComp x ω w) = 0
    · refine ⟨ω ^ 2, hω6, fun h₂ => hw ?_⟩
      rw [h₀, h₁, h₂, add_zero, add_zero]
    · exact ⟨ω, hω, h₁⟩
  · exact ⟨1, one_pow 3, h₀⟩

theorem exists_common_eigen_perp {ω : k} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2)
    (S : Finset (M →ₗ[k] M)) (hSB : ∀ x ∈ S, ∀ u v, B (x u) (x v) = B u v)
    (hS3 : ∀ x ∈ S, ∀ v, x (x (x v)) = v) (hSc : ∀ x ∈ S, ∀ y ∈ S, ∀ v, x (y v) = y (x v))
    {r : ℕ} (b : Fin r → M) (hbS : ∀ i, ∀ x ∈ S, ∃ μ : k, x (b i) = μ • b i) {w : M}
    (hw : B w w ≠ 0) (hwb : ∀ i, B (b i) w = 0) :
    ∃ v : M, B v v ≠ 0 ∧ (∀ i, B (b i) v = 0) ∧ ∀ x ∈ S, ∃ c : k, x v = c • v := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨w, hw, hwb, fun x hx => by simp at hx⟩
  | @insert x T hxT ih =>
    have hx := Finset.mem_insert_self x T
    have hT : ∀ y ∈ T, y ∈ insert x T := fun y hy => Finset.mem_insert_of_mem hy
    obtain ⟨v, hv, hvb, hvT⟩ := ih (fun y hy => hSB y (hT y hy)) (fun y hy => hS3 y (hT y hy))
      (fun y hy z hz => hSc y (hT y hy) z (hT z hz)) (fun i y hy => hbS i y (hT y hy))
    obtain ⟨c, hc, hcv⟩ := exists_eigComp_ne_zero (hSB x hx) (hS3 x hx) hω hω1 hσω hv
    refine ⟨eigComp x c v, hcv, fun i => ?_, fun y hy => ?_⟩
    · obtain ⟨μ, hμ⟩ := hbS i x hx
      exact form_eigComp_eq_zero (hSB x hx) (hS3 x hx) hμ (hvb i) c
    · rcases Finset.mem_insert.1 hy with hyx | hyT
      · rw [hyx]
        exact ⟨c, apply_eigComp (hS3 x hx) hc v⟩
      · obtain ⟨μ, hμ⟩ := hvT y hyT
        exact ⟨μ, eigComp_eigen (hSc x hx y hy) hμ c⟩

variable [FiniteDimensional k M]

theorem exists_norm_one_common_eigen (hB : B.IsSymm) (hBl : B.SeparatingLeft) {c₀ : k}
    (hc₀ : σ c₀ ≠ c₀) (hnorm : ∀ d : k, σ d = d → d ≠ 0 → ∃ c, σ c * c = d) {ω : k}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2) (S : Finset (M →ₗ[k] M))
    (hSB : ∀ x ∈ S, ∀ u v, B (x u) (x v) = B u v) (hS3 : ∀ x ∈ S, ∀ v, x (x (x v)) = v)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, ∀ v, x (y v) = y (x v)) {r : ℕ} (hr : r < Module.finrank k M)
    (b : Fin r → M) (hb : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (hbS : ∀ i, ∀ x ∈ S, ∃ μ : k, x (b i) = μ • b i) :
    ∃ v : M, B v v = 1 ∧ (∀ i, B (b i) v = 0) ∧ ∀ x ∈ S, ∃ c : k, x v = c • v := by
  obtain ⟨u, hu, hub⟩ := exists_norm_one_perp_of_lt hB hBl hc₀ hnorm hr b hb
  obtain ⟨v, hv, hvb, hvS⟩ := exists_common_eigen_perp hω hω1 hσω S hSB hS3 hSc b hbS
    (by rw [hu]; exact one_ne_zero) hub
  have hd : σ (B v v) = B v v := hB.eq v v
  obtain ⟨c, hc⟩ := hnorm (B v v)⁻¹ (by rw [map_inv₀, hd]) (inv_ne_zero hv)
  refine ⟨c • v, ?_, fun i => ?_, fun x hx => ?_⟩
  · have e : B (c • v) (c • v) = σ c * c * B v v := by
      simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    rw [e, hc, inv_mul_cancel₀ hv]
  · rw [map_smul, hvb, smul_zero]
  · obtain ⟨μ, hμ⟩ := hvS x hx
    exact ⟨μ, by rw [map_smul, hμ, smul_comm]⟩

theorem exists_orthonormal_common_eigen (hB : B.IsSymm) (hBl : B.SeparatingLeft) {c₀ : k}
    (hc₀ : σ c₀ ≠ c₀) (hnorm : ∀ d : k, σ d = d → d ≠ 0 → ∃ c, σ c * c = d) {ω : k}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hσω : σ ω = ω ^ 2) (S : Finset (M →ₗ[k] M))
    (hSB : ∀ x ∈ S, ∀ u v, B (x u) (x v) = B u v) (hS3 : ∀ x ∈ S, ∀ v, x (x (x v)) = v)
    (hSc : ∀ x ∈ S, ∀ y ∈ S, ∀ v, x (y v) = y (x v)) {r : ℕ} (hr : r ≤ Module.finrank k M) :
    ∃ b : Fin r → M, (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      ∀ i, ∀ x ∈ S, ∃ μ : k, x (b i) = μ • b i := by
  induction r with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    obtain ⟨b, hb, hbS⟩ := ih (by omega)
    obtain ⟨v, hv, hbv, hvS⟩ :=
      exists_norm_one_common_eigen hB hBl hc₀ hnorm hω hω1 hσω S hSB hS3 hSc (by omega) b hb hbS
    have hvb : ∀ i, B v (b i) = 0 := fun i => by rw [← hB.eq (b i) v, hbv i, map_zero]
    refine ⟨Fin.cons v b, fun i j => ?_, fun i => ?_⟩
    · cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp [hv, hbv, hvb, hb, (Fin.succ_ne_zero _).symm]
    · cases i using Fin.cases with
      | zero => simpa only [Fin.cons_zero] using hvS
      | succ i => simpa only [Fin.cons_succ] using hbS i

end Abstract

section Matrix

variable {ℓ f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem exists_cube_root_bar (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ h.bar ω = ω ^ 2 := by
  haveI := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht⟩ := h3
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul']
    have h1 : 3 ∣ ℓ ^ f * (ℓ ^ f + 1) := Dvd.dvd.mul_left ⟨t, ht⟩ _
    have h2 := Nat.dvd_sub h1 ⟨t, ht⟩
    have e : ℓ ^ f * (ℓ ^ f + 1) - (ℓ ^ f + 1) = (ℓ ^ f) ^ 2 - 1 := by
      rw [mul_add, mul_one, sq, add_comm (ℓ ^ f) 1, Nat.add_sub_add_right]
    rwa [e] at h2
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hω : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  refine ⟨(u : K), hω, fun h1 => ?_, ?_⟩
  · have hu1 : u = 1 := Units.ext h1
    rw [hu1, orderOf_one] at hu
    norm_num at hu
  · have hq : ℓ ^ f = 3 * (t - 1) + 2 := by omega
    rw [h.bar_apply, hq, pow_add, pow_mul, hω, one_pow, one_mul]

theorem exists_unitary_isDiag_conj (h : UnitaryFieldData ℓ f K) (h3 : 3 ∣ ℓ ^ f + 1)
    (E : Set (GL (Fin n) K))
    (hEU : ∀ x ∈ E, x ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1) :
    ∃ P ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      ∀ x ∈ E, ((P⁻¹ * x * P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag := by
  classical
  haveI := h.finite
  obtain ⟨ω, hω, hω1, hσω⟩ := exists_cube_root_bar h h3
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  have hnorm : ∀ d : K, h.bar d = d → d ≠ 0 → ∃ c, h.bar c * c = d := fun d hd _ => by
    obtain ⟨c, hc⟩ := h.normHom_surjective ⟨d, hd⟩
    exact ⟨c, by rw [mul_comm]; exact congrArg Subtype.val hc⟩
  have hG1 : ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := Units.val_one
  have hB : (gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).IsSymm :=
    gramForm_isSymm h (by
      rw [hG1, Matrix.map_one _ (map_zero h.bar) (map_one h.bar), transpose_one])
  have hBl : (gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).SeparatingLeft :=
    gramForm_separatingLeft h (by rw [hG1, det_one]; exact one_ne_zero)
  have hEfin : E.Finite := Set.toFinite E
  set S : Finset (Module.End K (Fin n → K)) :=
    hEfin.toFinset.image fun x : GL (Fin n) K => (x : Matrix (Fin n) (Fin n) K).mulVecLin
    with hS
  have hmemS : ∀ y ∈ S, ∃ x ∈ E, y = (x : Matrix (Fin n) (Fin n) K).mulVecLin := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨x, hEfin.mem_toFinset.1 hx, rfl⟩
  have hSB : ∀ y ∈ S, ∀ u v, gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) (y u)
      (y v) = gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) u v := by
    intro y hy u v
    obtain ⟨x, hx, rfl⟩ := hmemS y hy
    exact (gramForm_isometry_iff h _ (x : Matrix (Fin n) (Fin n) K)).2 (hEU x hx) u v
  have hS3 : ∀ y ∈ S, ∀ v, y (y (y v)) = v := by
    intro y hy v
    obtain ⟨x, hx, rfl⟩ := hmemS y hy
    have hx3 : (x : Matrix (Fin n) (Fin n) K) * ((x : Matrix (Fin n) (Fin n) K) * x) = 1 := by
      have := congrArg Units.val (hE3 x hx)
      rwa [Units.val_pow_eq_pow_val, pow_three, Units.val_one] at this
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hx3, Matrix.one_mulVec]
  have hSc : ∀ y ∈ S, ∀ z ∈ S, ∀ v, y (z v) = z (y v) := by
    intro y hy z hz v
    obtain ⟨x, hx, rfl⟩ := hmemS y hy
    obtain ⟨x', hx', rfl⟩ := hmemS z hz
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, hEc x hx x' hx', Units.val_mul]
  obtain ⟨b, hb, hbS⟩ := exists_orthonormal_common_eigen hB hBl hc₀ hnorm hω hω1 hσω S hSB hS3
    hSc (r := n) (Module.finrank_fin_fun K).ge
  set Pm : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => b j i with hPm
  have hPP : (Pm.map h.bar)ᵀ * Pm = 1 := by
    ext i j
    have hij := hb i j
    rw [gramForm_apply, hG1, Matrix.one_mulVec] at hij
    rw [Matrix.one_apply, ← hij]
    rfl
  have hPP' : Pm * (Pm.map h.bar)ᵀ = 1 := mul_eq_one_comm.1 hPP
  refine ⟨⟨Pm, (Pm.map h.bar)ᵀ, hPP', hPP⟩, ?_, fun x hx => ?_⟩
  · show (Pm.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Pm =
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hG1, Matrix.mul_one, hPP]
  · have hxS : (x : Matrix (Fin n) (Fin n) K).mulVecLin ∈ S :=
      Finset.mem_image_of_mem _ (hEfin.mem_toFinset.2 hx)
    have hμ' : ∀ j, ∃ μ : K, (x : Matrix (Fin n) (Fin n) K) *ᵥ b j = μ • b j := fun j => by
      obtain ⟨μ, hμ⟩ := hbS j _ hxS
      exact ⟨μ, by rwa [Matrix.mulVecLin_apply] at hμ⟩
    choose μ hμ using hμ'
    have hxP : (x : Matrix (Fin n) (Fin n) K) * Pm = Pm * Matrix.diagonal μ := by
      ext i j
      rw [Matrix.mul_diagonal]
      have hj := congrFun (hμ j) i
      rw [Pi.smul_apply, smul_eq_mul] at hj
      rw [Matrix.mul_apply]
      calc ∑ k, (x : Matrix (Fin n) (Fin n) K) i k * Pm k j =
          ((x : Matrix (Fin n) (Fin n) K) *ᵥ b j) i := rfl
        _ = Pm i j * μ j := by rw [hj, mul_comm]; rfl
    show ((Pm.map h.bar)ᵀ * (x : Matrix (Fin n) (Fin n) K) * Pm).IsDiag
    rw [Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    exact Matrix.isDiag_diagonal μ

end Matrix

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
