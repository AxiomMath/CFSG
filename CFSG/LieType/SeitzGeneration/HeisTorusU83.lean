module

public import CFSG.LieType.SeitzGeneration.HeisTorusU82

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def ug83_adj (h : UnitaryFieldData ℓ f K) {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) : Matrix (Fin k) (Fin m) K :=
  (A.map h.bar)ᵀ

section Adj

variable (h : UnitaryFieldData ℓ f K) {m k l : ℕ}

theorem ug83_adj_apply (A : Matrix (Fin m) (Fin k) K) (i : Fin k) (j : Fin m) :
    ug83_adj h A i j = h.bar (A j i) :=
  rfl

theorem ug83_adj_mul (A : Matrix (Fin m) (Fin k) K) (B : Matrix (Fin k) (Fin l) K) :
    ug83_adj h (A * B) = ug83_adj h B * ug83_adj h A := by
  simp only [ug83_adj, Matrix.map_mul, Matrix.transpose_mul]

theorem ug83_adj_adj (A : Matrix (Fin m) (Fin k) K) : ug83_adj h (ug83_adj h A) = A := by
  ext i j
  simp [ug83_adj_apply, h.bar_bar]

theorem ug83_adj_one : ug83_adj h (1 : Matrix (Fin m) (Fin m) K) = 1 := by
  simp [ug83_adj, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]

theorem ug83_adj_add (A B : Matrix (Fin m) (Fin k) K) :
    ug83_adj h (A + B) = ug83_adj h A + ug83_adj h B := by
  ext i j
  simp [ug83_adj_apply]

theorem ug83_adj_sub (A B : Matrix (Fin m) (Fin k) K) :
    ug83_adj h (A - B) = ug83_adj h A - ug83_adj h B := by
  ext i j
  simp [ug83_adj_apply]

@[expose] noncomputable def ug83_P (w : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  vecMulVec w fun i => h.bar (w i)

theorem ug83_P_apply (w : Fin m → K) (i j : Fin m) : ug83_P h w i j = w i * h.bar (w j) :=
  rfl

theorem ug83_hom_eq {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) (σ : K) :
    unitaryHomology h w σ = 1 + (σ - 1) • ug83_P h w := by
  rw [unitaryHomology, hw, div_one]
  rfl

theorem ug83_P_mul_P {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) :
    ug83_P h w * ug83_P h w = ug83_P h w := by
  rw [ug83_P, vecMulVec_mul_vecMulVec]
  have : (fun i => h.bar (w i)) ⬝ᵥ w = 1 := hw
  rw [this, one_smul]

theorem ug83_hom_mul {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) (σ τ : K) :
    unitaryHomology h w σ * unitaryHomology h w τ = unitaryHomology h w (σ * τ) := by
  have hP := ug83_P_mul_P h hw
  rw [ug83_hom_eq h hw, ug83_hom_eq h hw, ug83_hom_eq h hw]
  simp only [mul_add, add_mul, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, hP]
  module

theorem ug83_hom_one {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) :
    unitaryHomology h w 1 = 1 := by
  rw [ug83_hom_eq h hw]
  simp

theorem ug83_exists_unit_hom {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) {σ : K}
    (hσ : σ ≠ 0) :
    ∃ g : GL (Fin m) K, (g : Matrix (Fin m) (Fin m) K) = unitaryHomology h w σ :=
  ⟨⟨unitaryHomology h w σ, unitaryHomology h w σ⁻¹,
    by rw [ug83_hom_mul h hw, mul_inv_cancel₀ hσ, ug83_hom_one h hw],
    by rw [ug83_hom_mul h hw, inv_mul_cancel₀ hσ, ug83_hom_one h hw]⟩, rfl⟩

theorem ug83_vecMul_adj (M : Matrix (Fin m) (Fin k) K) (x : Fin k → K) :
    (fun j => h.bar (x j)) ᵥ* ug83_adj h M = fun i => h.bar ((M *ᵥ x) i) := by
  funext i
  simp only [vecMul, dotProduct, ug83_adj_apply, mulVec, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem ug83_mul_P_mul_adj (M : Matrix (Fin k) (Fin m) K) (w : Fin m → K) :
    M * ug83_P h w * ug83_adj h M = ug83_P h (M *ᵥ w) := by
  simp only [ug83_P]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ug83_vecMul_adj]

theorem ug83_norm_mulVec (M : Matrix (Fin k) (Fin m) K) (hM : ug83_adj h M * M = 1)
    (w : Fin m → K) :
    ∑ i, h.bar ((M *ᵥ w) i) * (M *ᵥ w) i = ∑ j, h.bar (w j) * w j := by
  have h1 : ∑ i, h.bar ((M *ᵥ w) i) * (M *ᵥ w) i =
      (fun i => h.bar ((M *ᵥ w) i)) ⬝ᵥ (M *ᵥ w) := rfl
  rw [h1, ← ug83_vecMul_adj h M w, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec]
  rfl

theorem ug83_conj_hom (g : Matrix (Fin m) (Fin m) K) (hg : ug83_adj h g * g = 1)
    {w : Fin m → K} (hw : ∑ i, h.bar (w i) * w i = 1) (σ : K) :
    g * unitaryHomology h w σ * ug83_adj h g = unitaryHomology h (g *ᵥ w) σ := by
  have hgg : g * ug83_adj h g = 1 := mul_eq_one_comm.2 hg
  have hw' : ∑ i, h.bar ((g *ᵥ w) i) * (g *ᵥ w) i = 1 := by
    rw [ug83_norm_mulVec h g hg w, hw]
  rw [ug83_hom_eq h hw, ug83_hom_eq h hw', Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hgg,
    Matrix.mul_smul, Matrix.smul_mul, ug83_mul_P_mul_adj]

theorem ug83_hom_single (j : Fin m) (ρ : K) :
    unitaryHomology h (Pi.single j 1 : Fin m → K) ρ =
      diagonal (Function.update (1 : Fin m → K) j ρ) := by
  have hw : ∑ i, h.bar ((Pi.single j 1 : Fin m → K) i) * (Pi.single j 1 : Fin m → K) i = 1 := by
    simp [Pi.single_apply]
  rw [ug83_hom_eq h hw]
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases haj : a = j
    · subst haj
      simp [ug83_P_apply, Pi.single_apply, Matrix.one_apply]
    · simp [ug83_P_apply, Pi.single_apply, Matrix.one_apply, haj]
  · simp [ug83_P_apply, Pi.single_apply, Matrix.one_apply, hab]
    rintro rfl rfl
    exact absurd rfl hab

end Adj

def ug83_Mem {n : ℕ} (X : Subgroup (GL (Fin n) K)) (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ g ∈ X, (g : Matrix (Fin n) (Fin n) K) = M

theorem ug83_Mem.mul {n : ℕ} {X : Subgroup (GL (Fin n) K)} {A B : Matrix (Fin n) (Fin n) K}
    (hA : ug83_Mem X A) (hB : ug83_Mem X B) : ug83_Mem X (A * B) := by
  obtain ⟨a, ha, rfl⟩ := hA
  obtain ⟨b, hb, rfl⟩ := hB
  exact ⟨a * b, mul_mem ha hb, rfl⟩

theorem ug83_adj_mul_self_of_mem (h : UnitaryFieldData ℓ f K) {n : ℕ} {X : Subgroup (GL (Fin n) K)}
    (hXU : X ≤ primeFormUnitary h 1) {g : GL (Fin n) K} (hg : g ∈ X) :
    ug83_adj h (g : Matrix (Fin n) (Fin n) K) * g = 1 := by
  have := hXU hg
  rw [mem_primeFormUnitary, Matrix.mul_one] at this
  exact this

theorem ug83_coe_inv_eq_adj (h : UnitaryFieldData ℓ f K) {n : ℕ} {g : GL (Fin n) K}
    (hg : ug83_adj h (g : Matrix (Fin n) (Fin n) K) * g = 1) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ug83_adj h (g : Matrix (Fin n) (Fin n) K) := by
  calc ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = (ug83_adj h (g : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [hg, Matrix.one_mul]
    _ = ug83_adj h (g : Matrix (Fin n) (Fin n) K) := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

theorem ug83_Mem_conj (h : UnitaryFieldData ℓ f K) {n : ℕ} {X : Subgroup (GL (Fin n) K)}
    (hXU : X ≤ primeFormUnitary h 1) {g : GL (Fin n) K} (hg : g ∈ X)
    {M : Matrix (Fin n) (Fin n) K} (hM : ug83_Mem X M) :
    ug83_Mem X ((g : Matrix (Fin n) (Fin n) K) * M *
      ug83_adj h (g : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨a, ha, rfl⟩ := hM
  refine ⟨g * a * g⁻¹, mul_mem (mul_mem hg ha) (inv_mem hg), ?_⟩
  rw [Units.val_mul, Units.val_mul, ug83_coe_inv_eq_adj h (ug83_adj_mul_self_of_mem h hXU hg)]

theorem ug83_Mem_diagonal (h : UnitaryFieldData ℓ f K) {n : ℕ} {X : Subgroup (GL (Fin n) K)}
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    (t : Fin n → K) (ht : ∀ i, h.bar (t i) * t i = 1) : ug83_Mem X (diagonal t) := by
  have ht0 : ∀ i, t i ≠ 0 := fun i h0 => by simpa [h0] using ht i
  let g : GL (Fin n) K :=
    ⟨diagonal t, diagonal fun i => (t i)⁻¹,
      by rw [diagonal_mul_diagonal]; simp [ht0, diagonal_one],
      by rw [diagonal_mul_diagonal]; simp [ht0, diagonal_one]⟩
  refine ⟨g, hD g ?_ ⟨t, rfl⟩, rfl⟩
  rw [mem_primeFormUnitary]
  change ((diagonal t).map h.bar)ᵀ * 1 * diagonal t = 1
  rw [diagonal_map (map_zero h.bar), diagonal_transpose, Matrix.mul_one, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  exact ht i

theorem ug83_exists_orderOf (h : UnitaryFieldData ℓ f K) : ∃ a : K, orderOf a = ℓ ^ f + 1 := by
  have hfin := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Units.map h.normHom).ker)
  have hord : orderOf g = ℓ ^ f + 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, h.card_ker_normUnits_and_surjective.1]
  refine ⟨(((g : Kˣ)) : K), ?_⟩
  rw [orderOf_units, Subgroup.orderOf_coe, hord]

theorem ug83_norm_of_orderOf (h : UnitaryFieldData ℓ f K) {a : K} (ha : orderOf a = ℓ ^ f + 1) :
    h.bar a * a = 1 := by
  rw [h.bar_apply, ← pow_succ, ← ha, pow_orderOf_eq_one]

theorem ug83_exists_norm_eq (h : UnitaryFieldData ℓ f K) {t : K} (ht : t ∈ h.fixedField) :
    ∃ d : K, h.bar d * d = t := by
  obtain ⟨d, hd⟩ := h.normHom_surjective ⟨t, ht⟩
  refine ⟨d, ?_⟩
  have := congrArg Subtype.val hd
  simpa [UnitaryFieldData.norm, mul_comm] using this

theorem ug83_exists_rho (h : UnitaryFieldData ℓ f K) (hq : 4 ≤ ℓ ^ f) :
    ∃ ρ : K, h.bar ρ * ρ = 1 ∧ ρ ≠ 1 ∧ h.bar (ρ - 1) * (ρ - 1) ≠ 1 := by
  classical
  obtain ⟨σ, hσ⟩ := ug83_exists_orderOf h
  have hσN := ug83_norm_of_orderOf h hσ
  let P : Polynomial K :=
    Polynomial.X ^ 3 - Polynomial.C 2 * Polynomial.X ^ 2 + Polynomial.C 2 * Polynomial.X - 1
  have hP0 : P ≠ 0 := by
    intro h0
    have := congrArg (Polynomial.eval 0) h0
    simp [P] at this
  have hPdeg : P.natDegree < Fintype.card (Fin 4) := by
    have : P.natDegree ≤ 3 := by
      simp only [P]
      compute_degree
    simp only [Fintype.card_fin]
    omega
  have hinj : Function.Injective (fun i : Fin 4 => σ ^ (i : ℕ)) := by
    intro i j hij
    have hlt : ∀ i : Fin 4, (i : ℕ) ∈ Set.Iio (orderOf σ) := fun i => by
      simp only [Set.mem_Iio, hσ]
      omega
    exact Fin.ext (pow_injOn_Iio_orderOf (hlt i) (hlt j) hij)
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, P.eval (σ ^ (i : ℕ)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hP0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hinj hcon hPdeg)
  have hN : h.bar (σ ^ (i : ℕ)) * σ ^ (i : ℕ) = 1 := by
    rw [map_pow, ← mul_pow, hσN, one_pow]
  refine ⟨σ ^ (i : ℕ), hN, ?_, ?_⟩
  · intro h1
    apply hi
    rw [h1]
    simp [P]
  · intro hcon
    apply hi
    simp only [P, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    rw [map_sub, map_one] at hcon
    linear_combination ((σ ^ (i : ℕ) - 1) * (σ ^ (i : ℕ) - 1)) * hN -
      ((σ ^ (i : ℕ) - 1) * σ ^ (i : ℕ)) * hcon

section Frame

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

def ug83_frame (p₀ p₁ : Fin n → K) : Matrix (Fin n) (Fin 2) K :=
  Matrix.of fun i x => ![p₀ i, p₁ i] x

theorem ug83_frame_mulVec (p₀ p₁ : Fin n → K) (w : Fin 2 → K) :
    ug83_frame p₀ p₁ *ᵥ w = fun i => p₀ i * w 0 + p₁ i * w 1 := by
  funext i
  simp [ug83_frame, mulVec, dotProduct, Fin.sum_univ_two]

theorem ug83_adj_frame_mul_frame {p₀ p₁ : Fin n → K} (h00 : ∑ i, h.bar (p₀ i) * p₀ i = 1)
    (h11 : ∑ i, h.bar (p₁ i) * p₁ i = 1) (h01 : ∑ i, h.bar (p₀ i) * p₁ i = 0) :
    ug83_adj h (ug83_frame p₀ p₁) * ug83_frame p₀ p₁ = 1 := by
  have h10 : ∑ i, h.bar (p₁ i) * p₀ i = 0 := by
    have := congrArg h.bar h01
    simpa [map_sum, map_mul, h.bar_bar, mul_comm] using this
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.mul_apply, ug83_adj_apply, ug83_frame, h00, h11, h01, h10]

@[expose] noncomputable def ug83_emb (F : Matrix (Fin n) (Fin 2) K)
    (hF : ug83_adj h F * F = 1) : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin n) (Fin n) K where
  toFun y := 1 + F * (y - 1) * ug83_adj h F
  map_one' := by simp
  map_mul' y y' := by
    have e : F * (y - 1) * ug83_adj h F * (F * (y' - 1) * ug83_adj h F) =
        F * ((y - 1) * (y' - 1)) * ug83_adj h F := by
      calc F * (y - 1) * ug83_adj h F * (F * (y' - 1) * ug83_adj h F)
          = F * (y - 1) * (ug83_adj h F * F) * (y' - 1) * ug83_adj h F := by
            simp only [Matrix.mul_assoc]
        _ = F * ((y - 1) * (y' - 1)) * ug83_adj h F := by
            rw [hF, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
    have e2 : y * y' - 1 = (y - 1) + (y' - 1) + (y - 1) * (y' - 1) := by noncomm_ring
    rw [e2]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, e]
    abel

theorem ug83_emb_apply (F : Matrix (Fin n) (Fin 2) K) (hF : ug83_adj h F * F = 1)
    (y : Matrix (Fin 2) (Fin 2) K) : ug83_emb h F hF y = 1 + F * (y - 1) * ug83_adj h F :=
  rfl

theorem ug83_emb_hom {F : Matrix (Fin n) (Fin 2) K} (hF : ug83_adj h F * F = 1)
    {w : Fin 2 → K} (hw : ∑ i, h.bar (w i) * w i = 1) (σ : K) :
    ug83_emb h F hF (unitaryHomology h w σ) = unitaryHomology h (F *ᵥ w) σ := by
  have hw' : ∑ i, h.bar ((F *ᵥ w) i) * (F *ᵥ w) i = 1 := by
    rw [ug83_norm_mulVec h F hF w, hw]
  rw [ug83_emb_apply, ug83_hom_eq h hw, ug83_hom_eq h hw', add_sub_cancel_left, Matrix.mul_smul,
    Matrix.smul_mul, ug83_mul_P_mul_adj]

theorem ug83_adj_emb {F : Matrix (Fin n) (Fin 2) K} (hF : ug83_adj h F * F = 1)
    (y : Matrix (Fin 2) (Fin 2) K) :
    ug83_adj h (ug83_emb h F hF y) = ug83_emb h F hF (ug83_adj h y) := by
  simp only [ug83_emb_apply, ug83_adj_add, ug83_adj_one, ug83_adj_mul, ug83_adj_adj,
    ug83_adj_sub, Matrix.mul_assoc]

theorem ug83_adj_mul_emb_mul {F : Matrix (Fin n) (Fin 2) K} (hF : ug83_adj h F * F = 1)
    (y : Matrix (Fin 2) (Fin 2) K) : ug83_adj h F * ug83_emb h F hF y * F = y := by
  calc ug83_adj h F * ug83_emb h F hF y * F
      = ug83_adj h F * F + (ug83_adj h F * F) * (y - 1) * (ug83_adj h F * F) := by
        simp only [ug83_emb_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
          Matrix.mul_assoc]
    _ = y := by rw [hF]; simp

theorem ug83_det_emb {F : Matrix (Fin n) (Fin 2) K} (hF : ug83_adj h F * F = 1)
    (y : Matrix (Fin 2) (Fin 2) K) : (ug83_emb h F hF y).det = y.det := by
  rw [ug83_emb_apply, Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hF,
    Matrix.mul_one, add_sub_cancel]

@[expose] noncomputable def ug83_embGL (F : Matrix (Fin n) (Fin 2) K) (hF : ug83_adj h F * F = 1) :
    GL (Fin 2) K →* GL (Fin n) K :=
  Units.map (ug83_emb h F hF)

theorem ug83_coe_embGL (F : Matrix (Fin n) (Fin 2) K) (hF : ug83_adj h F * F = 1)
    (y : GL (Fin 2) K) :
    (ug83_embGL h F hF y : Matrix (Fin n) (Fin n) K) = ug83_emb h F hF y :=
  rfl

end Frame

@[expose] def TwoHomologiesSU2 (h : UnitaryFieldData ℓ f K) : Prop :=
  4 ≤ ℓ ^ f → 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1) →
  ∀ (X : Subgroup (GL (Fin 2) K)) {w u : Fin 2 → K} {σ ρ : K},
    h.bar (w 0) * w 0 + h.bar (w 1) * w 1 ≠ 0 →
    h.bar (u 0) * u 0 + h.bar (u 1) * u 1 ≠ 0 →
    h.bar (w 0) * u 0 + h.bar (w 1) * u 1 ≠ 0 → w 0 * u 1 - w 1 * u 0 ≠ 0 →
    orderOf σ = ℓ ^ f + 1 → orderOf ρ = ℓ ^ f + 1 →
    (∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h w σ) →
    (∃ g ∈ X, (g : Matrix (Fin 2) (Fin 2) K) = unitaryHomology h u ρ) →
    unitarySU ℓ f K 2 ≤ X

theorem ug83_plane (h : UnitaryFieldData ℓ f K) (h82 : TwoHomologiesSU2 h) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) {n : ℕ} (X : Subgroup (GL (Fin n) K))
    {p₀ p₁ : Fin n → K} (hF : ug83_adj h (ug83_frame p₀ p₁) * ug83_frame p₀ p₁ = 1)
    {α β : K} (hα : α ≠ 0) (hβ : β ≠ 0) (hαβ : h.bar α * α + h.bar β * β = 1)
    (hX1 : ∀ σ, h.bar σ * σ = 1 → ug83_Mem X (unitaryHomology h p₀ σ))
    (hX2 : ∀ ρ, h.bar ρ * ρ = 1 →
      ug83_Mem X (unitaryHomology h (fun i => p₀ i * α + p₁ i * β) ρ)) :
    ∀ y ∈ unitarySU ℓ f K 2, ug83_embGL h (ug83_frame p₀ p₁) hF y ∈ X := by
  obtain ⟨σ, hσ⟩ := ug83_exists_orderOf h
  have hσN := ug83_norm_of_orderOf h hσ
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    simp at hσN
  have hw1 : ∑ i, h.bar ((![1, 0] : Fin 2 → K) i) * (![1, 0] : Fin 2 → K) i = 1 := by
    simp [Fin.sum_univ_two]
  have hu1 : ∑ i, h.bar ((![α, β] : Fin 2 → K) i) * (![α, β] : Fin 2 → K) i = 1 := by
    simpa [Fin.sum_univ_two] using hαβ
  have hFw : ug83_frame p₀ p₁ *ᵥ (![1, 0] : Fin 2 → K) = p₀ := by
    rw [ug83_frame_mulVec]
    funext i
    simp
  have hFu : ug83_frame p₀ p₁ *ᵥ (![α, β] : Fin 2 → K) = fun i => p₀ i * α + p₁ i * β := by
    rw [ug83_frame_mulVec]
    simp
  have key : unitarySU ℓ f K 2 ≤ X.comap (ug83_embGL h (ug83_frame p₀ p₁) hF) := by
    refine h82 hq he _ (w := ![1, 0]) (u := ![α, β]) (σ := σ) (ρ := σ) ?_ ?_ ?_ ?_ hσ hσ ?_ ?_
    · simp
    · simp [hαβ]
    · simpa using hα
    · simpa using hβ
    · obtain ⟨g, hg⟩ := ug83_exists_unit_hom h hw1 hσ0
      obtain ⟨g', hg'X, hg'⟩ := hX1 σ hσN
      refine ⟨g, ?_, hg⟩
      have : ug83_embGL h (ug83_frame p₀ p₁) hF g = g' := by
        apply Units.ext
        rw [ug83_coe_embGL, hg, ug83_emb_hom h hF hw1, hFw, hg']
      rw [Subgroup.mem_comap, this]
      exact hg'X
    · obtain ⟨g, hg⟩ := ug83_exists_unit_hom h hu1 hσ0
      obtain ⟨g', hg'X, hg'⟩ := hX2 σ hσN
      refine ⟨g, ?_, hg⟩
      have : ug83_embGL h (ug83_frame p₀ p₁) hF g = g' := by
        apply Units.ext
        rw [ug83_coe_embGL, hg, ug83_emb_hom h hF hu1, hFu, hg']
      rw [Subgroup.mem_comap, this]
      exact hg'X
  exact fun y hy => key hy

@[expose] def ug83_Good (h : UnitaryFieldData ℓ f K) {n : ℕ} (X : Subgroup (GL (Fin n) K))
    (w : Fin n → K) : Prop :=
  ∑ i, h.bar (w i) * w i = 1 ∧
    ∀ ρ : K, h.bar ρ * ρ = 1 → ug83_Mem X (unitaryHomology h w ρ)

open _root_.Classical in
noncomputable def ug83_supp {n : ℕ} (u : Fin n → K) : Finset (Fin n) :=
  Finset.univ.filter fun i => u i ≠ 0

theorem ug83_mem_supp {n : ℕ} {u : Fin n → K} {i : Fin n} : i ∈ ug83_supp u ↔ u i ≠ 0 := by
  simp [ug83_supp]

section Good

variable (h : UnitaryFieldData ℓ f K) {n : ℕ} {X : Subgroup (GL (Fin n) K)}

theorem ug83_Mem_hom_single
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    (k : Fin n) {σ : K} (hσ : h.bar σ * σ = 1) :
    ug83_Mem X (unitaryHomology h (Pi.single k 1 : Fin n → K) σ) := by
  rw [ug83_hom_single]
  refine ug83_Mem_diagonal h hD _ fun i => ?_
  by_cases hi : i = k
  · subst hi
    simpa using hσ
  · simp [Function.update_apply, hi]

theorem ug83_good_column (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    {x : GL (Fin n) K} (hx : x ∈ X) (j : Fin n) :
    ug83_Good h X (fun i => (x : Matrix (Fin n) (Fin n) K) i j) := by
  have hcol : (fun i => (x : Matrix (Fin n) (Fin n) K) i j) =
      (x : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single j 1 : Fin n → K) := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hU := ug83_adj_mul_self_of_mem h hXU hx
  have hw : ∑ i, h.bar ((Pi.single j 1 : Fin n → K) i) * (Pi.single j 1 : Fin n → K) i = 1 := by
    simp [Pi.single_apply]
  rw [hcol]
  refine ⟨by rw [ug83_norm_mulVec h _ hU, hw], fun ρ hρ => ?_⟩
  rw [← ug83_conj_hom h _ hU hw ρ]
  exact ug83_Mem_conj h hXU hx (ug83_Mem_hom_single h hD j hρ)

end Good

section Coord

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

theorem ug83_coord_gram {a b : Fin n} (hab : a ≠ b) :
    ug83_adj h (ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1)) *
      ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1) = 1 :=
  ug83_adj_frame_mul_frame h (by simp [Pi.single_apply]) (by simp [Pi.single_apply])
    (by simp [Pi.single_apply, hab, Ne.symm hab])

theorem ug83_coord_proj {a b : Fin n} (hab : a ≠ b) :
    ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1) *
      ug83_adj h (ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1)) =
      diagonal (fun i => if i = a ∨ i = b then (1 : K) else 0) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, ug83_adj_apply, ug83_frame, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single_apply, diagonal_apply]
  by_cases hia : i = a <;> by_cases hib : i = b <;> by_cases hja : j = a <;>
    by_cases hjb : j = b <;> simp_all [eq_comm]

theorem ug83_block_eq_emb {a b : Fin n} (hab : a ≠ b) {g : GL (Fin n) K}
    (hg : g ∈ unitarySU ℓ f K n) (hblock : IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K)) :
    ∃ y ∈ unitarySU ℓ f K 2,
      ug83_embGL h (ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1))
        (ug83_coord_gram h hab) y = g := by
  set F := ug83_frame (Pi.single a 1 : Fin n → K) (Pi.single b 1)
  have hF := ug83_coord_gram h hab
  have hProj := ug83_coord_proj h (K := K) hab
  obtain ⟨hdet, hU⟩ := (mem_unitarySU_iff h).1 hg
  set M := ug83_adj h F * (g : Matrix (Fin n) (Fin n) K) * F
  set d : Fin n → K := fun i => if i = a ∨ i = b then (1 : K) else 0 with hd
  have hProjProj : F * ug83_adj h F * (F * ug83_adj h F) = F * ug83_adj h F := by
    calc F * ug83_adj h F * (F * ug83_adj h F) = F * (ug83_adj h F * F) * ug83_adj h F := by
          simp only [Matrix.mul_assoc]
      _ = F * ug83_adj h F := by rw [hF, Matrix.mul_one]
  have hblock' : (g : Matrix (Fin n) (Fin n) K) - 1 =
      diagonal d * ((g : Matrix (Fin n) (Fin n) K) - 1) * diagonal d := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases hij : (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b)
    · have := hblock i j hij
      simp [this, Matrix.one_apply]
    · push Not at hij
      have hi : d i = 1 := by
        simp only [hd]
        by_cases hia : i = a
        · simp [hia]
        · simp [hij.1 hia]
      have hj : d j = 1 := by
        simp only [hd]
        by_cases hja : j = a
        · simp [hja]
        · simp [hij.2 hja]
      rw [hi, hj, one_mul, mul_one]
  have hgE : (g : Matrix (Fin n) (Fin n) K) = ug83_emb h F hF M := by
    have e1 : F * (ug83_adj h F * (g : Matrix (Fin n) (Fin n) K) * F - 1) * ug83_adj h F =
        F * ug83_adj h F * (g : Matrix (Fin n) (Fin n) K) * (F * ug83_adj h F) -
          F * ug83_adj h F := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    have e2 : F * ug83_adj h F * ((g : Matrix (Fin n) (Fin n) K) - 1) * (F * ug83_adj h F) =
        F * ug83_adj h F * (g : Matrix (Fin n) (Fin n) K) * (F * ug83_adj h F) -
          F * ug83_adj h F := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hProjProj]
    calc (g : Matrix (Fin n) (Fin n) K) = 1 + ((g : Matrix (Fin n) (Fin n) K) - 1) := by abel
      _ = 1 + diagonal d * ((g : Matrix (Fin n) (Fin n) K) - 1) * diagonal d := by
          rw [← hblock']
      _ = 1 + F * ug83_adj h F * ((g : Matrix (Fin n) (Fin n) K) - 1) * (F * ug83_adj h F) := by
          rw [hProj]
      _ = ug83_emb h F hF M := by rw [ug83_emb_apply, e2, ← e1]
  have hemb : ug83_emb h F hF (ug83_adj h M * M) = 1 := by
    rw [map_mul, ← ug83_adj_emb h hF, ← hgE]
    exact hU
  have hMu : ug83_adj h M * M = 1 := by
    rw [← ug83_adj_mul_emb_mul h hF (ug83_adj h M * M), hemb, Matrix.mul_one, hF]
  have hdetM : M.det = 1 := by
    rw [← ug83_det_emb h hF M, ← hgE, hdet]
  refine ⟨⟨M, ug83_adj h M, mul_eq_one_comm.2 hMu, hMu⟩,
    (mem_unitarySU_iff h).2 ⟨hdetM, hMu⟩, ?_⟩
  apply Units.ext
  rw [ug83_coe_embGL]
  exact hgE.symm

end Coord

section PlaneDiag

variable (h : UnitaryFieldData ℓ f K) {n : ℕ}

theorem ug83_frame_diag (p₀ p₁ : Fin n → K) (c : Fin 2 → K) :
    ug83_frame p₀ p₁ * diagonal c * ug83_adj h (ug83_frame p₀ p₁) =
      c 0 • ug83_P h p₀ + c 1 • ug83_P h p₁ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, ug83_frame, ug83_adj_apply, ug83_P_apply,
    Matrix.diagonal_apply]
  ring

theorem ug83_emb_diag {p₀ p₁ : Fin n → K}
    (hF : ug83_adj h (ug83_frame p₀ p₁) * ug83_frame p₀ p₁ = 1) (c : Fin 2 → K) :
    ug83_emb h (ug83_frame p₀ p₁) hF (diagonal c) =
      1 + (c 0 - 1) • ug83_P h p₀ + (c 1 - 1) • ug83_P h p₁ := by
  have e : (diagonal c : Matrix (Fin 2) (Fin 2) K) - 1 = diagonal (fun i => c i - 1) := by
    rw [← diagonal_one, ← diagonal_sub]
  rw [ug83_emb_apply, e, ug83_frame_diag, add_assoc]

theorem ug83_emb_diag_mul {p₀ p₁ : Fin n → K}
    (hF : ug83_adj h (ug83_frame p₀ p₁) * ug83_frame p₀ p₁ = 1)
    (h00 : ∑ i, h.bar (p₀ i) * p₀ i = 1) (h11 : ∑ i, h.bar (p₁ i) * p₁ i = 1)
    (h01 : ∑ i, h.bar (p₀ i) * p₁ i = 0) {a : K} (ha : h.bar a * a = 1) :
    ug83_emb h (ug83_frame p₀ p₁) hF (diagonal ![h.bar a, a]) * unitaryHomology h p₀ a =
      unitaryHomology h p₁ a := by
  have h10 : ∑ i, h.bar (p₁ i) * p₀ i = 0 := by
    have := congrArg h.bar h01
    simpa [map_sum, map_mul, h.bar_bar, mul_comm] using this
  have hEE := ug83_P_mul_P h h00
  have hVV := ug83_P_mul_P h h11
  have hVE : ug83_P h p₁ * ug83_P h p₀ = 0 := by
    rw [ug83_P, ug83_P, vecMulVec_mul_vecMulVec]
    have : (fun i => h.bar (p₁ i)) ⬝ᵥ p₀ = 0 := h10
    rw [this, zero_smul, vecMulVec_zero]
  rw [ug83_emb_diag, ug83_hom_eq h h00, ug83_hom_eq h h11]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : (1 + (h.bar a - 1) • ug83_P h p₀ + (a - 1) • ug83_P h p₁) *
      (1 + (a - 1) • ug83_P h p₀) = 1 + (a - 1) • ug83_P h p₁ +
        ((h.bar a - 1) + (a - 1) + (h.bar a - 1) * (a - 1)) • ug83_P h p₀ := by
    simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, hEE, hVE,
      smul_zero, add_zero]
    module
  have hc : (h.bar a - 1) + (a - 1) + (h.bar a - 1) * (a - 1) = 0 := by linear_combination ha
  rw [key, hc, zero_smul, add_zero]

end PlaneDiag

theorem ug83_diag_mem_su2 (h : UnitaryFieldData ℓ f K) {a : K} (ha : h.bar a * a = 1) :
    ∃ y ∈ unitarySU ℓ f K 2, (y : Matrix (Fin 2) (Fin 2) K) = diagonal ![h.bar a, a] := by
  have ha' : a * h.bar a = 1 := by
    rw [mul_comm]
    exact ha
  have hMu : ug83_adj h (diagonal ![h.bar a, a] : Matrix (Fin 2) (Fin 2) K) *
      diagonal ![h.bar a, a] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ug83_adj_apply, Matrix.mul_apply, Fin.sum_univ_two, ha, ha', h.bar_bar,
        Matrix.diagonal_apply]
  refine ⟨⟨diagonal ![h.bar a, a], ug83_adj h (diagonal ![h.bar a, a]),
    mul_eq_one_comm.2 hMu, hMu⟩, (mem_unitarySU_iff h).2 ⟨?_, hMu⟩, rfl⟩
  simp [det_diagonal, Fin.prod_univ_two, ha]

section Main

variable (h : UnitaryFieldData ℓ f K) {n : ℕ} {X : Subgroup (GL (Fin n) K)}

theorem ug83_base (h82 : TwoHomologiesSU2 h) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1))
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    {u : Fin n → K} (hu : ug83_Good h X u) {a b : Fin n} (hab : a ≠ b)
    (hs : ug83_supp u = {a, b}) :
    ∀ g ∈ unitarySU ℓ f K n, IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ X := by
  intro g hg hblock
  obtain ⟨y, hy, rfl⟩ := ug83_block_eq_emb h hab hg hblock
  have hua : u a ≠ 0 := ug83_mem_supp.1 (by rw [hs]; simp)
  have hub : u b ≠ 0 := ug83_mem_supp.1 (by rw [hs]; simp)
  have hzero : ∀ i, i ≠ a → i ≠ b → u i = 0 := by
    intro i hia hib
    by_contra hne
    have := ug83_mem_supp.2 hne
    rw [hs] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    tauto
  have hsum : h.bar (u a) * u a + h.bar (u b) * u b = 1 := by
    have h2 : ∑ i ∈ ({a, b} : Finset (Fin n)), h.bar (u i) * u i = ∑ i, h.bar (u i) * u i :=
      Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        simp [hzero i hi.1 hi.2]
    rw [Finset.sum_pair hab] at h2
    rw [h2]
    exact hu.1
  have hvec : (fun i => (Pi.single a 1 : Fin n → K) i * u a + (Pi.single b 1 : Fin n → K) i * u b)
      = u := by
    funext i
    by_cases hia : i = a
    · subst hia
      simp [Pi.single_apply, hab]
    · by_cases hib : i = b
      · subst hib
        simp [Pi.single_apply, hia]
      · simp [Pi.single_apply, hia, hib, hzero i hia hib]
  exact ug83_plane h h82 hq he X (ug83_coord_gram h hab) hua hub hsum
    (fun σ hσ => ug83_Mem_hom_single h hD a hσ)
    (fun ρ hρ => by rw [hvec]; exact hu.2 ρ hρ) y hy

theorem ug83_stepB (h82 : TwoHomologiesSU2 h) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1))
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    {u : Fin n → K} (hu : ug83_Good h X u) {k : Fin n} (hk : u k ≠ 0)
    (hN : h.bar (u k) * u k ≠ 1) :
    ∃ v : Fin n → K, ug83_Good h X v ∧ ug83_supp v = (ug83_supp u).erase k := by
  obtain ⟨s, hs⟩ : ∃ s : K, s = 1 - h.bar (u k) * u k := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hs]
    exact sub_ne_zero.2 (Ne.symm hN)
  have hsbar : h.bar s = s := by
    rw [hs, map_sub, map_one, map_mul, h.bar_bar, mul_comm]
  have htF : s⁻¹ ∈ h.fixedField := by
    rw [UnitaryFieldData.mem_fixedField, map_inv₀, hsbar]
  obtain ⟨d, hd⟩ := ug83_exists_norm_eq h htF
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hd
    exact hs0 hd.symm
  obtain ⟨v, hv⟩ : ∃ v : Fin n → K, v = fun i => if i = k then 0 else d * u i := ⟨_, rfl⟩
  have hvk : v k = 0 := by simp [hv]
  have hvi : ∀ i, i ≠ k → v i = d * u i := fun i hi => by simp [hv, hi]
  have hvnorm : ∑ i, h.bar (v i) * v i = 1 := by
    calc ∑ i, h.bar (v i) * v i
        = ∑ i, ((h.bar d * d) * (h.bar (u i) * u i) -
            if i = k then (h.bar d * d) * (h.bar (u k) * u k) else 0) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases hi : i = k
          · subst hi
            simp [hv]
          · rw [hvi i hi]
            simp [hi]
            ring
      _ = (h.bar d * d) * ∑ i, h.bar (u i) * u i - (h.bar d * d) * (h.bar (u k) * u k) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k]
          simp
      _ = 1 := by
          rw [hu.1, hd, ← mul_sub, ← hs, inv_mul_cancel₀ hs0]
  have hF : ug83_adj h (ug83_frame (Pi.single k 1 : Fin n → K) v) *
      ug83_frame (Pi.single k 1 : Fin n → K) v = 1 :=
    ug83_adj_frame_mul_frame h (by simp [Pi.single_apply]) hvnorm
      (by simp [Pi.single_apply, hvk])
  have hβ0 : d⁻¹ ≠ 0 := inv_ne_zero hd0
  have hαβ : h.bar (u k) * u k + h.bar d⁻¹ * d⁻¹ = 1 := by
    rw [map_inv₀, ← mul_inv, hd, inv_inv, hs]
    ring
  have hvec : (fun i => (Pi.single k 1 : Fin n → K) i * u k + v i * d⁻¹) = u := by
    funext i
    by_cases hi : i = k
    · subst hi
      simp [hvk]
    · rw [hvi i hi]
      simp [Pi.single_apply, hi]
      field_simp
  have hplane := ug83_plane h h82 hq he X hF hk hβ0 hαβ
    (fun σ hσ => ug83_Mem_hom_single h hD k hσ)
    (fun ρ hρ => by rw [hvec]; exact hu.2 ρ hρ)
  refine ⟨v, ⟨hvnorm, fun a ha => ?_⟩, ?_⟩
  · obtain ⟨y, hy, hyM⟩ := ug83_diag_mem_su2 h ha
    have hmem : ug83_Mem X (ug83_emb h (ug83_frame (Pi.single k 1 : Fin n → K) v) hF
        (diagonal ![h.bar a, a])) :=
      ⟨_, hplane y hy, by rw [ug83_coe_embGL, hyM]⟩
    have := hmem.mul (ug83_Mem_hom_single h hD k ha)
    rwa [ug83_emb_diag_mul h hF (by simp [Pi.single_apply]) hvnorm
      (by simp [Pi.single_apply, hvk]) ha] at this
  · ext i
    simp only [ug83_mem_supp, Finset.mem_erase, ne_eq]
    by_cases hi : i = k
    · simp [hvk, hi]
    · simp [hvi i hi, hi, hd0]

theorem ug83_stepA (hq : 4 ≤ ℓ ^ f) (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    {u : Fin n → K} (hu : ug83_Good h X u) (hcard : 2 ≤ (ug83_supp u).card) :
    ∃ u' : Fin n → K, ug83_Good h X u' ∧ ug83_supp u' = ug83_supp u ∧
      ∃ k, u' k ≠ 0 ∧ h.bar (u' k) * u' k ≠ 1 := by
  by_cases hex : ∃ k, u k ≠ 0 ∧ h.bar (u k) * u k ≠ 1
  · obtain ⟨k, hk⟩ := hex
    exact ⟨u, hu, rfl, k, hk⟩
  · push Not at hex
    obtain ⟨ρ₀, hρN, hρ1, hρ2⟩ := ug83_exists_rho h hq
    obtain ⟨k₀, hk₀, k, hk, hkk⟩ := Finset.one_lt_card.1 (by omega : 1 < (ug83_supp u).card)
    obtain ⟨g, hgX, hg⟩ := hu.2 ρ₀ hρN
    have hU := ug83_adj_mul_self_of_mem h hXU hgX
    have hw1 : ∑ i, h.bar ((Pi.single k₀ 1 : Fin n → K) i) *
        (Pi.single k₀ 1 : Fin n → K) i = 1 := by
      simp [Pi.single_apply]
    obtain ⟨u', hu'⟩ : ∃ u' : Fin n → K,
        u' = (g : Matrix (Fin n) (Fin n) K) *ᵥ (Pi.single k₀ 1 : Fin n → K) := ⟨_, rfl⟩
    have hcoord : ∀ i, u' i = (if i = k₀ then 1 else 0) + (ρ₀ - 1) * (u i * h.bar (u k₀)) := by
      intro i
      rw [hu', Matrix.mulVec_single_one, Matrix.col_apply, hg, ug83_hom_eq h hu.1]
      simp [ug83_P_apply, Matrix.one_apply]
    have hgood : ug83_Good h X u' := by
      refine ⟨by rw [hu', ug83_norm_mulVec h _ hU, hw1], fun ρ hρ => ?_⟩
      rw [hu', ← ug83_conj_hom h _ hU hw1 ρ]
      exact ug83_Mem_conj h hXU hgX (ug83_Mem_hom_single h hD k₀ hρ)
    have hk0 : u k₀ ≠ 0 := ug83_mem_supp.1 hk₀
    have hk0' : u k ≠ 0 := ug83_mem_supp.1 hk
    have hρ0 : ρ₀ ≠ 0 := by
      rintro rfl
      simp at hρN
    have hbar0 : h.bar (u k₀) ≠ 0 := (h.bar_eq_zero_iff).not.mpr hk0
    have hρ1' : ρ₀ - 1 ≠ 0 := sub_ne_zero.2 hρ1
    have hsupp : ug83_supp u' = ug83_supp u := by
      ext i
      rw [ug83_mem_supp, ug83_mem_supp, hcoord]
      by_cases hi : i = k₀
      · subst hi
        have : (1 : K) + (ρ₀ - 1) * (u i * h.bar (u i)) = ρ₀ := by
          rw [mul_comm (u i), hex i hk0]
          ring
        simp [this, hρ0, hk0]
      · simp [hi, hρ1', hbar0]
    refine ⟨u', hgood, hsupp, k, ?_, ?_⟩
    · rw [hcoord]
      simp [hkk.symm, hρ1', hk0', hbar0]
    · have : h.bar (u' k) * u' k = h.bar (ρ₀ - 1) * (ρ₀ - 1) *
          ((h.bar (u k) * u k) * (h.bar (u k₀) * u k₀)) := by
        rw [hcoord]
        simp only [if_neg hkk.symm, zero_add, map_mul, h.bar_bar]
        ring
      rw [this, hex k hk0', hex k₀ hk0]
      simpa using hρ2

theorem ug83_step (h82 : TwoHomologiesSU2 h) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    {u : Fin n → K} (hu : ug83_Good h X u) (hcard : 3 ≤ (ug83_supp u).card) :
    ∃ v : Fin n → K, ug83_Good h X v ∧ (ug83_supp v).card + 1 = (ug83_supp u).card := by
  obtain ⟨u', hu', hsupp, k, hk, hN⟩ := ug83_stepA h hq hXU hD hu (by omega)
  obtain ⟨v, hv, hvs⟩ := ug83_stepB h h82 hq he hD hu' hk hN
  refine ⟨v, hv, ?_⟩
  rw [hvs, Finset.card_erase_of_mem (ug83_mem_supp.2 hk), hsupp]
  omega

theorem ug83_main (h82 : TwoHomologiesSU2 h) (hq : 4 ≤ ℓ ^ f)
    (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X) :
    ∀ m : ℕ, 2 ≤ m → ∀ u : Fin n → K, ug83_Good h X u → (ug83_supp u).card = m →
      ∃ a b : Fin n, a ≠ b ∧ ∀ g ∈ unitarySU ℓ f K n,
        IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ X := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro u hu hc
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hc
    exact ⟨a, b, hab, ug83_base h h82 hq he hD hu hab hs⟩
  | succ m hm ih =>
    intro u hu hc
    obtain ⟨v, hv, hvc⟩ := ug83_step h h82 hq he hXU hD hu (by omega)
    exact ih v hv (by omega)

end Main

theorem exists_block_su_of_diag_of (h : UnitaryFieldData ℓ f K) (h82 : TwoHomologiesSU2 h)
    (hq : 4 ≤ ℓ ^ f) (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) {n : ℕ}
    (hn : 2 ≤ n) (X : Subgroup (GL (Fin n) K)) (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    (hx : ∃ x ∈ X, ¬ IsMonomialMat (x : Matrix (Fin n) (Fin n) K)) :
    ∃ a b : Fin n, a ≠ b ∧ ∀ g ∈ unitarySU ℓ f K n,
      IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ X := by
  obtain ⟨x, hxX, hxm⟩ := hx
  unfold IsMonomialMat at hxm
  push Not at hxm
  obtain ⟨j, i, i', hi, hi', hne⟩ := hxm
  have hgood := ug83_good_column h hXU hD hxX j
  have hcard : 2 ≤ (ug83_supp (fun r => (x : Matrix (Fin n) (Fin n) K) r j)).card := by
    have hsub : ({i, i'} : Finset (Fin n)) ⊆
        ug83_supp (fun r => (x : Matrix (Fin n) (Fin n) K) r j) := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact ug83_mem_supp.2 hi
      · exact ug83_mem_supp.2 hi'
    calc 2 = ({i, i'} : Finset (Fin n)).card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card hsub
  exact ug83_main h h82 hq he hXU hD _ hcard _ hgood rfl

theorem exists_block_su_of_diag (h : UnitaryFieldData ℓ f K)
    (hq : 4 ≤ ℓ ^ f) (he : 5 ≤ (ℓ ^ f + 1) / Nat.gcd 2 (ℓ ^ f + 1)) {n : ℕ}
    (hn : 2 ≤ n) (X : Subgroup (GL (Fin n) K)) (hXU : X ≤ primeFormUnitary h 1)
    (hD : ∀ g ∈ primeFormUnitary h (1 : Matrix (Fin n) (Fin n) K),
      (∃ t, (g : Matrix (Fin n) (Fin n) K) = diagonal t) → g ∈ X)
    (hx : ∃ x ∈ X, ¬ IsMonomialMat (x : Matrix (Fin n) (Fin n) K)) :
    ∃ a b : Fin n, a ≠ b ∧ ∀ g ∈ unitarySU ℓ f K n,
      IsCoordBlockOn a b (g : Matrix (Fin n) (Fin n) K) → g ∈ X :=
  exists_block_su_of_diag_of h (su2_le_of_two_homologies h) hq he hn X hXU hD hx

end CFSG.LieType.SeitzGeneration
