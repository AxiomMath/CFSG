module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025Mat
public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025

open Matrix Subgroup

section FormGroup

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def formGroup (σ : K →+* K) (J : Matrix ι ι K) : Subgroup (GL ι K) where
  carrier := {A | ((A : Matrix ι ι K).map σ)ᵀ * J * (A : Matrix ι ι K) = J}
  one_mem' := by
    simp [Matrix.map_one σ (map_zero σ) (map_one σ)]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    calc (((b : Matrix ι ι K).map σ)ᵀ * ((a : Matrix ι ι K).map σ)ᵀ) * J *
          ((a : Matrix ι ι K) * (b : Matrix ι ι K))
        = ((b : Matrix ι ι K).map σ)ᵀ *
          (((a : Matrix ι ι K).map σ)ᵀ * J * (a : Matrix ι ι K)) * (b : Matrix ι ι K) := by
          noncomm_ring
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : (((a⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((a : Matrix ι ι K).map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]
    have h2 : (a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (((a⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * J * ((a⁻¹ : GL ι K) : Matrix ι ι K)
        = (((a⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ *
          (((a : Matrix ι ι K).map σ)ᵀ * J * (a : Matrix ι ι K)) *
          ((a⁻¹ : GL ι K) : Matrix ι ι K) := by rw [ha]
      _ = ((((a⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * ((a : Matrix ι ι K).map σ)ᵀ) * J *
          ((a : Matrix ι ι K) * ((a⁻¹ : GL ι K) : Matrix ι ι K)) := by noncomm_ring
      _ = J := by rw [h1, h2]; simp

theorem mem_formGroup {σ : K →+* K} {J : Matrix ι ι K} {A : GL ι K} :
    A ∈ formGroup σ J ↔ ((A : Matrix ι ι K).map σ)ᵀ * J * (A : Matrix ι ι K) = J := Iff.rfl

end FormGroup


section W

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem one_add_form {σ : K →+* K} {J X : Matrix ι ι K} (hX : (X.map σ)ᵀ * J * X = J)
    (hXX : X * X = -1) : ((1 + X).map σ)ᵀ * J * (1 + X) = (2 : K) • J := by
  have hmap : (1 + X).map σ = 1 + X.map σ := by
    have := map_add σ.mapMatrix 1 X
    rwa [map_one] at this
  have h3 : -((X.map σ)ᵀ * J) = J * X := by
    calc -((X.map σ)ᵀ * J) = (X.map σ)ᵀ * J * (X * X) := by rw [hXX]; noncomm_ring
      _ = (X.map σ)ᵀ * J * X * X := by rw [Matrix.mul_assoc ((X.map σ)ᵀ * J)]
      _ = J * X := by rw [hX]
  rw [hmap, Matrix.transpose_add, Matrix.transpose_one]
  calc (1 + (X.map σ)ᵀ) * J * (1 + X)
      = J + ((X.map σ)ᵀ * J + J * X) + (X.map σ)ᵀ * J * X := by noncomm_ring
    _ = (2 : K) • J := by
      rw [hX, ← h3, add_neg_cancel, add_zero, two_smul]

theorem map_smul_ring (σ : K →+* K) (c : K) (M : Matrix ι ι K) :
    (c • M).map σ = σ c • M.map σ := by
  ext i j
  simp

theorem formGroup_W {σ : K →+* K} {J : Matrix ι ι K} (h2 : (2 : K) ≠ 0) (hσ : σ 2⁻¹ = 2⁻¹)
    {x u w : GL ι K} (hx : x ∈ formGroup σ J) (hu : u ∈ formGroup σ J) (hxx : x * x = -1)
    (hw : (w : Matrix ι ι K) = (2⁻¹ : K) • ((1 + (x : Matrix ι ι K)) *
      (1 + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K)))) : w ∈ formGroup σ J := by
  have hx' : u * x * u⁻¹ ∈ formGroup σ J :=
    (formGroup σ J).mul_mem ((formGroup σ J).mul_mem hu hx) ((formGroup σ J).inv_mem hu)
  have hxx' : (u * x * u⁻¹) * (u * x * u⁻¹) = -1 := by
    calc (u * x * u⁻¹) * (u * x * u⁻¹) = u * (x * x) * u⁻¹ := by group
      _ = -1 := by rw [hxx, conj_neg_one]
  have hX : ((x : Matrix ι ι K).map σ)ᵀ * J * (x : Matrix ι ι K) = J := hx
  have hX' : (((u * x * u⁻¹ : GL ι K) : Matrix ι ι K).map σ)ᵀ * J *
      ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K) = J := hx'
  have hXX : (x : Matrix ι ι K) * x = -1 := by simpa using congrArg Units.val hxx
  have hXX' : ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K) * ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K)
      = -1 := by
    have := congrArg Units.val hxx'
    rwa [Units.val_mul, Units.val_neg, Units.val_one] at this
  have hA := one_add_form hX hXX
  have hB := one_add_form hX' hXX'
  show (((w : Matrix ι ι K)).map σ)ᵀ * J * (w : Matrix ι ι K) = J
  rw [hw]
  generalize hAdef : (1 : Matrix ι ι K) + (x : Matrix ι ι K) = A at hA ⊢
  generalize hBdef : (1 : Matrix ι ι K) + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K) = B at hB ⊢
  have hc : (2⁻¹ : K) * σ (2⁻¹ : K) * (2 * 2) = 1 := by
    rw [hσ]
    field_simp
  have hmid : (B.map σ)ᵀ * (A.map σ)ᵀ * J * (A * B) = (2 * 2 : K) • J := by
    calc (B.map σ)ᵀ * (A.map σ)ᵀ * J * (A * B)
        = (B.map σ)ᵀ * ((A.map σ)ᵀ * J * A) * B := by noncomm_ring
      _ = (B.map σ)ᵀ * ((2 : K) • J) * B := by rw [hA]
      _ = (2 : K) • ((B.map σ)ᵀ * J * B) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (2 : K) • ((2 : K) • J) := by rw [hB]
      _ = (2 * 2 : K) • J := by rw [smul_smul]
  have hT : ((((2⁻¹ : K) • (A * B)).map σ)ᵀ) = σ (2⁻¹) • ((B.map σ)ᵀ * (A.map σ)ᵀ) := by
    rw [map_smul_ring, Matrix.transpose_smul, Matrix.map_mul, Matrix.transpose_mul]
  rw [hT]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [hmid, smul_smul, hc, one_smul]

end W


section Det

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem det_W (h2 : (2 : K) ≠ 0) (hcard : Fintype.card ι = 4) {x u w : GL ι K}
    (hx : (x : Matrix ι ι K).det = 1) (hxx : x * x = -1)
    (hw : (w : Matrix ι ι K) = (2⁻¹ : K) • ((1 + (x : Matrix ι ι K)) *
      (1 + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K)))) : (w : Matrix ι ι K).det = 1 := by
  have hXX : (x : Matrix ι ι K) * x = -1 := by simpa using congrArg Units.val hxx
  have hd1 : ((1 : Matrix ι ι K) + x).det * ((1 : Matrix ι ι K) + x).det = 16 := by
    rw [← Matrix.det_mul]
    have : ((1 : Matrix ι ι K) + x) * (1 + x) = (2 : K) • (x : Matrix ι ι K) := by
      calc ((1 : Matrix ι ι K) + x) * (1 + x) = 1 + x + x + x * x := by noncomm_ring
        _ = (2 : K) • (x : Matrix ι ι K) := by
          rw [hXX, two_smul]
          abel
    rw [this, Matrix.det_smul, hx, hcard]
    norm_num
  have hd2 : ((1 : Matrix ι ι K) + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K)).det =
      ((1 : Matrix ι ι K) + x).det := by
    have : (1 : Matrix ι ι K) + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K) =
        (u : Matrix ι ι K) * (1 + x) * ((u⁻¹ : GL ι K) : Matrix ι ι K) := by
      calc (1 : Matrix ι ι K) + ((u * x * u⁻¹ : GL ι K) : Matrix ι ι K)
          = (u : Matrix ι ι K) * ((u⁻¹ : GL ι K) : Matrix ι ι K) +
            (u : Matrix ι ι K) * x * ((u⁻¹ : GL ι K) : Matrix ι ι K) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Units.val_mul, Units.val_mul]
        _ = (u : Matrix ι ι K) * (1 + x) * ((u⁻¹ : GL ι K) : Matrix ι ι K) := by noncomm_ring
    rw [this, Matrix.det_units_conj]
  rw [hw, Matrix.det_smul, Matrix.det_mul, hd2, hcard]
  calc (2⁻¹ : K) ^ 4 * (((1 : Matrix ι ι K) + x).det * ((1 : Matrix ι ι K) + x).det)
      = 2⁻¹ ^ 4 * 16 := by rw [hd1]
    _ = 1 := by
      field_simp
      norm_num

theorem scalar_pow_four_of_det (hcard : Fintype.card ι = 4) {H₀ : Subgroup (GL ι K)}
    (hdet : ∀ g ∈ H₀, (g : Matrix ι ι K).det = 1) (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar ι c ∈ H₀) : c ^ 4 = 1 := by
  have h1 := hdet _ hc
  have h2 : ((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K).det =
      (c : K) ^ Fintype.card ι := by
    have := congrArg Units.val (Matrix.GeneralLinearGroup.det_scalar (n := ι) c)
    simpa using this
  rw [h2, hcard] at h1
  exact Units.ext (by simpa using h1)

end Det


section Stated

open CFSG.Open

theorem statedSL_eq (n : ℕ) (K : Type) [Field K] :
    StatedSL n K = (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  have hset : {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1} =
      ((Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker : Set (GL (Fin n) K)) := by
    ext A
    simp [MonoidHom.mem_ker, Units.ext_iff]
  unfold StatedSL
  rw [hset]
  exact Subgroup.closure_eq _

theorem statedSp_eq (n : ℕ) (K : Type) [Field K] :
    StatedSp n K = formGroup (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  unfold StatedSp
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro A hA
    simpa [mem_formGroup] using hA
  · intro A hA
    apply Subgroup.subset_closure
    simpa [mem_formGroup] using hA

theorem statedSU_eq (n q : ℕ) (K : Type) [Field K] (σ : K →+* K) (hσ : ∀ x, σ x = x ^ q) :
    StatedSU n q K = (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker ⊓
      formGroup σ (1 : Matrix (Fin n) (Fin n) K) := by
  have hmap : ∀ A : Matrix (Fin n) (Fin n) K, A.map σ = A.map (· ^ q) := fun A => by
    ext i j
    simp [hσ]
  unfold StatedSU
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro A ⟨hdet, hform⟩
    refine ⟨?_, ?_⟩
    · simpa [MonoidHom.mem_ker, Units.ext_iff] using hdet
    · show ((A : Matrix (Fin n) (Fin n) K).map σ)ᵀ * 1 * (A : Matrix (Fin n) (Fin n) K) = 1
      rw [hmap, mul_one]
      exact hform
  · rintro A ⟨hdet, hform⟩
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · simpa [MonoidHom.mem_ker, Units.ext_iff] using hdet
    · have h1 : ((A : Matrix (Fin n) (Fin n) K).map σ)ᵀ * 1 * (A : Matrix (Fin n) (Fin n) K) = 1 :=
        hform
      rw [hmap, mul_one] at h1
      exact h1

end Stated


section Families

open CFSG.Open

variable {K : Type} [Field K] [Finite K]

theorem kxSection_sl (h2 : (2 : K) ≠ 0) {A : Type} [Group A] {L S : Subgroup A}
    (e : ↥L ≃* StatedProj (StatedSL 4 K)) {z : A} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : orderOf z = p) (hzL : z ∈ L) (hSL : S ≤ L) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) (hcomm : ⁅S, zpowers z⁆ = S) :
    KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  have hdet : ∀ g ∈ StatedSL 4 K, (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    intro g hg
    rw [statedSL_eq] at hg
    simpa [MonoidHom.mem_ker, Units.ext_iff] using hg
  refine kxSection_of_stated_proj h2 (Fintype.card_fin 4) (StatedSL 4 K)
    (fun c hc => scalar_pow_four_of_det (Fintype.card_fin 4) hdet c hc) ?_ e hp hp5 hzp hzL hSL
    hS2 hS1 hzS hcomm
  intro x u w hx hu hxx hw
  rw [statedSL_eq]
  simp only [MonoidHom.mem_ker]
  apply Units.ext
  simpa using det_W h2 (Fintype.card_fin 4) (hdet x hx) hxx hw

theorem symplectic_scalar (c : Kˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ formGroup (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) : c ^ 4 = 1 := by
  rw [mem_formGroup] at hc
  have h := congrFun (congrFun hc (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.mul_apply, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.diagonal_apply] at h
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  calc (c : K) ^ 4 = ((c : K) * c) * ((c : K) * c) := by ring
    _ = 1 := by rw [h]; ring

theorem kxSection_sp (h2 : (2 : K) ≠ 0) {A : Type} [Group A] {L S : Subgroup A}
    (e : ↥L ≃* StatedProj (StatedSp 2 K)) {z : A} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hzp : orderOf z = p) (hzL : z ∈ L) (hSL : S ≤ L) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) (hcomm : ⁅S, zpowers z⁆ = S) :
    KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  refine kxSection_of_stated_proj h2 (by simp) (StatedSp 2 K)
    (fun c hc => by rw [statedSp_eq] at hc; exact symplectic_scalar c hc) ?_ e hp hp5 hzp hzL hSL
    hS2 hS1 hzS hcomm
  intro x u w hx hu hxx hw
  rw [statedSp_eq] at hx hu ⊢
  exact formGroup_W h2 (by simp) hx hu hxx hw


theorem kxSection_su {p f : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2) (hf : f ≠ 0)
    (hK : Nat.card K = (p ^ f) ^ 2) {A : Type} [Group A] {L S : Subgroup A}
    (e : ↥L ≃* StatedProj (StatedSU 4 (p ^ f) K)) {z : A} {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hzp : orderOf z = r) (hzL : z ∈ L) (hSL : S ≤ L) (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥)
    (hzS : z ∈ normalizer (S : Set A)) (hcomm : ⁅S, zpowers z⁆ = S) :
    KxSection z (normalizer (S : Set A) ⊓ L) 3 := by
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = p ^ (2 * f) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  haveI : CharP K p := charP_of_card_eq_prime_pow hcard
  haveI : ExpChar K p := ExpChar.prime hpp
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h')
  obtain ⟨σ, hσ⟩ : ∃ σ : K →+* K, ∀ x, σ x = x ^ (p ^ f) :=
    ⟨iterateFrobenius K p f, fun x => rfl⟩
  have hσ2 : σ 2⁻¹ = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  have hdet : ∀ g ∈ StatedSU 4 (p ^ f) K, (g : Matrix (Fin 4) (Fin 4) K).det = 1 := by
    intro g hg
    rw [statedSU_eq 4 (p ^ f) K σ hσ] at hg
    simpa [MonoidHom.mem_ker, Units.ext_iff] using hg.1
  refine kxSection_of_stated_proj h2 (Fintype.card_fin 4) (StatedSU 4 (p ^ f) K)
    (fun c hc => scalar_pow_four_of_det (Fintype.card_fin 4) hdet c hc) ?_ e hr hr5 hzp hzL hSL
    hS2 hS1 hzS hcomm
  intro x u w hx hu hxx hw
  have hxd := hdet x hx
  rw [statedSU_eq 4 (p ^ f) K σ hσ] at hx hu ⊢
  refine ⟨MonoidHom.mem_ker.mpr (Units.ext ?_), formGroup_W h2 hσ2 hx.2 hu.2 hxx hw⟩
  simpa using det_W h2 (Fintype.card_fin 4) hxd hxx hw

end Families

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025
