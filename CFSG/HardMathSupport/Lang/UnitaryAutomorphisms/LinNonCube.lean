module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinNil
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinGlue
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.LinFrame

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

theorem rk1_comm_of_orth {u u' ψ ψ' : Fin n → K} (_hu : ψ ⬝ᵥ u = 0) (_hu' : ψ' ⬝ᵥ u' = 0)
    (h1 : ψ ⬝ᵥ u' = 0) (h2 : ψ' ⬝ᵥ u = 0) (a b : K) :
    rk1 u ψ a * rk1 u' ψ' b = rk1 u' ψ' b * rk1 u ψ a := by
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [rk1_pair_apply, rk1_pair_apply, h1, h2]
  simp only [mul_zero, zero_mul, add_zero]
  module

@[expose] def triRk1 (e φ : Fin 3 → Fin n → K) (a : K) : Matrix (Fin n) (Fin n) K :=
  rk1 (e 0) (φ 0) a * rk1 (e 1) (φ 1) a * rk1 (e 2) (φ 2) a

theorem commute_rk1_of_orth {e φ : Fin 3 → Fin n → K} (hee : ∀ i j, φ i ⬝ᵥ e j = 0) (a : K)
    (i j : Fin 3) : Commute (rk1 (e i) (φ i) a) (rk1 (e j) (φ j) a) :=
  rk1_comm_of_orth (hee i i) (hee j j) (hee i j) (hee j i) a a

theorem triRk1_pow_char {e φ : Fin 3 → Fin n → K} (hee : ∀ i j, φ i ⬝ᵥ e j = 0) (a : K)
    (p : ℕ) [CharP K p] : triRk1 e φ a ^ p = 1 := by
  have c := commute_rk1_of_orth hee a
  unfold triRk1
  rw [((c 0 2).mul_left (c 1 2)).mul_pow, (c 0 1).mul_pow, rk1_pow_char (hee 0 0),
    rk1_pow_char (hee 1 1), rk1_pow_char (hee 2 2)]
  simp

theorem det_triRk1 {e φ : Fin 3 → Fin n → K} (hee : ∀ i j, φ i ⬝ᵥ e j = 0) (a : K) :
    (triRk1 e φ a).det = 1 := by
  unfold triRk1
  rw [Matrix.det_mul, Matrix.det_mul, det_rk1 (hee 0 0), det_rk1 (hee 1 1), det_rk1 (hee 2 2)]
  simp

theorem rk1_smul_inv_smul {l : K} (hl : l ≠ 0) (u ψ : Fin n → K) (a : K) :
    rk1 (l • u) (l⁻¹ • ψ) a = rk1 u ψ a := by
  rw [rk1, rk1, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, smul_smul,
    mul_assoc, mul_inv_cancel₀ hl, mul_one]

theorem triRk1_commute {e φ : Fin 3 → Fin n → K} (hee : ∀ i j, φ i ⬝ᵥ e j = 0)
    {Bm Bi : Matrix (Fin n) (Fin n) K} (hBB : Bm * Bi = 1) (hBB' : Bi * Bm = 1) {l : K}
    (hl : l ≠ 0) (a : K)
    (h01 : Bm *ᵥ e 0 = e 1) (h12 : Bm *ᵥ e 1 = e 2) (h20 : Bm *ᵥ e 2 = l • e 0)
    (f01 : φ 0 ᵥ* Bi = φ 1) (f12 : φ 1 ᵥ* Bi = φ 2) (f20 : φ 2 ᵥ* Bi = l⁻¹ • φ 0) :
    Bm * triRk1 e φ a = triRk1 e φ a * Bm := by
  have c := commute_rk1_of_orth hee a
  have hBB'' : ∀ Z : Matrix (Fin n) (Fin n) K, Bi * (Bm * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBB', Matrix.one_mul]
  have key : Bm * triRk1 e φ a * Bi = triRk1 e φ a := by
    have e1 : Bm * triRk1 e φ a * Bi =
        (Bm * rk1 (e 0) (φ 0) a * Bi) * (Bm * rk1 (e 1) (φ 1) a * Bi) *
          (Bm * rk1 (e 2) (φ 2) a * Bi) := by
      unfold triRk1
      simp only [Matrix.mul_assoc, hBB'']
    rw [e1, conj_rk1 hBB, conj_rk1 hBB, conj_rk1 hBB, h01, h12, h20, f01, f12, f20,
      rk1_smul_inv_smul hl]
    unfold triRk1
    rw [Matrix.mul_assoc, ← (c 0 2).eq, ← Matrix.mul_assoc, ← (c 0 1).eq, Matrix.mul_assoc]
  calc Bm * triRk1 e φ a = Bm * triRk1 e φ a * (Bi * Bm) := by rw [hBB', Matrix.mul_one]
    _ = (Bm * triRk1 e φ a * Bi) * Bm := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [key]

theorem triRk1_pair_cube {e g φ φ' : Fin 3 → Fin n → K}
    (hee : ∀ i j, φ i ⬝ᵥ e j = 0) (hgg : ∀ i j, φ' i ⬝ᵥ g j = 0)
    (heg : ∀ i j, φ i ⬝ᵥ g j = if i = j then 1 else 0)
    (hge : ∀ i j, φ' i ⬝ᵥ e j = if i = j then 1 else 0) {β β' : K} (hββ : β * β' = -3) :
    (triRk1 e φ β * triRk1 g φ' β') ^ 3 = 1 := by
  have caa := commute_rk1_of_orth hee β
  have cbb := commute_rk1_of_orth hgg β'
  have cab : ∀ i j, i ≠ j → Commute (rk1 (e i) (φ i) β) (rk1 (g j) (φ' j) β') :=
    fun i j hij => rk1_comm_of_orth (hee i i) (hgg j j) (by rw [heg]; simp [hij])
      (by rw [hge]; simp [Ne.symm hij]) β β'
  have hS : ∀ i j, i ≠ j → Commute (rk1 (e i) (φ i) β * rk1 (g i) (φ' i) β')
      (rk1 (e j) (φ j) β * rk1 (g j) (φ' j) β') := fun i j hij =>
    ((caa i j).mul_right (cab i j hij)).mul_left
      ((cab j i hij.symm).symm.mul_right (cbb i j))
  have hr : triRk1 e φ β * triRk1 g φ' β' =
      (rk1 (e 0) (φ 0) β * rk1 (g 0) (φ' 0) β') * (rk1 (e 1) (φ 1) β * rk1 (g 1) (φ' 1) β') *
        (rk1 (e 2) (φ 2) β * rk1 (g 2) (φ' 2) β') := by
    unfold triRk1
    simp only [Matrix.mul_assoc]
    rw [(cab 2 0 (by decide)).left_comm, (cab 1 0 (by decide)).left_comm,
      (cab 2 1 (by decide)).left_comm]
  have hc : ∀ i, (rk1 (e i) (φ i) β * rk1 (g i) (φ' i) β') ^ 3 = 1 := fun i =>
    rk1_pair_cube (hee i i) (hgg i i) (by rw [heg]; simp) (by rw [hge]; simp) hββ
  rw [hr, ((hS 0 2 (by decide)).mul_left (hS 1 2 (by decide))).mul_pow,
    (hS 0 1 (by decide)).mul_pow, hc 0, hc 1, hc 2]
  simp

theorem triRk1_pair_not_scalar {e g φ φ' : Fin 3 → Fin n → K}
    (hee : ∀ i j, φ i ⬝ᵥ e j = 0)
    (heg : ∀ i j, φ i ⬝ᵥ g j = if i = j then 1 else 0)
    (hge : ∀ i j, φ' i ⬝ᵥ e j = if i = j then 1 else 0) {β β' : K} (hβ' : β' ≠ 0)
    (s : K) : triRk1 e φ β * triRk1 g φ' β' ≠ s • (1 : Matrix (Fin n) (Fin n) K) := by
  intro hs
  have hv := congrArg (fun M => M *ᵥ e 1) hs
  simp only [triRk1] at hv
  simp only [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    rk1_mulVec, dotProduct_add, dotProduct_smul, hee, heg, hge] at hv
  have := congrArg (dotProduct (φ 1)) hv
  simp [dotProduct_add, dotProduct_smul, hee, heg] at this
  exact hβ' this

theorem dot_vecMul_pow_mulVec (ψ x : Fin n → K) (M N : Matrix (Fin n) (Fin n) K) :
    (ψ ᵥ* M) ⬝ᵥ (N *ᵥ x) = ψ ⬝ᵥ ((M * N) *ᵥ x) := by
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem frame_dot {Bm Bi : Matrix (Fin n) (Fin n) K} {l : K} (hl : l ≠ 0)
    (hB3 : Bm ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hBi : Bi = l⁻¹ • Bm ^ 2)
    (ψ x : Fin n → K) (c : K) (hk : ∀ k : ℕ, k < 3 → ψ ⬝ᵥ ((Bm ^ k) *ᵥ x) = if k = 0 then c else 0)
    (i j : Fin 3) :
    (ψ ᵥ* Bi ^ (i : ℕ)) ⬝ᵥ ((Bm ^ (j : ℕ)) *ᵥ x) = if i = j then c else 0 := by
  have h4 : Bm ^ 4 = l • Bm := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hB3, pow_one, smul_mul_assoc, Matrix.one_mul]
  have h5 : Bm ^ 5 = l • Bm ^ 2 := by
    rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, hB3, smul_mul_assoc, Matrix.one_mul]
  have hBi2 : Bi ^ 2 = l⁻¹ • Bm := by
    rw [pow_two, hBi, smul_mul_smul_comm, ← pow_add, h4, smul_smul, mul_assoc,
      inv_mul_cancel₀ hl, mul_one]
  have hBi1 : Bi ^ 1 = l⁻¹ • Bm ^ 2 := by rw [pow_one, hBi]
  have hmat : ∀ i j : ℕ, i < 3 → j < 3 → ∃ (d : K) (k : ℕ), k < 3 ∧ (k = 0 ↔ i = j) ∧
      (i = j → d = 1) ∧ Bi ^ i * Bm ^ j = d • Bm ^ k := by
    intro i j hi hj
    have hinv : l⁻¹ • l • (1 : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [smul_smul, inv_mul_cancel₀ hl, one_smul]
    interval_cases i <;> interval_cases j
    · exact ⟨1, 0, by norm_num, by simp, fun _ => rfl, by simp⟩
    · exact ⟨1, 1, by norm_num, by simp, by simp, by simp⟩
    · exact ⟨1, 2, by norm_num, by simp, by simp, by simp⟩
    · exact ⟨l⁻¹, 2, by norm_num, by simp, by simp, by simp [hBi1]⟩
    · refine ⟨1, 0, by norm_num, by simp, fun _ => rfl, ?_⟩
      rw [hBi1, smul_mul_assoc, pow_one, ← pow_succ, hB3, hinv]; simp
    · refine ⟨1, 1, by norm_num, by simp, by simp, ?_⟩
      rw [hBi1, smul_mul_assoc, ← pow_add, show 2 + 2 = 4 from rfl, h4, smul_smul,
        inv_mul_cancel₀ hl]; simp
    · refine ⟨l⁻¹, 1, by norm_num, by simp, by simp, ?_⟩
      rw [hBi2]; simp
    · refine ⟨l⁻¹, 2, by norm_num, by simp, by simp, ?_⟩
      rw [hBi2, smul_mul_assoc, pow_one, ← pow_two]
    · refine ⟨1, 0, by norm_num, by simp, fun _ => rfl, ?_⟩
      rw [hBi2, smul_mul_assoc, ← pow_succ', hB3, hinv]; simp
  obtain ⟨d, k, hk3, hk0, hd1, hM⟩ := hmat i j i.2 j.2
  rw [dot_vecMul_pow_mulVec, hM, Matrix.smul_mulVec, dotProduct_smul, hk k hk3]
  have hij : i = j ↔ (i : ℕ) = j := Fin.ext_iff
  by_cases h : i = j
  · have h1 := hk0.2 (hij.1 h)
    simp [h, h1, hd1 (hij.1 h)]
  · have h1 : ¬ k = 0 := fun h' => h (hij.2 (hk0.1 h'))
    simp [h, h1]

theorem hasFixedThreePair_conjAut_of_nonCube {ℓ f : ℕ} [Finite K] [hℓ : Fact ℓ.Prime]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hf : 1 ≤ f) (h3 : 3 ∣ Nat.card K - 1) (hn : 6 ≤ n)
    (B : GL (Fin n) K) {l : K}
    (hB3 : ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K))
    (hl : ∀ x : K, x ^ 3 ≠ l) : HasFixedThreePair (conjAut n K B) := by
  classical
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    rw [hK] at h3
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have hpos : 0 < 3 ^ f := by positivity
    have h4 := Nat.dvd_sub h1 h3
    rw [show 3 ^ f - (3 ^ f - 1) = 1 by omega] at h4
    omega
  have h3K : (3 : K) ≠ 0 := by
    intro h0
    have : ((3 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K ℓ] at this
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_three).1 this)
  set Bm : Matrix (Fin n) (Fin n) K := ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBm
  set Bi : Matrix (Fin n) (Fin n) K :=
    (((B : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hBi
  have hBB : Bm * Bi = 1 := by rw [hBm, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hBB' : Bi * Bm = 1 := by rw [hBm, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hl0 : l ≠ 0 := by
    rintro rfl
    have hdet : Bm.det * Bi.det = 1 := by rw [← Matrix.det_mul, hBB, Matrix.det_one]
    have h1 := congrArg Matrix.det hB3
    rw [Matrix.det_pow, zero_smul, ] at h1
    have hn0 : Matrix.det (0 : Matrix (Fin n) (Fin n) K) = 0 := by
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      exact Matrix.det_zero
    rw [hn0] at h1
    have : Bm.det = 0 := pow_eq_zero_iff (by norm_num) |>.1 h1
    rw [this, zero_mul] at hdet
    exact zero_ne_one hdet
  have hBiEq : Bi = l⁻¹ • Bm ^ 2 := by
    have h1 : Bm * (l⁻¹ • Bm ^ 2) = 1 := by
      rw [Matrix.mul_smul, ← pow_succ', hB3, smul_smul, inv_mul_cancel₀ hl0, one_smul]
    calc Bi = Bi * (Bm * (l⁻¹ • Bm ^ 2)) := by rw [h1, Matrix.mul_one]
      _ = l⁻¹ • Bm ^ 2 := by rw [← Matrix.mul_assoc, hBB', Matrix.one_mul]
  obtain ⟨u, u', ψ, ψ', hψu, hψ'u', hψu', hψ'u⟩ := exists_lin_frame hn Bm hB3 hl
  set e : Fin 3 → Fin n → K := fun i => (Bm ^ (i : ℕ)) *ᵥ u with he
  set g : Fin 3 → Fin n → K := fun i => (Bm ^ (i : ℕ)) *ᵥ u' with hg
  set φ : Fin 3 → Fin n → K := fun i => ψ ᵥ* Bi ^ (i : ℕ) with hφ
  set φ' : Fin 3 → Fin n → K := fun i => ψ' ᵥ* Bi ^ (i : ℕ) with hφ'
  have hee : ∀ i j, φ i ⬝ᵥ e j = 0 := fun i j => by
    have := frame_dot hl0 hB3 hBiEq ψ u 0 (fun k hk => by rw [hψu k hk]; simp) i j
    simpa using this
  have hgg : ∀ i j, φ' i ⬝ᵥ g j = 0 := fun i j => by
    have := frame_dot hl0 hB3 hBiEq ψ' u' 0 (fun k hk => by rw [hψ'u' k hk]; simp) i j
    simpa using this
  have heg : ∀ i j, φ i ⬝ᵥ g j = if i = j then 1 else 0 := fun i j =>
    frame_dot hl0 hB3 hBiEq ψ u' 1 hψu' i j
  have hge : ∀ i j, φ' i ⬝ᵥ e j = if i = j then 1 else 0 := fun i j =>
    frame_dot hl0 hB3 hBiEq ψ' u 1 hψ'u i j
  have step : ∀ (x : Fin n → K) (k : ℕ), Bm *ᵥ ((Bm ^ k) *ᵥ x) = (Bm ^ (k + 1)) *ᵥ x :=
    fun x k => by rw [Matrix.mulVec_mulVec, ← pow_succ']
  have stepf : ∀ (x : Fin n → K) (k : ℕ), (x ᵥ* Bi ^ k) ᵥ* Bi = x ᵥ* Bi ^ (k + 1) :=
    fun x k => by rw [Matrix.vecMul_vecMul, ← pow_succ]
  have wrap : ∀ x : Fin n → K, Bm *ᵥ ((Bm ^ 2) *ᵥ x) = l • x := fun x => by
    rw [step x 2, pow_three_mulVec hB3]
  have hBi3 : Bi ^ 3 = l⁻¹ • (1 : Matrix (Fin n) (Fin n) K) := by
    have hc : Commute Bi Bm := hBB'.trans hBB.symm
    have h1 : Bi ^ 3 * Bm ^ 3 = 1 := by
      rw [← hc.mul_pow, hBB', one_pow]
    rw [hB3, Matrix.mul_smul, Matrix.mul_one] at h1
    calc Bi ^ 3 = l⁻¹ • l • Bi ^ 3 := by rw [smul_smul, inv_mul_cancel₀ hl0, one_smul]
      _ = _ := by rw [h1]
  have hwrapf : ∀ x : Fin n → K, (x ᵥ* Bi ^ 2) ᵥ* Bi = l⁻¹ • x := fun x => by
    rw [stepf x 2, hBi3, Matrix.vecMul_smul, Matrix.vecMul_one]
  have he01 : Bm *ᵥ e 0 = e 1 := step u 0
  have he12 : Bm *ᵥ e 1 = e 2 := step u 1
  have he20 : Bm *ᵥ e 2 = l • e 0 := by
    show Bm *ᵥ ((Bm ^ 2) *ᵥ u) = l • ((Bm ^ 0) *ᵥ u)
    rw [wrap, pow_zero, Matrix.one_mulVec]
  have hg01 : Bm *ᵥ g 0 = g 1 := step u' 0
  have hg12 : Bm *ᵥ g 1 = g 2 := step u' 1
  have hg20 : Bm *ᵥ g 2 = l • g 0 := by
    show Bm *ᵥ ((Bm ^ 2) *ᵥ u') = l • ((Bm ^ 0) *ᵥ u')
    rw [wrap, pow_zero, Matrix.one_mulVec]
  have hf01 : φ 0 ᵥ* Bi = φ 1 := stepf ψ 0
  have hf12 : φ 1 ᵥ* Bi = φ 2 := stepf ψ 1
  have hf20 : φ 2 ᵥ* Bi = l⁻¹ • φ 0 := by
    show (ψ ᵥ* Bi ^ 2) ᵥ* Bi = l⁻¹ • (ψ ᵥ* Bi ^ 0)
    rw [hwrapf, pow_zero, Matrix.vecMul_one]
  have hf01' : φ' 0 ᵥ* Bi = φ' 1 := stepf ψ' 0
  have hf12' : φ' 1 ᵥ* Bi = φ' 2 := stepf ψ' 1
  have hf20' : φ' 2 ᵥ* Bi = l⁻¹ • φ' 0 := by
    show (ψ' ᵥ* Bi ^ 2) ᵥ* Bi = l⁻¹ • (ψ' ᵥ* Bi ^ 0)
    rw [hwrapf, pow_zero, Matrix.vecMul_one]
  have hβ' : (-3 : K) ≠ 0 := neg_ne_zero.2 h3K
  let x : Matrix.SpecialLinearGroup (Fin n) K := ⟨triRk1 e φ 1, det_triRk1 hee 1⟩
  let y : Matrix.SpecialLinearGroup (Fin n) K := ⟨triRk1 g φ' (-3), det_triRk1 hgg (-3)⟩
  have hxv : (x : Matrix (Fin n) (Fin n) K) = triRk1 e φ 1 := rfl
  have hyv : (y : Matrix (Fin n) (Fin n) K) = triRk1 g φ' (-3) := rfl
  refine hasFixedThreePair_of_sl_pair (conjAut n K B) x y ℓ hℓ.out hℓ3 ?_ ?_ ?_ ?_ ?_ ?_
  · refine fixed_conjAut_of_commute B x ?_
    rw [hxv]
    exact triRk1_commute hee hBB hBB' hl0 1 he01 he12 he20 hf01 hf12 hf20
  · refine fixed_conjAut_of_commute B y ?_
    rw [hyv]
    exact triRk1_commute hgg hBB hBB' hl0 (-3) hg01 hg12 hg20 hf01' hf12' hf20'
  · exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, hxv, triRk1_pow_char hee]; rfl)
  · exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, hyv, triRk1_pow_char hgg]; rfl)
  · exact Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, hxv, hyv]
      exact triRk1_pair_cube hee hgg heg hge (by norm_num))
  · intro s
    rw [Matrix.SpecialLinearGroup.coe_mul, hxv, hyv]
    exact triRk1_pair_not_scalar hee heg hge hβ' s

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
