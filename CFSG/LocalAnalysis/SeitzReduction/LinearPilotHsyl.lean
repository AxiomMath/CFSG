module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Relations

variable {K : Type*} [Field K] {n : ℕ}

theorem one_add_single_mul_apply (c d : Fin n) (t : K) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    ((1 + single c d t) * A) i j = A i j + if i = c then t * A d j else 0 := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply]
  by_cases hi : i = c
  · subst hi
    simp
  · simp [hi, single_mul_apply_of_ne _ _ _ _ _ hi]

theorem mul_one_add_single_apply (c d : Fin n) (t : K) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) :
    (A * (1 + single c d t)) i j = A i j + if j = d then A i c * t else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  by_cases hj : j = d
  · subst hj
    simp
  · simp [hj, mul_single_apply_of_ne _ _ _ _ _ hj]

theorem exists_mul_eq_smul_of_conjAut {A : GL (Fin n) K} {g T : SpecialLinearGroup (Fin n) K}
    (h : conjAut n K A (LinearFlag.proj n K g) = LinearFlag.proj n K T) :
    ∃ μ : Kˣ, (T : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) =
      (μ : K) • ((A : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K)) := by
  rw [conjAut_proj] at h
  obtain ⟨μ, hμ⟩ := exists_smul_of_proj_eq h
  refine ⟨μ, ?_⟩
  rw [hμ, coe_slConjugation, Matrix.smul_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem coe_map_transvection {c d : Fin n} (hcd : c ≠ d) (σ : K ≃+* K) (t : K) :
    ((Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.transvection hcd t) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + single c d (σ t) := by
  rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe]
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, single_apply,
    one_apply]
  split_ifs <;> simp

theorem coe_transpose_inv_transvection {c d : Fin n} (hcd : c ≠ d) (t : K) :
    (((Matrix.SpecialLinearGroup.transvection hcd t)⁻¹).transpose :
        Matrix (Fin n) (Fin n) K) = 1 + single d c (-t) := by
  have hinv : (Matrix.SpecialLinearGroup.transvection hcd t)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hcd (-t) := by
    refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.coe_one]
    have := Matrix.transvection_mul_transvection_same c d hcd t (-t)
    simp only [Matrix.transvection, add_neg_cancel, single_zero, add_zero] at this
    exact this
  rw [hinv, Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.transvection_coe,
    transpose_add, transpose_one, transpose_single]

theorem exists_rel_of_fix_field {A : GL (Fin n) K} {σ : K ≃+* K} {c d : Fin n} (hcd : c ≠ d)
    (t : K) (h : (conjAut n K A * fieldAut n K σ)
      (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) =
        LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) :
    ∃ μ : Kˣ, ∀ i j, (A : Matrix (Fin n) (Fin n) K) i j +
        (if i = c then t * (A : Matrix (Fin n) (Fin n) K) d j else 0) =
      (μ : K) * ((A : Matrix (Fin n) (Fin n) K) i j +
        if j = d then (A : Matrix (Fin n) (Fin n) K) i c * σ t else 0) := by
  rw [MulAut.mul_apply, fieldAut_proj] at h
  obtain ⟨μ, hμ⟩ := exists_mul_eq_smul_of_conjAut h
  rw [coe_map_transvection, Matrix.SpecialLinearGroup.transvection_coe] at hμ
  refine ⟨μ, fun i j => ?_⟩
  have := congrFun (congrFun hμ i) j
  rw [one_add_single_mul_apply, Matrix.smul_apply, mul_one_add_single_apply, smul_eq_mul] at this
  exact this

theorem exists_rel_of_fix_graph {A : GL (Fin n) K} {σ : K ≃+* K} {c d : Fin n} (hcd : c ≠ d)
    (t : K) (h : (conjAut n K A * fieldAut n K σ * dualAut n K)
      (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) =
        LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) :
    ∃ μ : Kˣ, ∀ i j, (A : Matrix (Fin n) (Fin n) K) i j +
        (if i = c then t * (A : Matrix (Fin n) (Fin n) K) d j else 0) =
      (μ : K) * ((A : Matrix (Fin n) (Fin n) K) i j +
        if j = c then (A : Matrix (Fin n) (Fin n) K) i d * σ (-t) else 0) := by
  rw [MulAut.mul_apply, MulAut.mul_apply, dualAut_proj, fieldAut_proj] at h
  obtain ⟨μ, hμ⟩ := exists_mul_eq_smul_of_conjAut h
  have hM : ((Matrix.SpecialLinearGroup.map σ.toRingHom
      ((Matrix.SpecialLinearGroup.transvection hcd t)⁻¹).transpose :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + single d c (σ (-t)) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_transpose_inv_transvection]
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, single_apply,
      one_apply]
    split_ifs <;> simp
  rw [hM, Matrix.SpecialLinearGroup.transvection_coe] at hμ
  refine ⟨μ, fun i j => ?_⟩
  have := congrFun (congrFun hμ i) j
  rw [one_add_single_mul_apply, Matrix.smul_apply, mul_one_add_single_apply, smul_eq_mul] at this
  exact this

theorem eq_one_of_forall_apply_eq_mul (hn : 3 ≤ n) {A : GL (Fin n) K} {c d : Fin n} {μ : Kˣ}
    (h : ∀ i j, i ≠ c → j ≠ d →
      (A : Matrix (Fin n) (Fin n) K) i j = (μ : K) * (A : Matrix (Fin n) (Fin n) K) i j) :
    μ = 1 := by
  by_contra hμ
  have hμ' : (1 : K) - μ ≠ 0 := sub_ne_zero.2 fun h => hμ (Units.ext h.symm)
  have hzero : ∀ i j, i ≠ c → j ≠ d → (A : Matrix (Fin n) (Fin n) K) i j = 0 := fun i j hi hj =>
    (mul_eq_zero.1 (by linear_combination h i j hi hj :
      ((1 : K) - μ) * (A : Matrix (Fin n) (Fin n) K) i j = 0)).resolve_left hμ'
  obtain ⟨j₁, j₂, hj₁, hj₂, hj⟩ : ∃ j₁ j₂ : Fin n, j₁ ≠ d ∧ j₂ ≠ d ∧ j₁ ≠ j₂ := by
    have hcard : 2 ≤ ((Finset.univ : Finset (Fin n)).erase d).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ d), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨j₁, h₁, j₂, h₂, h⟩ := Finset.one_lt_card.1 hcard
    exact ⟨j₁, j₂, Finset.ne_of_mem_erase h₁, Finset.ne_of_mem_erase h₂, h⟩
  exact Matrix.GeneralLinearGroup.det_ne_zero A (det_eq_zero_of_cols (c := c) hj
    (fun i hi => hzero i j₁ hi hj₁) (fun i hi => hzero i j₂ hi hj₂))

end Relations

section FixBlock

variable {K : Type*} [Field K] {n : ℕ}

theorem false_of_fix_graph (hn : 3 ≤ n) {J : Finset (Fin n)} (hJ : 3 ≤ J.card)
    {A : GL (Fin n) K} {σ : K ≃+* K}
    (hβ : ∀ x ∈ blockSL J, (conjAut n K A * fieldAut n K σ * dualAut n K) x = x) : False := by
  obtain ⟨c₁, c₂, d, hc₁, hc₂, hd, h12, h1d, h2d⟩ := Finset.two_lt_card_iff.1 hJ
  have hσ : σ (-1) = -1 := by rw [map_neg, map_one]
  have hcol : ∀ c ∈ J, c ≠ d → ∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i d = 0 := by
    intro c hc hcd i hi
    obtain ⟨μ, hμ⟩ := exists_rel_of_fix_graph hcd 1
      (hβ _ (proj_transvection_mem_blockSL hcd hc hd 1))
    have hμ1 : μ = 1 := eq_one_of_forall_apply_eq_mul hn (c := c) (d := c) fun i j hi hj => by
      have := hμ i j
      simpa [hi, hj] using this
    have := hμ i c
    rw [hμ1, hσ] at this
    simp only [hi, ite_false, ite_true, add_zero, Units.val_one, one_mul] at this
    linear_combination this
  apply Matrix.GeneralLinearGroup.det_ne_zero A
  refine det_eq_zero_of_col (j := d) fun i => ?_
  by_cases hi : i = c₁
  · exact hcol c₂ hc₂ h2d i (hi ▸ h12)
  · exact hcol c₁ hc₁ h1d i hi

theorem rel_of_fix_field (hn : 3 ≤ n) {A : GL (Fin n) K} {σ : K ≃+* K} {c d : Fin n}
    (hcd : c ≠ d) (t : K) (h : (conjAut n K A * fieldAut n K σ)
      (LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) =
        LinearFlag.proj n K (Matrix.SpecialLinearGroup.transvection hcd t)) :
    (∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i c * σ t = 0) ∧
      (∀ j, j ≠ d → t * (A : Matrix (Fin n) (Fin n) K) d j = 0) ∧
        t * (A : Matrix (Fin n) (Fin n) K) d d = (A : Matrix (Fin n) (Fin n) K) c c * σ t := by
  obtain ⟨μ, hμ⟩ := exists_rel_of_fix_field hcd t h
  have hμ1 : μ = 1 := eq_one_of_forall_apply_eq_mul hn (c := c) (d := d) fun i j hi hj => by
    have := hμ i j
    simpa [hi, hj] using this
  subst hμ1
  refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
  · have := hμ i d
    simp only [hi, ite_false, ite_true, add_zero, Units.val_one, one_mul] at this
    linear_combination -this
  · have := hμ c j
    simp only [hj, ite_false, ite_true, add_zero, Units.val_one, one_mul] at this
    linear_combination this
  · have := hμ c d
    simp only [ite_true, Units.val_one, one_mul] at this
    linear_combination this

theorem fix_field_struct (hn : 3 ≤ n) {J : Finset (Fin n)} (hJ : 2 ≤ J.card) {A : GL (Fin n) K}
    {σ : K ≃+* K} (hβ : ∀ x ∈ blockSL J, (conjAut n K A * fieldAut n K σ) x = x) :
    σ = 1 ∧ ∀ c ∈ J, ∀ d ∈ J, c ≠ d →
      (∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i c = 0) ∧
        (∀ j, j ≠ d → (A : Matrix (Fin n) (Fin n) K) d j = 0) ∧
          (A : Matrix (Fin n) (Fin n) K) c c = (A : Matrix (Fin n) (Fin n) K) d d := by
  have hpair : ∀ c ∈ J, ∀ d ∈ J, ∀ hcd : c ≠ d, ∀ t : K,
      (∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i c * σ t = 0) ∧
        (∀ j, j ≠ d → t * (A : Matrix (Fin n) (Fin n) K) d j = 0) ∧
          t * (A : Matrix (Fin n) (Fin n) K) d d = (A : Matrix (Fin n) (Fin n) K) c c * σ t :=
    fun c hc d hd hcd t =>
      rel_of_fix_field hn hcd t (hβ _ (proj_transvection_mem_blockSL hcd hc hd t))
  have hstruct : ∀ c ∈ J, ∀ d ∈ J, c ≠ d →
      (∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i c = 0) ∧
        (∀ j, j ≠ d → (A : Matrix (Fin n) (Fin n) K) d j = 0) ∧
          (A : Matrix (Fin n) (Fin n) K) c c = (A : Matrix (Fin n) (Fin n) K) d d := by
    intro c hc d hd hcd
    obtain ⟨h1, h2, h3⟩ := hpair c hc d hd hcd 1
    refine ⟨fun i hi => ?_, fun j hj => ?_, ?_⟩
    · simpa using h1 i hi
    · simpa using h2 j hj
    · simpa using h3.symm
  refine ⟨?_, hstruct⟩
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
  obtain ⟨hcol, -, hdiag⟩ := hstruct c hc d hd hcd
  have hcc : (A : Matrix (Fin n) (Fin n) K) c c ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    refine det_eq_zero_of_col (j := c) fun i => ?_
    by_cases hi : i = c
    · rw [hi, h0]
    · exact hcol i hi
  refine RingEquiv.ext fun t => ?_
  have h3 := (hpair c hc d hd hcd t).2.2
  rw [← hdiag] at h3
  have : (A : Matrix (Fin n) (Fin n) K) c c * (σ t - t) = 0 := by linear_combination -h3
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hcc)

theorem exists_conjAut_eq_of_fix_blockSL [Finite K] (hn : 3 ≤ n) {J : Finset (Fin n)}
    (hJ : 3 ≤ J.card) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβ : ∀ x ∈ blockSL J, β x = x) :
    ∃ A : GL (Fin n) K, β = conjAut n K A ∧
      ∀ i j, (i ∈ J ∨ j ∈ J) →
        (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 β
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  swap
  · rw [pow_one] at hβ
    exact (false_of_fix_graph hn hJ hβ).elim
  rw [pow_zero, mul_one] at hβ ⊢
  obtain ⟨rfl, hstruct⟩ := fix_field_struct hn (by omega) hβ
  rw [map_one, mul_one]
  have hpartner : ∀ c ∈ J, ∃ d ∈ J, c ≠ d := fun c hc => by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
    by_cases hcx : c = x
    · exact ⟨y, hy, hcx ▸ hxy⟩
    · exact ⟨x, hx, hcx⟩
  obtain ⟨c₀, hc₀⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  have hcol : ∀ c ∈ J, ∀ i, i ≠ c → (A : Matrix (Fin n) (Fin n) K) i c = 0 := fun c hc i hi => by
    obtain ⟨d, hd, hcd⟩ := hpartner c hc
    exact (hstruct c hc d hd hcd).1 i hi
  have hrow : ∀ d ∈ J, ∀ j, j ≠ d → (A : Matrix (Fin n) (Fin n) K) d j = 0 := fun d hd j hj => by
    obtain ⟨c, hc, hdc⟩ := hpartner d hd
    exact (hstruct c hc d hd (Ne.symm hdc)).2.1 j hj
  have hdiag : ∀ c ∈ J, (A : Matrix (Fin n) (Fin n) K) c c = (A : Matrix (Fin n) (Fin n) K) c₀ c₀ :=
    fun c hc => by
      by_cases hcc : c = c₀
      · rw [hcc]
      · exact ((hstruct c₀ hc₀ c hc (Ne.symm hcc)).2.2).symm
  have hs : (A : Matrix (Fin n) (Fin n) K) c₀ c₀ ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero A
    refine det_eq_zero_of_col (j := c₀) fun i => ?_
    by_cases hi : i = c₀
    · rw [hi, h0]
    · exact hcol c₀ hc₀ i hi
  set u : Kˣ := Units.mk0 _ hs
  refine ⟨A * Matrix.GeneralLinearGroup.scalar (Fin n) u⁻¹, ?_, fun i j hij => ?_⟩
  · rw [map_mul, conjAut_scalar, mul_one]
  · rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, mul_diagonal]
    by_cases hij' : i = j
    · subst hij'
      have hiJ : i ∈ J := hij.elim id id
      rw [hdiag i hiJ, one_apply_eq]
      simp [u, hs]
    · rw [one_apply_ne hij']
      rcases hij with hi | hj
      · rw [hrow i hi j (Ne.symm hij'), zero_mul]
      · rw [hcol j hj i hij', zero_mul]

end FixBlock

section TwoElements

variable {K : Type*} [Field K] [CharP K 2]

theorem eq_one_or_pow_eq_one_of_mul_eq_mul {x u : Matrix (Fin 2) (Fin 2) K}
    (hx : ¬ (x 0 1 = 0 ∧ x 1 0 = 0 ∧ x 0 0 = x 1 1)) (hdet : x.det = 1) (hu : u * x = x * u)
    {k : ℕ} (huk : u ^ 2 ^ k = 1) : u = 1 ∨ x ^ 2 ^ k = 1 := by
  obtain ⟨s, r, rfl⟩ := exists_eq_smul_one_add_smul_of_mul_eq_mul hx hu
  have hcomm : Commute (s • (1 : Matrix (Fin 2) (Fin 2) K)) (r • x) :=
    ((Commute.one_left x).smul_left s).smul_right r
  rw [add_pow_char_pow_of_commute 2 k hcomm, smul_pow, smul_pow, one_pow] at huk
  have hs : s ^ 2 ^ k = 1 → s = 1 := fun h => by
    have h0 : (s - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, one_pow, h, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h0)
  by_cases hr : r = 0
  · left
    subst hr
    rw [zero_pow (pow_ne_zero _ two_ne_zero), zero_smul, add_zero] at huk
    have h00 := congrFun (congrFun huk 0) 0
    simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h00
    rw [hs h00, one_smul, zero_smul, add_zero]
  · right
    have hrk : r ^ 2 ^ k ≠ 0 := pow_ne_zero _ hr
    have hX : x ^ 2 ^ k = ((r ^ 2 ^ k)⁻¹ * (1 - s ^ 2 ^ k)) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h1 : (r ^ 2 ^ k) • x ^ 2 ^ k = (1 - s ^ 2 ^ k) • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [sub_smul, one_smul, eq_sub_iff_add_eq, add_comm]
        exact huk
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hrk, one_smul]
    have hdetX : (x ^ 2 ^ k).det = 1 := by rw [det_pow, hdet, one_pow]
    rw [hX, det_smul, det_one, mul_one, Fintype.card_fin] at hdetX
    rw [hX, eq_one_of_sq_eq_one hdetX, one_smul]

variable [Finite K] {n : ℕ}

theorem mul_eq_mul_of_conjAut_fix {A : GL (Fin n) K} {y : SpecialLinearGroup (Fin n) K}
    (h : conjAut n K A (LinearFlag.proj n K y) = LinearFlag.proj n K y)
    (hy : LinearFlag.proj n K y ^ (Nat.card K + 1) = 1) :
    (A : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) =
      (y : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  obtain ⟨μ, hμ⟩ := exists_mul_eq_smul_of_conjAut h
  set Y : Matrix (Fin n) (Fin n) K := (y : Matrix (Fin n) (Fin n) K) with hY
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hM
  have hpow : ∀ m : ℕ, Y ^ m * M = ((μ : K) ^ m) • (M * Y ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc Y ^ (m + 1) * M = Y * (Y ^ m * M) := by rw [pow_succ', Matrix.mul_assoc]
        _ = Y * (((μ : K) ^ m) • (M * Y ^ m)) := by rw [ih]
        _ = ((μ : K) ^ m) • ((Y * M) * Y ^ m) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = ((μ : K) ^ m) • (((μ : K) • (M * Y)) * Y ^ m) := by rw [hμ]
        _ = ((μ : K) ^ m * μ) • (M * (Y * Y ^ m)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        _ = ((μ : K) ^ (m + 1)) • (M * Y ^ (m + 1)) := by rw [← pow_succ, ← pow_succ']
  have hscal : y ^ (Nat.card K + 1) ∈ LinearFlag.scalars n K := by
    rw [← LinearFlag.ker_proj, MonoidHom.mem_ker, map_pow, hy]
  obtain ⟨c, -, hc⟩ := LinearFlag.mem_scalars.1 hscal
  rw [Matrix.SpecialLinearGroup.coe_pow] at hc
  have h1 := hpow (Nat.card K + 1)
  rw [hc, scalar_apply, ← smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul] at h1
  have hA0 : (A : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h0
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [h0, det_zero] at hdet
    exact hdet rfl
  have hμm : μ ^ (Nat.card K + 1) = 1 := by
    have h2 : ((c : K) - (μ : K) ^ (Nat.card K + 1) * c) • (A : Matrix (Fin n) (Fin n) K) = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 := (smul_eq_zero.1 h2).resolve_right hA0
    have h4 : ((1 : K) - (μ : K) ^ (Nat.card K + 1)) * c = 0 := by linear_combination h3
    have h5 := (mul_eq_zero.1 h4).resolve_right c.ne_zero
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; linear_combination -h5)
  have hμ1 := eq_one_of_pow_card_add_one hμm
  rw [hμ1, Units.val_one, one_smul] at hμ
  exact hμ.symm

end TwoElements

section Agree

variable {K : Type*} [Field K] {n : ℕ}

theorem agrees_one_mul {J : Finset (Fin n)} {M N : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (hN : ∀ i j, (i ∉ J ∨ j ∉ J) → N i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    ∀ i j, (i ∉ J ∨ j ∉ J) → (M * N) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  rw [agrees_one_iff] at hM hN ⊢
  exact ⟨by rw [Matrix.mul_assoc, hN.1, hM.1], by rw [← Matrix.mul_assoc, hM.2, hN.2]⟩

theorem agrees_one_pow {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) (m : ℕ) :
    ∀ i j, (i ∉ J ∨ j ∉ J) → (M ^ m) i j = (1 : Matrix (Fin n) (Fin n) K) i j := by
  induction m with
  | zero => exact fun i j _ => by rw [pow_zero]
  | succ m ih => exact fun i j h => by rw [pow_succ]; exact agrees_one_mul ih hM i j h

theorem submatrix_pow_of_agrees_one {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) (m : ℕ) :
    (M ^ m).submatrix e e = (M.submatrix e e) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, submatrix_one _ he]
  | succ m ih =>
    rw [pow_succ', pow_succ', submatrix_mul_of_rows he hJ
      (fun i hi k hk => (blockDiag_of_agrees_one hM) i k (by tauto)), ih]

theorem eq_one_of_agrees_one_of_submatrix_eq_one {r : ℕ} {e : Fin r → Fin n}
    (he : Function.Injective e) {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e)
    {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    (h1 : M.submatrix e e = 1) : M = 1 := by
  ext i j
  by_cases hij : i ∈ J ∧ j ∈ J
  · obtain ⟨k, rfl⟩ := (hJ i).1 hij.1
    obtain ⟨l, rfl⟩ := (hJ j).1 hij.2
    have := congrFun (congrFun h1 k) l
    rw [submatrix_apply] at this
    rw [this]
    by_cases hkl : k = l
    · subst hkl
      simp
    · rw [one_apply_ne hkl, one_apply_ne (he.ne hkl)]
  · exact hM i j (not_and_or.1 hij)

end Agree

section Hsyl

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem eq_one_of_two_group_centralizes (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hX : X ≤ rootSL2 a b)
    (hXc : Nat.card X = Nat.card K + 1) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβX : ∀ x ∈ X, β x = x) (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d)
    {k : ℕ} (hβk : β ^ 2 ^ k = 1) : β = 1 := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨A, rfl, hA⟩ := exists_conjAut_eq_of_fix_blockSL (by omega) (by omega) hβD
  have hA' : ∀ i j, (i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n))) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h =>
    hA i j (by simpa only [Finset.mem_compl] using h)
  obtain ⟨x, hxX, y, hy, rfl, hx1, hxm, hyy⟩ := exists_lift_torusQ1 hX hXc
  have hAy := mul_eq_mul_of_conjAut_fix (hβX _ hxX) hxm
  have he := pair_injective (n := n) hab
  have hJ := mem_pair_iff_mem_range (a := a) (b := b)
  have hrowsA : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      (A : Matrix (Fin n) (Fin n) K) i k = 0 := fun i hi k hk =>
    (blockDiag_of_agrees_one hA') i k (by tauto)
  have hrowsy : ∀ i ∈ ({a, b} : Finset (Fin n)), ∀ k ∉ ({a, b} : Finset (Fin n)),
      (y : Matrix (Fin n) (Fin n) K) i k = 0 := fun i hi k hk =>
    row_eq_zero_of_agrees_one hy hi k hk
  have hblock : (A : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
      (y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] =
        (y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] *
          (A : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b] := by
    rw [← submatrix_mul_of_rows he hJ hrowsA, ← submatrix_mul_of_rows he hJ hrowsy, hAy]
  have hydet : (y : Matrix (Fin n) (Fin n) K).det = 1 := y.2
  have hyy' : (y : Matrix (Fin n) (Fin n) K) * y ≠ 1 := fun h =>
    hyy (Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, h,
      Matrix.SpecialLinearGroup.coe_one]))
  have hx0 := not_scalar_submatrix_pair hab hy hydet hyy'
  have hdet0 : ((y : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b]).det = 1 := by
    rw [det_submatrix_of_agrees_one he hJ hy, hydet]
  have hAk : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1 := by
    have h1 : conjAut n K (A ^ 2 ^ k) * fieldAut n K 1 = 1 := by
      rw [map_one, mul_one, map_pow, hβk]
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by omega) _ _ h1
    have hu' : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = scalar (Fin n) (u : K) := by
      rw [← Units.val_pow_eq_pow_val, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
    obtain ⟨j, hj⟩ : ∃ j, j ∉ ({a, b} : Finset (Fin n)) := by
      by_contra h
      push Not at h
      have := Finset.card_le_card (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => h j)
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hab] at this
      omega
    have hjj := agrees_one_pow hA' (2 ^ k) j j (Or.inl hj)
    rw [hu', scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
    rw [hu', hjj, map_one]
  have hA0k : ((A : Matrix (Fin n) (Fin n) K).submatrix ![a, b] ![a, b]) ^ 2 ^ k = 1 := by
    rw [← submatrix_pow_of_agrees_one he hJ hA', hAk, submatrix_one _ he]
  rcases eq_one_or_pow_eq_one_of_mul_eq_mul hx0 hdet0 hblock hA0k with h | h
  ·
    have hA1 : (A : Matrix (Fin n) (Fin n) K) = 1 :=
      eq_one_of_agrees_one_of_submatrix_eq_one he hJ hA' h
    have : A = 1 := Units.ext hA1
    rw [this, map_one]
  ·
    exfalso
    have hyk : (y : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1 :=
      eq_one_of_agrees_one_of_submatrix_eq_one he hJ (agrees_one_pow hy _)
        (by rw [submatrix_pow_of_agrees_one he hJ hy, h])
    have hxk : LinearFlag.proj n K y ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : y ^ 2 ^ k = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_pow, hyk,
        Matrix.SpecialLinearGroup.coe_one])
      rw [this, map_one]
    have hd1 := orderOf_dvd_of_pow_eq_one hxk
    have hd2 := orderOf_dvd_of_pow_eq_one hxm
    have hcop : Nat.Coprime (2 ^ k) (Nat.card K + 1) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 odd_natCard_add_one)
    exact hx1 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2))

theorem eq_one_of_isPGroup_centralizes (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup (LinearFlag.projectiveSL n K)} (hX : X ≤ rootSL2 a b)
    (hXc : Nat.card X = Nat.card K + 1) {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβ2 : IsPGroup 2 (Subgroup.zpowers β)) (hβX : ∀ x ∈ X, β x = x)
    (hβD : ∀ d ∈ blockSL (({a, b} : Finset (Fin n))ᶜ), β d = d) : β = 1 := by
  obtain ⟨k, hk⟩ := hβ2 ⟨β, Subgroup.mem_zpowers β⟩
  exact eq_one_of_two_group_centralizes hn hab hX hXc hβX hβD (k := k)
    (congrArg Subtype.val hk)

theorem eq_one_of_two_group_fix_levi (hn : 4 ≤ n) (a : Fin n)
    {β : MulAut (LinearFlag.projectiveSL n K)}
    (hβD : ∀ d ∈ blockSL (({a} : Finset (Fin n))ᶜ), β d = d) {k : ℕ} (hβk : β ^ 2 ^ k = 1) :
    β = 1 := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  obtain ⟨A, rfl, hA⟩ := exists_conjAut_eq_of_fix_blockSL (by omega) (by omega) hβD
  have hA' : ∀ i j, (i ∉ ({a} : Finset (Fin n)) ∨ j ∉ ({a} : Finset (Fin n))) →
      (A : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j := fun i j h =>
    hA i j (by simpa only [Finset.mem_compl] using h)
  have he : Function.Injective ![a] := fun _ _ _ => Subsingleton.elim _ _
  have hJ := mem_singleton_iff_mem_range a
  have hAk : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = 1 := by
    have h1 : conjAut n K (A ^ 2 ^ k) * fieldAut n K 1 = 1 := by
      rw [map_one, mul_one, map_pow, hβk]
    obtain ⟨-, u, hu⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (by omega) _ _ h1
    have hu' : (A : Matrix (Fin n) (Fin n) K) ^ 2 ^ k = scalar (Fin n) (u : K) := by
      rw [← Units.val_pow_eq_pow_val, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
    obtain ⟨j, hj⟩ : ∃ j, j ∉ ({a} : Finset (Fin n)) := by
      by_contra h
      push Not at h
      have := Finset.card_le_card (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => h j)
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at this
      omega
    have hjj := agrees_one_pow hA' (2 ^ k) j j (Or.inl hj)
    rw [hu', scalar_apply, diagonal_apply_eq, one_apply_eq] at hjj
    rw [hu', hjj, map_one]
  have hA0k : ((A : Matrix (Fin n) (Fin n) K).submatrix ![a] ![a]) ^ 2 ^ k = 1 := by
    rw [← submatrix_pow_of_agrees_one he hJ hA', hAk, submatrix_one _ he]
  have hlam : (A : Matrix (Fin n) (Fin n) K) a a = 1 := by
    have hpow : ∀ m : ℕ, (((A : Matrix (Fin n) (Fin n) K).submatrix ![a] ![a]) ^ m) 0 0 =
        (A : Matrix (Fin n) (Fin n) K) a a ^ m := by
      intro m
      induction m with
      | zero => rw [pow_zero, pow_zero, one_apply_eq]
      | succ m ih => rw [pow_succ, mul_apply, Fin.sum_univ_one, ih, pow_succ]; rfl
    have h0 := congrFun (congrFun hA0k 0) 0
    rw [hpow, one_apply_eq] at h0
    have h00 : ((A : Matrix (Fin n) (Fin n) K) a a - 1) ^ 2 ^ k = 0 := by
      rw [sub_pow_char_pow, one_pow, h0, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h00)
  have hA1 : (A : Matrix (Fin n) (Fin n) K) = 1 := by
    refine eq_one_of_agrees_one_of_submatrix_eq_one he hJ hA' ?_
    ext i j
    fin_cases i
    fin_cases j
    simp [hlam]
  have : A = 1 := Units.ext hA1
  rw [this, map_one]

end Hsyl

section Transport

variable {G : Type*} [Group G] {L : Subgroup G}

theorem inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem {C : Type*} [Group C]
    (e : L ≃* C) {A D : Subgroup C} (hDA : D ≤ Subgroup.centralizer (A : Set C))
    (hcomm : ∀ g ∈ Subgroup.centralizer (A : Set C), ∀ h ∈ Subgroup.centralizer (A : Set C),
      g * h * g⁻¹ * h⁻¹ ∈ D) (hD : CFSG.IsQuasisimple D) :
    inSubgroup layer
        (L ⊓ Subgroup.centralizer (((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
          Set G)) =
      (D.map e.symm.toMonoidHom).map L.subtype := by
  rw [CFSG.SeitzReduction.F4Pilot.inf_centralizer_map_symm]
  refine inSubgroup_layer_eq_of_commutator_mem (Subgroup.map_mono (Subgroup.map_mono hDA))
    ?_ ?_
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨e.symm.toMonoidHom (g * h * g⁻¹ * h⁻¹),
      ⟨g * h * g⁻¹ * h⁻¹, hcomm g hg h hh, rfl⟩, ?_⟩
    simp
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
        ((D.map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)) hD

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem layer_inf_centralizer_torusQ1 (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {X : Subgroup (LinearFlag.projectiveSL n K)}
    (hX : X ≤ rootSL2 a b) (hXc : Nat.card X = Nat.card K + 1) :
    inSubgroup layer
        (L ⊓ Subgroup.centralizer (((X.map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
          Set G)) =
      ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype := by
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  exact inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (blockSL_compl_le_centralizer hX)
    (fun g hg h hh => commutator_mem_blockSL_of_mem_centralizer_torusQ1 hab hX hXc hg hh)
    (isQuasisimple_blockSL (by omega) (by omega) (Or.inl (by omega)))

omit [Finite K] [CharP K 2] in
theorem isQuasisimple_map_blockSL [Finite K] (e : L ≃* LinearFlag.projectiveSL n K)
    {I : Finset (Fin n)} (hI : I.card < n) (h2 : 2 ≤ I.card) (h : 3 ≤ I.card ∨ 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (((blockSL (K := K) I).map e.symm.toMonoidHom).map L.subtype) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (((blockSL I).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((blockSL I).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective))
    (isQuasisimple_blockSL hI h2 h)

omit [Finite K] [CharP K 2] in
theorem isQuasisimple_open_map_blockSL [Finite K] (e : L ≃* LinearFlag.projectiveSL n K)
    {I : Finset (Fin n)} (hI : I.card < n) (h2 : 2 ≤ I.card) (h : 3 ≤ I.card ∨ 4 ≤ Nat.card K) :
    CFSG.Open.IsQuasisimple (((blockSL (K := K) I).map e.symm.toMonoidHom).map L.subtype) :=
  ⟨(isQuasisimple_map_blockSL e hI h2 h).1.commutator_eq_top,
    (isQuasisimple_map_blockSL e hI h2 h).2.1⟩

omit [CharP K 2] in
theorem layer_inf_centralizer_levTorus (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n)
    (a : Fin n) (hc : ∃ c : Kˣ, c ^ n ≠ 1) :
    inSubgroup layer
        (L ⊓ Subgroup.centralizer
          ((((levTorus (K := K) a).map e.symm.toMonoidHom).map L.subtype : Subgroup G) :
            Set G)) =
      ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype := by
  have hcard : (({a} : Finset (Fin n))ᶜ).card = n - 1 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
  exact inSubgroup_layer_inf_centralizer_map_symm_of_commutator_mem e
    (blockSL_compl_le_centralizer_levTorus a)
    (fun g hg h hh => commutator_mem_blockSL_of_mem_centralizer_levTorus (by omega) hc hg hh)
    (isQuasisimple_blockSL (by omega) (by omega) (Or.inl (by omega)))

theorem eq_one_of_fix_map_torusQ1 (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n)
    {a b : Fin n} (hab : a ≠ b) {X D : Subgroup G}
    (hX : (X.subgroupOf L).map e.toMonoidHom ≤ rootSL2 a b)
    (hXc : Nat.card ((X.subgroupOf L).map e.toMonoidHom) = Nat.card K + 1)
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ k : ℕ, β ^ 2 ^ k = 1 → β = 1 := by
  intro β hβX hβD k hβk
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_two_group_centralizes hn hab hX hXc (fun x hx => ?_) (fun x hx => ?_)
      (k := k) ?_
    · obtain ⟨a, ha, rfl⟩ := hx
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hβX a (Subgroup.mem_subgroupOf.1 ha)]
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hβD _ hmem, MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβk, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem eq_one_of_fix_map_levi (e : L ≃* LinearFlag.projectiveSL n K) (hn : 4 ≤ n) (a : Fin n)
    {X D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ∀ β : MulAut L, (∀ x : L, (x : G) ∈ X → β x = x) → (∀ x : L, (x : G) ∈ D → β x = x) →
      ∀ k : ℕ, β ^ 2 ^ k = 1 → β = 1 := by
  intro β _ hβD k hβk
  have key : MulAut.congr e β = 1 := by
    refine eq_one_of_two_group_fix_levi hn a (fun x hx => ?_) (k := k) ?_
    · rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have hmem : ((e.symm x : L) : G) ∈ D := by
        rw [hDe]
        exact ⟨e.symm x, ⟨x, hx, rfl⟩, rfl⟩
      rw [hβD _ hmem, MulEquiv.apply_symm_apply]
    · rw [← map_pow, hβk, map_one]
  have := congrArg (MulAut.congr e).symm key
  rwa [MulEquiv.symm_apply_apply, map_one] at this

theorem card_le_two_of_torusQ1 [Finite G] {t : G}
    (hCtN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hK : Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) =
      Subgroup.zpowers t) (ht : orderOf t = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) {X D : Subgroup G}
    (hX : (X.subgroupOf L).map e.toMonoidHom ≤ rootSL2 a b)
    (hXc : Nat.card ((X.subgroupOf L).map e.toMonoidHom) = Nat.card K + 1)
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  CFSG.SeitzReduction.F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hK ht
    (eq_one_of_fix_map_torusQ1 e hn hab hX hXc hDe) hU hUC

theorem card_le_two_of_levi [Finite G] {t : G}
    (hCtN : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hK : Subgroup.centralizer (L : Set G) ⊓ Subgroup.centralizer ({t} : Set G) =
      Subgroup.zpowers t) (ht : orderOf t = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 4 ≤ n) (a : Fin n) {X D : Subgroup G}
    (hDe : D = ((blockSL (({a} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {U : Subgroup G} (hU : IsPGroup 2 U)
    (hUC : U ≤ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer (D : Set G)) :
    Nat.card U ≤ 2 :=
  CFSG.SeitzReduction.F4Pilot.card_le_two_of_forall_fix_eq_one hCtN hK ht
    (eq_one_of_fix_map_levi e hn a hDe) hU hUC

end Transport

end CFSG.SeitzReduction.LinearPilot
