module

public import Mathlib

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo

open Matrix

namespace HeisP

variable {K : Type*} [Field K] {n : ℕ}

local notation "sc" => Matrix.GeneralLinearGroup.scalar (Fin n)

lemma sc_zpow (c : Kˣ) (i : ℤ) : (sc c : GL (Fin n) K) ^ i = sc (c ^ i) :=
  (map_zpow (Matrix.GeneralLinearGroup.scalar (Fin n)) c i).symm

variable {A B : GL (Fin n) K} {ω : Kˣ}

lemma rel_AB (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) : A * B * A⁻¹ = sc ω * B := by
  calc A * B * A⁻¹ = (A * B * A⁻¹ * B⁻¹) * B := by group
    _ = sc ω * B := by rw [hAB]

lemma rel_BA (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) : B * A * B⁻¹ = sc ω⁻¹ * A := by
  have h1 : B * A * B⁻¹ * A⁻¹ = (sc ω)⁻¹ := by
    rw [← hAB]; group
  calc B * A * B⁻¹ = (B * A * B⁻¹ * A⁻¹) * A := by group
    _ = sc ω⁻¹ * A := by rw [h1, map_inv]

lemma rel_A_zpow (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (v : ℤ) :
    A * B ^ v * A⁻¹ = sc (ω ^ v) * B ^ v := by
  rw [← conj_zpow, rel_AB hAB, Commute.mul_zpow (Matrix.GeneralLinearGroup.scalar_commute ω B) v,
    sc_zpow]

lemma rel_B_zpow (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (u : ℤ) :
    B * A ^ u * B⁻¹ = sc (ω⁻¹ ^ u) * A ^ u := by
  rw [← conj_zpow, rel_BA hAB, Commute.mul_zpow (Matrix.GeneralLinearGroup.scalar_commute ω⁻¹ A) u,
    sc_zpow]

lemma rel_A_mul (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (u v : ℤ) :
    A * (A ^ u * B ^ v) * A⁻¹ = sc (ω ^ v) * (A ^ u * B ^ v) := by
  have hc : A * A ^ u = A ^ u * A := (Commute.self_zpow A u).eq
  calc A * (A ^ u * B ^ v) * A⁻¹ = A ^ u * (A * B ^ v * A⁻¹) := by
        rw [← mul_assoc, hc]; simp only [mul_assoc]
    _ = A ^ u * (sc (ω ^ v) * B ^ v) := by rw [rel_A_zpow hAB]
    _ = sc (ω ^ v) * (A ^ u * B ^ v) := by
        rw [← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute (ω ^ v) (A ^ u), mul_assoc]

lemma rel_B_mul (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (u v : ℤ) :
    B * (A ^ u * B ^ v) * B⁻¹ = sc (ω⁻¹ ^ u) * (A ^ u * B ^ v) := by
  have hc : B⁻¹ * B ^ v = B ^ v * B⁻¹ := ((Commute.self_zpow B v).inv_left).eq
  calc B * (A ^ u * B ^ v) * B⁻¹ = B * A ^ u * (B ^ v * B⁻¹) := by simp only [mul_assoc]
    _ = B * A ^ u * (B⁻¹ * B ^ v) := by rw [hc]
    _ = (B * A ^ u * B⁻¹) * B ^ v := by simp only [mul_assoc]
    _ = (sc (ω⁻¹ ^ u) * A ^ u) * B ^ v := by rw [rel_B_zpow hAB]
    _ = sc (ω⁻¹ ^ u) * (A ^ u * B ^ v) := by rw [mul_assoc]

noncomputable def tr (g : GL (Fin n) K) : K := Matrix.trace (g : Matrix (Fin n) (Fin n) K)

lemma tr_conj (h g : GL (Fin n) K) : tr (h * g * h⁻¹) = tr g := by
  unfold tr
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle]
  simp

lemma tr_sc_mul (c : Kˣ) (g : GL (Fin n) K) : tr (sc c * g) = (c : K) * tr g := by
  unfold tr
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul, Matrix.trace_smul, smul_eq_mul]

lemma eq_zero_of_scalar_mul {c : Kˣ} {t : K} (h : (c : K) * t = t) (hc : c ≠ 1) : t = 0 := by
  have h1 : ((c : K) - 1) * t = 0 := by linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (Units.ext (sub_eq_zero.1 h2)) hc
  · exact h2

lemma tr_zero {p : ℕ} (hω : IsPrimitiveRoot ω p) (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (u v : ℤ)
    (h : ¬ (p : ℤ) ∣ u ∨ ¬ (p : ℤ) ∣ v) : tr (A ^ u * B ^ v) = 0 := by
  by_cases hv : (p : ℤ) ∣ v
  · have hu : ¬ (p : ℤ) ∣ u := h.resolve_right (not_not.2 hv)
    have h1 := tr_conj B (A ^ u * B ^ v)
    rw [rel_B_mul hAB, tr_sc_mul] at h1
    refine eq_zero_of_scalar_mul h1 fun hc => hu ?_
    rw [_root_.inv_zpow] at hc
    exact (hω.zpow_eq_one_iff_dvd u).1 (inv_eq_one.1 hc)
  · have h1 := tr_conj A (A ^ u * B ^ v)
    rw [rel_A_mul hAB, tr_sc_mul] at h1
    exact eq_zero_of_scalar_mul h1 fun hc => hv ((hω.zpow_eq_one_iff_dvd v).1 hc)

lemma tr_mul_comm (g h : GL (Fin n) K) : tr (g * h) = tr (h * g) := by
  unfold tr
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm]

noncomputable def hm {p : ℕ} (A B : GL (Fin p) K) (x : Fin p × Fin p) :
    Matrix (Fin p) (Fin p) K :=
  ((A ^ (x.1 : ℕ) * B ^ (x.2 : ℕ) : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)

lemma tr_hm_inv {p : ℕ} {A B : GL (Fin p) K} {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) ω)
    (x y : Fin p × Fin p) :
    Matrix.trace (hm A B x * (((A ^ (y.1 : ℕ) * B ^ (y.2 : ℕ))⁻¹ : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K)) =
      if x = y then (p : K) else 0 := by
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  have e : hm A B (i, j) * (((A ^ (k : ℕ) * B ^ (l : ℕ))⁻¹ : GL (Fin p) K) :
      Matrix (Fin p) (Fin p) K) =
      ((A ^ (i : ℕ) * B ^ (j : ℕ) * (A ^ (k : ℕ) * B ^ (l : ℕ))⁻¹ : GL (Fin p) K) :
        Matrix (Fin p) (Fin p) K) := by
    simp only [hm, Units.val_mul]
  rw [e]
  change tr _ = _
  by_cases hij : (i, j) = (k, l)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij
    simp [tr]
  · simp only [hij, ite_false]
    have e2 : A ^ (i : ℕ) * B ^ (j : ℕ) * (A ^ (k : ℕ) * B ^ (l : ℕ))⁻¹ =
        A ^ (i : ℕ) * B ^ ((j : ℤ) - l) * A ^ (-(k : ℤ)) := by
      rw [← zpow_natCast A i, ← zpow_natCast B j, ← zpow_natCast A k, ← zpow_natCast B l]
      group
    rw [e2, tr_mul_comm]
    have e3 : A ^ (-(k : ℤ)) * (A ^ (i : ℕ) * B ^ ((j : ℤ) - l)) =
        A ^ ((i : ℤ) - k) * B ^ ((j : ℤ) - l) := by
      rw [← zpow_natCast A i]
      group
    rw [e3]
    refine tr_zero hω hAB _ _ ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hi : (i : ℤ) - k = 0 := Int.eq_zero_of_abs_lt_dvd h1 (by
      have := i.2; have := k.2; rw [abs_lt]; constructor <;> omega)
    have hj : (j : ℤ) - l = 0 := Int.eq_zero_of_abs_lt_dvd h2 (by
      have := j.2; have := l.2; rw [abs_lt]; constructor <;> omega)
    apply hij
    ext <;> simp <;> omega

lemma linearIndependent_hm {p : ℕ} {A B : GL (Fin p) K} {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0) :
    LinearIndependent K (hm A B) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg x0
  have h1 : Matrix.trace ((∑ y, g y • hm A B y) * (((A ^ (x0.1 : ℕ) * B ^ (x0.2 : ℕ))⁻¹ :
      GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) = 0 := by rw [hg, zero_mul, trace_zero]
  rw [Finset.sum_mul, Matrix.trace_sum] at h1
  simp only [Matrix.smul_mul, Matrix.trace_smul, tr_hm_inv hω hAB, smul_eq_mul] at h1
  rw [Finset.sum_eq_single x0 (fun y _ hy => by simp [hy]) (fun h => absurd (Finset.mem_univ _) h)]
    at h1
  simp only [ite_true, mul_eq_zero] at h1
  exact h1.resolve_right hpK

lemma commutant_scalar {p : ℕ} [NeZero p] {A B : GL (Fin p) K} {ω : Kˣ}
    (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0)
    (X : Matrix (Fin p) (Fin p) K) (hXA : X * (A : Matrix (Fin p) (Fin p) K) = A * X)
    (hXB : X * (B : Matrix (Fin p) (Fin p) K) = B * X) :
    ∃ c : K, X = Matrix.scalar (Fin p) c := by
  have hind := linearIndependent_hm hω hAB hpK
  have hcard : Fintype.card (Fin p × Fin p) = Module.finrank K (Matrix (Fin p) (Fin p) K) := by
    simp [Module.finrank_matrix]
  let b := basisOfLinearIndependentOfCardEqFinrank' (hm A B) hind hcard
  have hXA' : Commute X (A : Matrix (Fin p) (Fin p) K) := hXA
  have hXB' : Commute X (B : Matrix (Fin p) (Fin p) K) := hXB
  have hcomm : ∀ x, Commute X (hm A B x) := by
    intro x
    simp only [hm, Units.val_mul, Units.val_pow_eq_pow_val]
    exact (hXA'.pow_right _).mul_right (hXB'.pow_right _)
  have hall : ∀ Y : Matrix (Fin p) (Fin p) K, Commute X Y := by
    have hlin : (LinearMap.mulLeft K X) = (LinearMap.mulRight K X) := by
      refine b.ext fun x => ?_
      have hbx : b x = hm A B x :=
        congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' (hm A B) hind hcard) x
      simp only [LinearMap.mulLeft_apply, LinearMap.mulRight_apply, hbx]
      exact (hcomm x).eq
    intro Y
    have := congrArg (fun f => f Y) hlin
    exact this
  have := Matrix.mem_range_scalar_of_commute_single (fun i j _ => (hall (Matrix.single i j 1)).symm)
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc.symm⟩

lemma conjB_pow_A (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (j : ℕ) :
    B ^ j * A * (B ^ j)⁻¹ = sc (ω⁻¹ ^ j) * A := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : B ^ (j + 1) * A * (B ^ (j + 1))⁻¹ = B * (B ^ j * A * (B ^ j)⁻¹) * B⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]; simp only [mul_assoc]
    rw [e, ih]
    calc B * (sc (ω⁻¹ ^ j) * A) * B⁻¹ = sc (ω⁻¹ ^ j) * (B * A * B⁻¹) := by
          rw [← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute (ω⁻¹ ^ j) B]
          simp only [mul_assoc]
      _ = sc (ω⁻¹ ^ (j + 1)) * A := by
          rw [rel_BA hAB, ← mul_assoc, ← map_mul, pow_succ]

lemma conjA_pow_B (hAB : A * B * A⁻¹ * B⁻¹ = sc ω) (i : ℕ) :
    A ^ i * B * (A ^ i)⁻¹ = sc (ω ^ i) * B := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : A ^ (i + 1) * B * (A ^ (i + 1))⁻¹ = A * (A ^ i * B * (A ^ i)⁻¹) * A⁻¹ := by
      rw [pow_succ', _root_.mul_inv_rev]; simp only [mul_assoc]
    rw [e, ih]
    calc A * (sc (ω ^ i) * B) * A⁻¹ = sc (ω ^ i) * (A * B * A⁻¹) := by
          rw [← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute (ω ^ i) A]
          simp only [mul_assoc]
      _ = sc (ω ^ (i + 1)) * B := by
          rw [rel_AB hAB, ← mul_assoc, ← map_mul, pow_succ]

lemma conj_sc_mul (g h : GL (Fin n) K) (c : Kˣ) :
    g * (sc c * h) * g⁻¹ = sc c * (g * h * g⁻¹) := by
  rw [← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute c g]
  simp only [mul_assoc]

lemma coe_mul_eq_of_conj_eq {g h : GL (Fin n) K} (e : g * h * g⁻¹ = h) :
    (g : Matrix (Fin n) (Fin n) K) * h = h * g := by
  have : g * h = h * g := by rw [mul_inv_eq_iff_eq_mul] at e; exact e
  simpa [Units.val_mul] using congrArg Units.val this

end HeisP

open HeisP in
theorem heisenberg_normalizer_p {K : Type*} [Field K] {p : ℕ} [NeZero p] {A B : GL (Fin p) K}
    {ω : Kˣ} (hω : IsPrimitiveRoot ω p)
    (hAB : A * B * A⁻¹ * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) ω) (hpK : (p : K) ≠ 0)
    {C : GL (Fin p) K} {a b : Kˣ} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hCA : C * A * C⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) a * A)
    (hCB : C * B * C⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) b * B) :
    ∃ (i j : ℕ) (m : Kˣ), C = A ^ i * B ^ j * Matrix.GeneralLinearGroup.scalar (Fin p) m := by
  have hω' : IsPrimitiveRoot (ω : K) p := IsPrimitiveRoot.coe_units_iff.2 hω
  obtain ⟨u, hu, hua⟩ := hω'.eq_pow_of_pow_eq_one (ξ := (a : K))
    (by rw [← Units.val_pow_eq_pow_val, ha, Units.val_one])
  obtain ⟨v, hv, hvb⟩ := hω'.eq_pow_of_pow_eq_one (ξ := (b : K))
    (by rw [← Units.val_pow_eq_pow_val, hb, Units.val_one])
  have hua' : ω ^ u = a := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hua)
  have hvb' : ω ^ v = b := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hvb)
  have hωp : ω ^ p = 1 := hω.pow_eq_one
  set j := p - u with hj
  obtain ⟨M, hM⟩ : ∃ M : GL (Fin p) K, M = A ^ v * B ^ j := ⟨_, rfl⟩
  have hcAv : A ^ v * A * (A ^ v)⁻¹ = A := by
    have := (Commute.pow_left (Commute.refl A) v).eq
    rw [this]; group
  have hMA : M * A * M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * A := by
    calc M * A * M⁻¹ = A ^ v * (B ^ j * A * (B ^ j)⁻¹) * (A ^ v)⁻¹ := by
          rw [hM, _root_.mul_inv_rev]; simp only [mul_assoc]
      _ = A ^ v * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * A) * (A ^ v)⁻¹ := by
          rw [conjB_pow_A hAB]
      _ = _ := by rw [conj_sc_mul, hcAv]
  have hMB : M * B * M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) * B := by
    have hcBj : B ^ j * B * (B ^ j)⁻¹ = B := by
      have := (Commute.pow_left (Commute.refl B) j).eq
      rw [this]; group
    calc M * B * M⁻¹ = A ^ v * (B ^ j * B * (B ^ j)⁻¹) * (A ^ v)⁻¹ := by
          rw [hM, _root_.mul_inv_rev]; simp only [mul_assoc]
      _ = A ^ v * B * (A ^ v)⁻¹ := by rw [hcBj]
      _ = _ := conjA_pow_B hAB v
  have hMA' : M⁻¹ * A * M = Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) * A := by
    have h1 : A = M⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * A) * M := by
      rw [← hMA]; group
    have h2 : M⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * A) * M =
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * (M⁻¹ * A * M) := by
      have := conj_sc_mul M⁻¹ A (ω⁻¹ ^ j)
      rw [inv_inv] at this; exact this
    rw [h2] at h1
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) * A =
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) *
          (Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) * (M⁻¹ * A * M)) := by
      rw [← h1]
    have h4 : Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) *
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ j) = 1 := by
      rw [← map_mul, inv_pow, mul_inv_cancel, map_one]
    rw [h3, ← mul_assoc, h4, one_mul]
  have hMB' : M⁻¹ * B * M = Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) * B := by
    have h1 : B = M⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) * B) * M := by
      rw [← hMB]; group
    have h2 : M⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) * B) * M =
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) * (M⁻¹ * B * M) := by
      have := conj_sc_mul M⁻¹ B (ω ^ v)
      rw [inv_inv] at this; exact this
    rw [h2] at h1
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) * B =
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) *
          (Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) * (M⁻¹ * B * M)) := by
      rw [← h1]
    have h4 : Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) *
        Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ v) = 1 := by
      rw [← map_mul, inv_pow, inv_mul_cancel, map_one]
    rw [h3, ← mul_assoc, h4, one_mul]
  have hC'A : (C * M⁻¹) * A * (C * M⁻¹)⁻¹ = A := by
    calc (C * M⁻¹) * A * (C * M⁻¹)⁻¹ = C * (M⁻¹ * A * M) * C⁻¹ := by
          simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
      _ = C * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) * A) * C⁻¹ := by rw [hMA']
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) * (C * A * C⁻¹) := conj_sc_mul _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω ^ j) *
            (Matrix.GeneralLinearGroup.scalar (Fin p) a * A) := by rw [hCA]
      _ = A := by
          rw [← mul_assoc, ← map_mul, ← hua', ← pow_add, show j + u = p by omega, hωp, map_one,
            one_mul]
  have hC'B : (C * M⁻¹) * B * (C * M⁻¹)⁻¹ = B := by
    calc (C * M⁻¹) * B * (C * M⁻¹)⁻¹ = C * (M⁻¹ * B * M) * C⁻¹ := by
          simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
      _ = C * (Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) * B) * C⁻¹ := by rw [hMB']
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) * (C * B * C⁻¹) := conj_sc_mul _ _ _
      _ = Matrix.GeneralLinearGroup.scalar (Fin p) (ω⁻¹ ^ v) *
            (Matrix.GeneralLinearGroup.scalar (Fin p) b * B) := by rw [hCB]
      _ = B := by
          rw [← mul_assoc, ← map_mul, ← hvb', inv_pow, inv_mul_cancel, map_one, one_mul]
  obtain ⟨c, hc⟩ := commutant_scalar hω hAB hpK ((C * M⁻¹ : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)
    (coe_mul_eq_of_conj_eq hC'A) (coe_mul_eq_of_conj_eq hC'B)
  have hc0 : c ≠ 0 := by
    intro h0
    have := Matrix.GeneralLinearGroup.det_ne_zero (C * M⁻¹)
    rw [hc, h0] at this
    simp at this
  refine ⟨v, j, Units.mk0 c hc0, ?_⟩
  have hCM : C * M⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 c hc0) :=
    Units.ext (by rw [hc]; simp)
  calc C = (C * M⁻¹) * M := by group
    _ = Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 c hc0) * M := by rw [hCM]
    _ = M * Matrix.GeneralLinearGroup.scalar (Fin p) (Units.mk0 c hc0) :=
        Matrix.GeneralLinearGroup.scalar_commute _ _
    _ = _ := by rw [hM]

end CFSG.HardMathSupport.Timmesfeld.LocalTwo
