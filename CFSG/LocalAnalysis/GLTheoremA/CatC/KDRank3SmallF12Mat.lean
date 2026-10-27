module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Mat

open Matrix Module

variable {K : Type} [Field K]

theorem comm2_mem_span {p q r s : K} (hG : q ≠ 0 ∨ r ≠ 0 ∨ p ≠ s)
    {X : Matrix (Fin 2) (Fin 2) K} (hX : X * !![p, q; r, s] = !![p, q; r, s] * X) :
    ∃ α β : K, X = α • (1 : Matrix (Fin 2) (Fin 2) K) + β • !![p, q; r, s] := by
  have e00 := congrFun (congrFun hX 0) 0
  have e01 := congrFun (congrFun hX 0) 1
  have e10 := congrFun (congrFun hX 1) 0
  have e11 := congrFun (congrFun hX 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have h1 : X 0 1 * r = q * X 1 0 := by linear_combination e00
  have h2 : q * (X 0 0 - X 1 1) = (p - s) * X 0 1 := by linear_combination e01
  have h3 : r * (X 0 0 - X 1 1) = (p - s) * X 1 0 := by linear_combination -e10
  by_cases hq : q = 0
  · by_cases hr : r = 0
    ·
      have hps : p ≠ s := by
        rcases hG with h | h | h
        · exact absurd hq h
        · exact absurd hr h
        · exact h
      have hps' : p - s ≠ 0 := sub_ne_zero.2 hps
      set β : K := (X 0 0 - X 1 1) / (p - s) with hβ
      have hd : X 0 0 - X 1 1 = β * (p - s) := by rw [hβ]; field_simp
      have hb : X 0 1 = 0 := by
        have : (p - s) * X 0 1 = 0 := by rw [← h2, hq, zero_mul]
        exact (mul_eq_zero.1 this).resolve_left hps'
      have hc : X 1 0 = 0 := by
        have : (p - s) * X 1 0 = 0 := by rw [← h3, hr, zero_mul]
        exact (mul_eq_zero.1 this).resolve_left hps'
      refine ⟨X 0 0 - β * p, β, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hq, hr] <;>
        linear_combination (-1 : K) * hd
    ·
      set β : K := X 1 0 / r with hβ
      have hc : X 1 0 = β * r := by rw [hβ]; field_simp
      have hb : X 0 1 = β * q := by
        have hX01 : X 0 1 = 0 := by
          have : X 0 1 * r = 0 := by rw [h1, hq, zero_mul]
          exact (mul_eq_zero.1 this).resolve_right hr
        rw [hX01, hq, mul_zero]
      have hd : X 0 0 - X 1 1 = β * (p - s) := by
        rw [hβ]
        have : r * (X 0 0 - X 1 1) = r * (β * (p - s)) := by
          rw [h3, hc]
          field_simp
        exact mul_left_cancel₀ hr this
      refine ⟨X 0 0 - β * p, β, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc] <;> linear_combination (-1 : K) * hd
  ·
    set β : K := X 0 1 / q with hβ
    have hb : X 0 1 = β * q := by rw [hβ]; field_simp
    have hc : X 1 0 = β * r := by
      rw [hβ]; field_simp; linear_combination -h1
    have hd : X 0 0 - X 1 1 = β * (p - s) := by
      have : q * (X 0 0 - X 1 1) = q * (β * (p - s)) := by
        rw [h2, hb]; ring
      exact mul_left_cancel₀ hq this
    refine ⟨X 0 0 - β * p, β, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc] <;> linear_combination (-1 : K) * hd


theorem trace2_of_pow3_eq_zero {X : Matrix (Fin 2) (Fin 2) K} (hX : X * X * X = 0) :
    X 0 0 + X 1 1 = 0 := by
  set t : K := X 0 0 + X 1 1 with ht
  set D : K := X 0 0 * X 1 1 - X 0 1 * X 1 0 with hD
  have hCH : X * X = t • X - D • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hD] <;> ring
  have hX3 : X * X * X = (t ^ 2 - D) • X - (t * D) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc X * X * X = (t • X - D • (1 : Matrix (Fin 2) (Fin 2) K)) * X := by rw [← hCH]
      _ = t • (X * X) - D • X := by
          rw [sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
      _ = t • (t • X - D • (1 : Matrix (Fin 2) (Fin 2) K)) - D • X := by rw [hCH]
      _ = (t ^ 2 - D) • X - (t * D) • (1 : Matrix (Fin 2) (Fin 2) K) := by module
  rw [hX3] at hX
  have e00 : (t ^ 2 - D) * X 0 0 - t * D = 0 := by
    have h := congrFun (congrFun hX 0) 0
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.zero_apply] at h
    linear_combination h
  have e11 : (t ^ 2 - D) * X 1 1 - t * D = 0 := by
    have h := congrFun (congrFun hX 1) 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      Matrix.zero_apply] at h
    linear_combination h
  have e01 : (t ^ 2 - D) * X 0 1 = 0 := by
    have h := congrFun (congrFun hX 0) 1
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      smul_eq_mul, Matrix.zero_apply] at h
    linear_combination h
  have e10 : (t ^ 2 - D) * X 1 0 = 0 := by
    have h := congrFun (congrFun hX 1) 0
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
      smul_eq_mul, Matrix.zero_apply] at h
    linear_combination h
  by_cases hne : t ^ 2 - D = 0
  ·
    have hD2 : D = t ^ 2 := by linear_combination -hne
    have htD : t * D = 0 := by linear_combination -e00 + X 0 0 * hne
    have ht3 : t ^ 3 = 0 := by rw [hD2] at htD; linear_combination htD
    exact pow_eq_zero_iff (by norm_num) |>.1 ht3
  · have hb : X 0 1 = 0 := (mul_eq_zero.1 e01).resolve_left hne
    have hc : X 1 0 = 0 := (mul_eq_zero.1 e10).resolve_left hne
    have hab : X 0 0 = X 1 1 := by
      have : (t ^ 2 - D) * (X 0 0 - X 1 1) = 0 := by linear_combination e00 - e11
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)
    have hD' : D = X 0 0 * X 1 1 := by rw [hD, hb, hc]; ring
    have ha3 : X 0 0 ^ 3 = 0 := by
      have h := e00
      rw [ht, hD', ← hab] at h
      linear_combination h
    have ha : X 0 0 = 0 := pow_eq_zero_iff (by norm_num) |>.1 ha3
    rw [ht]
    linear_combination 2 * ha - hab


theorem eq_smul_one_of_mulVec {c : K} {B : Matrix (Fin 3) (Fin 3) K}
    (h : ∀ v : Fin 3 → K, B *ᵥ v = c • v) : B = c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  have hj := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at hj
  simp [Matrix.col, Pi.single_apply, Matrix.one_apply] at hj ⊢
  exact hj

theorem eigen_pattern {B : Matrix (Fin 3) (Fin 3) K} (hK : ringChar K ≠ 2) (hB : B * B = 1)
    (hB1 : B ≠ 1) (hBm : B ≠ -1) :
    ∃ b : Basis (Fin 3) K (Fin 3 → K), ∃ s : K, s * s = 1 ∧
      ∀ i : Fin 3, B *ᵥ b i = (if i = 0 then s else -s) • b i := by
  have hc := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.isCompl_eigenspaces hK hB
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_fin_fun] at hsum
  have hr0 : Module.finrank K (LinearMap.ker (Matrix.toLin' B - 1)) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    have htop : LinearMap.ker (Matrix.toLin' B + 1) = ⊤ := by
      have := hc.sup_eq_top
      rw [h0, bot_sup_eq] at this
      exact this
    apply hBm
    have h := eq_smul_one_of_mulVec (c := -1) (B := B) (fun v => by
      have hv : v ∈ LinearMap.ker (Matrix.toLin' B + 1) := by rw [htop]; trivial
      rw [LinearMap.mem_ker] at hv
      have h2 : B *ᵥ v + v = 0 := by simpa using hv
      rw [neg_one_smul]
      exact eq_neg_of_add_eq_zero_left h2)
    rw [h, neg_one_smul]
  have hr3 : Module.finrank K (LinearMap.ker (Matrix.toLin' B - 1)) ≠ 3 := by
    intro h3
    apply hB1
    have htop : LinearMap.ker (Matrix.toLin' B - 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3, finrank_fin_fun])
    have h := eq_smul_one_of_mulVec (c := 1) (B := B) (fun v => by
      have hv : v ∈ LinearMap.ker (Matrix.toLin' B - 1) := by rw [htop]; trivial
      rw [LinearMap.mem_ker] at hv
      have h2 : B *ᵥ v - v = 0 := by simpa using hv
      rw [one_smul]
      exact sub_eq_zero.1 h2)
    rw [h, one_smul]
  by_cases h1 : Module.finrank K (LinearMap.ker (Matrix.toLin' B - 1)) = 1
  · obtain ⟨b, hb⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_eigenbasis hK hB
    refine ⟨b, 1, by ring, fun i => ?_⟩
    rw [hb i, h1]
    fin_cases i <;> simp
  · have hr2 : Module.finrank K (LinearMap.ker (Matrix.toLin' B - 1)) = 2 := by
      omega
    have hB' : (-B) * (-B) = 1 := by rw [neg_mul_neg]; exact hB
    have hker : LinearMap.ker (Matrix.toLin' (-B) - 1) = LinearMap.ker (Matrix.toLin' B + 1) := by
      rw [show Matrix.toLin' (-B) - 1 = -(Matrix.toLin' B + 1) by
        rw [map_neg]; abel]
      exact LinearMap.ker_neg _
    have hfin : Module.finrank K (LinearMap.ker (Matrix.toLin' (-B) - 1)) = 1 := by
      rw [hker]
      omega
    obtain ⟨b, hb⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_eigenbasis hK hB'
    refine ⟨b, -1, by ring, fun i => ?_⟩
    have hi := hb i
    rw [hfin] at hi
    have hneg : B *ᵥ b i = -((-B) *ᵥ b i) := by
      rw [Matrix.neg_mulVec, neg_neg]
    rw [hneg, hi]
    fin_cases i <;> simp

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Mat
