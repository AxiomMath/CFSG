module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Struct
public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Pair

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

section Nu

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def sigU : Kˣ →* Kˣ := Units.map σ.toMonoidHom

@[expose] def nuU : Kˣ →* Kˣ := sigU σ * (sigU σ).comp (sigU σ) * (MonoidHom.id Kˣ)⁻¹

theorem nuU_apply (s : Kˣ) : nuU σ s = sigU σ s * sigU σ (sigU σ s) * s⁻¹ := rfl

variable {σ}

theorem sigU_coe (s : Kˣ) : ((sigU σ s : Kˣ) : K) = σ (s : K) := rfl

theorem sigU_neg_one : sigU σ (-1) = -1 := Units.ext (by simp [sigU_coe])

theorem nuU_injective (hσ : ∀ c, σ (σ (σ c)) = c) : Function.Injective (nuU σ) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hσ3 : ∀ a : Kˣ, sigU σ (sigU σ (sigU σ a)) = a := fun a => Units.ext (hσ _)
  set a := s with ha
  set b := sigU σ a with hb
  set c := sigU σ b with hc
  rw [nuU_apply] at hs
  have e1 : b * c = a := by
    have := hs
    rw [mul_inv_eq_one] at this
    exact this
  have e2 : c * a = b := by
    have := congrArg (sigU σ) e1
    rwa [map_mul, ← hb, ← hc, show sigU σ c = a from hσ3 a] at this
  have e3 : a * b = c := by
    have := congrArg (sigU σ) e2
    rwa [map_mul, show sigU σ c = a from hσ3 a, ← hb, ← hc] at this
  have ha2 : a * a = 1 := by
    have h : (a * a) * b = 1 * b := by
      calc a * a * b = a * (a * b) := by rw [mul_assoc]
        _ = a * c := by rw [e3]
        _ = c * a := mul_comm _ _
        _ = b := e2
        _ = 1 * b := (one_mul b).symm
    exact mul_right_cancel h
  have hsq : a = 1 ∨ a = -1 := by
    have h : (a : Kˣ) ^ 2 = 1 := by rw [sq]; exact ha2
    have h' : ((a : K)) * (a : K) = 1 := by
      rw [← Units.val_mul]; simpa using congrArg Units.val ha2
    rcases mul_self_eq_one_iff.1 h' with h1 | h1
    · exact Or.inl (Units.ext (by simpa using h1))
    · exact Or.inr (Units.ext (by simpa using h1))
  rcases hsq with h | h
  · exact h
  · have hb' : b = -1 := by rw [hb, h, sigU_neg_one]
    have hc' : c = -1 := by rw [hc, hb', sigU_neg_one]
    calc a = b * c := e1.symm
      _ = 1 := by rw [hb', hc']; simp

theorem nuU_surjective [Finite K] (hσ : ∀ c, σ (σ (σ c)) = c) : Function.Surjective (nuU σ) :=
  Finite.injective_iff_surjective.1 (nuU_injective hσ)

end Nu

section Tuples

variable {K : Type} [Field K] (σ : K →+* K)

@[expose] def tupS (s : Kˣ) : Fin d4.rank → Kˣ := fun j =>
  s ^ d4.cartan (nd 0) j * (sigU σ s) ^ d4.cartan (nd 1) j *
    (sigU σ (sigU σ s)) ^ d4.cartan (nd 3) j

variable {σ}

theorem tupS_zero (s : Kˣ) : tupS σ s (nd 0) = s ^ (2 : ℤ) := by
  show s ^ d4.cartan (nd 0) (nd 0) * (sigU σ s) ^ d4.cartan (nd 1) (nd 0) *
    (sigU σ (sigU σ s)) ^ d4.cartan (nd 3) (nd 0) = _
  rw [show d4.cartan (nd 0) (nd 0) = 2 by decide, show d4.cartan (nd 1) (nd 0) = 0 by decide,
    show d4.cartan (nd 3) (nd 0) = 0 by decide]
  simp

theorem tupS_one (s : Kˣ) : tupS σ s (nd 1) = (sigU σ s) ^ (2 : ℤ) := by
  show s ^ d4.cartan (nd 0) (nd 1) * (sigU σ s) ^ d4.cartan (nd 1) (nd 1) *
    (sigU σ (sigU σ s)) ^ d4.cartan (nd 3) (nd 1) = _
  rw [show d4.cartan (nd 0) (nd 1) = 0 by decide, show d4.cartan (nd 1) (nd 1) = 2 by decide,
    show d4.cartan (nd 3) (nd 1) = 0 by decide]
  simp

theorem tupS_two (s : Kˣ) :
    tupS σ s (nd 2) = s⁻¹ * (sigU σ s)⁻¹ * (sigU σ (sigU σ s))⁻¹ := by
  show s ^ d4.cartan (nd 0) (nd 2) * (sigU σ s) ^ d4.cartan (nd 1) (nd 2) *
    (sigU σ (sigU σ s)) ^ d4.cartan (nd 3) (nd 2) = _
  rw [show d4.cartan (nd 0) (nd 2) = -1 by decide, show d4.cartan (nd 1) (nd 2) = -1 by decide,
    show d4.cartan (nd 3) (nd 2) = -1 by decide]
  simp

theorem tupS_three (s : Kˣ) : tupS σ s (nd 3) = (sigU σ (sigU σ s)) ^ (2 : ℤ) := by
  show s ^ d4.cartan (nd 0) (nd 3) * (sigU σ s) ^ d4.cartan (nd 1) (nd 3) *
    (sigU σ (sigU σ s)) ^ d4.cartan (nd 3) (nd 3) = _
  rw [show d4.cartan (nd 0) (nd 3) = 0 by decide, show d4.cartan (nd 1) (nd 3) = 0 by decide,
    show d4.cartan (nd 3) (nd 3) = 2 by decide]
  simp

variable (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem twistedIncl_slB_HSL (s : Kˣ) :
    twistedIncl σ (slB σ hσ (HSL s)) = rootDiagUnit d4 (weylTuple tdNhat (tupS σ s)) := by
  rw [twistedIncl_slB, twistedIncl_slShort_HSL hσ, canonicalRep_conj_rootDiagUnit]
  rfl

theorem cB_zero (s : Kˣ) : weylTuple tdNhat (tupS σ s) (nd 0) = nuU σ s := by
  show rootChar (tupS σ s) (tdNhat⁻¹ • (Pi.single (nd 0) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_zero, rootChar_four, tupS_zero, tupS_two, nuU_apply]
  show (s ^ (2 : ℤ)) ^ (-1 : ℤ) * (tupS σ s (nd 1)) ^ (0 : ℤ) *
    (s⁻¹ * (sigU σ s)⁻¹ * (sigU σ (sigU σ s))⁻¹) ^ (-1 : ℤ) * (tupS σ s (nd 3)) ^ (0 : ℤ) = _
  simp only [zpow_zero, mul_one, zpow_neg, zpow_one, inv_inv, mul_inv_rev]
  apply Units.ext
  have hs := s.ne_zero
  have h1 : ((sigU σ s : Kˣ) : K) ≠ 0 := (sigU σ s).ne_zero
  have h2 : ((sigU σ (sigU σ s) : Kˣ) : K) ≠ 0 := (sigU σ (sigU σ s)).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, zpow_ofNat]
  field_simp

theorem cB_two (s : Kˣ) : weylTuple tdNhat (tupS σ s) (nd 2) = 1 := by
  show rootChar (tupS σ s) (tdNhat⁻¹ • (Pi.single (nd 2) 1 : Fin d4.rank → ℤ)) = _
  rw [tdNhat_inv_smul_two, rootChar_four, tupS_zero, tupS_one, tupS_two, tupS_three]
  show (s ^ (2 : ℤ)) ^ (1 : ℤ) * ((sigU σ s) ^ (2 : ℤ)) ^ (1 : ℤ) *
    (s⁻¹ * (sigU σ s)⁻¹ * (sigU σ (sigU σ s))⁻¹) ^ (2 : ℤ) *
      ((sigU σ (sigU σ s)) ^ (2 : ℤ)) ^ (1 : ℤ) = 1
  simp only [zpow_one]
  apply Units.ext
  have hs := s.ne_zero
  have h1 : ((sigU σ s : Kˣ) : K) ≠ 0 := (sigU σ s).ne_zero
  have h2 : ((sigU σ (sigU σ s) : Kˣ) : K) ≠ 0 := (sigU σ (sigU σ s)).ne_zero
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_one,
    zpow_ofNat]
  field_simp

end Tuples

section ScalarCases

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem two_ne_zero_of_neg_one_ne_one (hK : (-1 : Kˣ) ≠ 1) : (2 : K) ≠ 0 := by
  intro h
  apply hK
  apply Units.ext
  simp only [Units.val_neg, Units.val_one]
  linear_combination -h

theorem tuple_eq_of_compat {x y : twistedGroup σ} {b c : Fin d4.rank → Kˣ}
    (hx : twistedIncl σ x = rootDiagUnit d4 b) (hy : twistedIncl σ y = rootDiagUnit d4 c)
    (h0 : b (nd 0) = c (nd 0)) (h2 : b (nd 2) = c (nd 2)) : b = c := by
  obtain ⟨b1, b3, -, -⟩ := torus_compat hx
  obtain ⟨c1, c3, -, -⟩ := torus_compat hy
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact Units.ext (by rw [b1, c1, h0])
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact Units.ext (by rw [b3, c3, b1, c1, h0])

include hσ in
theorem involution_centralizing_slLong (hK : (-1 : Kˣ) ≠ 1) [Finite K] {z : twistedGroup σ}
    (hz : z ∈ SProd σ hσ) (hz2 : z * z = 1) (hc : ∀ C : SL(2, fixedField σ),
      z * slLong σ hσ C = slLong σ hσ C * z) : z = 1 ∨ z = slLong σ hσ (-1) := by
  obtain ⟨t, ht, A, B, rfl⟩ := hz
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, hsb, hs⟩ := torus_conj_slLong hσ hb
  have hzA : ∀ C : SL(2, fixedField σ), (t * slLong σ hσ A * slB σ hσ B) * slLong σ hσ C *
      (t * slLong σ hσ A * slB σ hσ B)⁻¹ =
      slLong σ hσ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL A) C) :=
    fun C => pair_prod_conj1 (slLong_comm_slB hσ) hs A B C
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq
    (D := 1) (E := diagGL s * Matrix.SpecialLinearGroup.toGL A) (fun C => by
      apply slLong_injective hσ
      rw [← hzA C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  have hscal : ((diagGL s * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) (fixedField σ)) :
      Matrix (Fin 2) (Fin 2) (fixedField σ)) = c • 1 := by
    rw [hcs]; simp
  obtain ⟨u, hAu, hsu⟩ := diag_mul_scalar s A c hscal
  set uK : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom u with huK
  set t' : twistedGroup σ := t * slLong σ hσ (HSL u) with ht'
  have hι' : twistedIncl σ t' = rootDiagUnit d4 (b * fun j => uK ^ d4.cartan (nd 2) j) := by
    rw [ht', map_mul, hb, twistedIncl_slLong_HSL hσ, rootDiagUnit_mul]
  have hb2 : (b * fun j => uK ^ d4.cartan (nd 2) j) (nd 2) = 1 := by
    apply Units.ext
    show ((b (nd 2) * uK ^ d4.cartan (nd 2) (nd 2) : Kˣ) : K) = 1
    rw [show d4.cartan (nd 2) (nd 2) = 2 by decide]
    have h1 : ((b (nd 2) : Kˣ) : K) = (((u⁻¹ * u⁻¹ : (fixedField σ)ˣ) : fixedField σ) : K) := by
      rw [← hsu]; exact hsb.symm
    have hu0 : ((u : (fixedField σ)ˣ) : fixedField σ) ≠ 0 := u.ne_zero
    have hu0K : (((u : (fixedField σ)ˣ) : fixedField σ) : K) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have huKc : ((uK : Kˣ) : K) = (((u : (fixedField σ)ˣ) : fixedField σ) : K) := rfl
    simp only [Units.val_mul, zpow_ofNat, Units.val_pow_eq_pow_val]
    rw [h1, huKc]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Subfield.coe_mul, Subfield.coe_inv]
    field_simp
  obtain ⟨s₀, hs₀⟩ := nuU_surjective hσ ((b * fun j => uK ^ d4.cartan (nd 2) j) (nd 0))
  have htup := tuple_eq_of_compat hι' (twistedIncl_slB_HSL hσ s₀) (by rw [cB_zero, hs₀])
    (by rw [cB_two, hb2])
  have hty : t' = slB σ hσ (HSL s₀) := twistedIncl_injective σ (by
    rw [hι', twistedIncl_slB_HSL hσ, htup])
  have hz : t * slLong σ hσ A * slB σ hσ B = slB σ hσ (HSL s₀ * B) := by
    rw [hAu, ← ht', hty, map_mul]
  rw [hz] at hz2 ⊢
  have hM : (HSL s₀ * B) * (HSL s₀ * B) = 1 := by
    apply slB_injective hσ
    rw [map_mul, map_one]
    exact hz2
  rcases sl2_sq_eq_one_of_two_ne_zero (two_ne_zero_of_neg_one_ne_one hK) _ hM with h | h
  · left
    rw [h, map_one]
  · right
    rw [h, slB_neg_one hσ]

include hσ in
theorem involution_centralizing_slB (hK : (-1 : Kˣ) ≠ 1) [Finite K] {z : twistedGroup σ}
    (hz : z ∈ SProd σ hσ) (hz2 : z * z = 1) (hc : ∀ C : SL(2, K),
      z * slB σ hσ C = slB σ hσ C * z) : z = 1 ∨ z = slLong σ hσ (-1) := by
  obtain ⟨t, ht, A, B, rfl⟩ := hz
  obtain ⟨b, hb⟩ := ht
  obtain ⟨s, hsb, hs⟩ := torus_conj_slB hσ hb
  have hzB : ∀ C : SL(2, K), (t * slLong σ hσ A * slB σ hσ B) * slB σ hσ C *
      (t * slLong σ hσ A * slB σ hσ B)⁻¹ =
      slB σ hσ (glConjSL (diagGL s * Matrix.SpecialLinearGroup.toGL B) C) :=
    fun C => pair_prod_conj2 (slLong_comm_slB hσ) hs A B C
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq
    (D := 1) (E := diagGL s * Matrix.SpecialLinearGroup.toGL B) (fun C => by
      apply slB_injective hσ
      rw [← hzB C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  have hscal : ((diagGL s * Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = c • 1 := by
    rw [hcs]; simp
  obtain ⟨v, hBv, hsv⟩ := diag_mul_scalar s B c hscal
  subst hBv
  set t'' : twistedGroup σ := t * slB σ hσ (HSL v) with ht''
  have ht''TK : t'' ∈ TK σ := mul_mem ⟨b, hb⟩ ⟨_, twistedIncl_slB_HSL hσ v⟩
  obtain ⟨b'', hb''⟩ := ht''TK
  obtain ⟨s'', hs''b, hs''⟩ := torus_conj_slB hσ hb''
  have hdiag : ((diagGL s * Matrix.SpecialLinearGroup.toGL (HSL v) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = ((v⁻¹ : Kˣ) : K) • 1 := by
    rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_HSL, hsv]
    have hv0 : (v : K) ≠ 0 := v.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hact : ∀ C : SL(2, K), t'' * slB σ hσ C * t''⁻¹ = slB σ hσ C := by
    intro C
    calc t'' * slB σ hσ C * t''⁻¹
        = t * (slB σ hσ (HSL v) * slB σ hσ C * (slB σ hσ (HSL v))⁻¹) * t⁻¹ := by
          rw [ht'']; group
      _ = t * slB σ hσ (HSL v * C * (HSL v)⁻¹) * t⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = slB σ hσ (glConjSL (diagGL s) (HSL v * C * (HSL v)⁻¹)) := hs _
      _ = slB σ hσ C := by
          congr 1
          rw [← glConjSL_toGL, ← glConjSL_mul]
          exact glConjSL_of_scalar hdiag C
  have hs''1 : s'' = 1 := by
    obtain ⟨c', -, hc'⟩ := exists_scalar_of_glConjSL_eq (D := 1) (E := diagGL s'') (fun C => by
      apply slB_injective hσ
      rw [glConjSL_one]
      exact ((hs'' C).symm.trans (hact C)).symm)
    have e00 := congrFun (congrFun hc' 0) 0
    have e11 := congrFun (congrFun hc' 1) 1
    simp [coe_diagGL_two] at e00 e11
    exact Units.ext (by rw [Units.val_one]; exact e00.trans e11.symm)
  obtain ⟨h1, h3, h0, h2⟩ := torus_compat hb''
  have e : ((b'' (nd 1) : Kˣ) : K) * (b'' (nd 2) : K) * (b'' (nd 3) : K) = 1 := by
    have := hs''b
    rw [hs''1] at this
    simpa using (congrArg Units.val this).symm
  have e' : ((b'' (nd 3) : Kˣ) : K) * (b'' (nd 2) : K) * (b'' (nd 0) : K) = 1 := by
    have := congrArg σ e
    rw [map_mul, map_mul, map_one, ← h3, ← h2, ← h0] at this
    exact this
  have hb10 : ((b'' (nd 1) : Kˣ) : K) = (b'' (nd 0) : K) := by
    have h : ((b'' (nd 1) : Kˣ) - (b'' (nd 0) : K)) *
        ((b'' (nd 2) : K) * (b'' (nd 3) : K)) = 0 := by
      linear_combination e - e'
    rcases mul_eq_zero.mp h with h | h
    · linear_combination h
    · exact absurd h (mul_ne_zero (b'' (nd 2)).ne_zero (b'' (nd 3)).ne_zero)
  have hβσ : σ ((b'' (nd 0) : Kˣ) : K) = ((b'' (nd 0) : Kˣ) : K) := h1.symm.trans hb10
  have hb30 : ((b'' (nd 3) : Kˣ) : K) = (b'' (nd 0) : K) := by rw [h3, hb10, hβσ]
  set β : Kˣ := b'' (nd 0) with hβ
  let βF : fixedField σ := ⟨(β : K), hβσ⟩
  have hβF0 : βF ≠ 0 := fun h => β.ne_zero (congrArg Subtype.val h)
  let u : (fixedField σ)ˣ := (Units.mk0 βF hβF0)⁻¹
  set uK : Kˣ := Units.map (fixedField σ).subtype.toMonoidHom u with huK
  have huKc : ((uK : Kˣ) : K) = ((β : Kˣ) : K)⁻¹ := by
    show (((u : (fixedField σ)ˣ) : fixedField σ) : K) = _
    simp [u, βF]
  have h0' : b'' (nd 0) = (fun j => uK ^ d4.cartan (nd 2) j) (nd 0) := by
    apply Units.ext
    show ((β : Kˣ) : K) = ((uK ^ d4.cartan (nd 2) (nd 0) : Kˣ) : K)
    rw [show d4.cartan (nd 2) (nd 0) = -1 by decide, zpow_neg_one, Units.val_inv_eq_inv_val,
      huKc, inv_inv]
  have h2' : b'' (nd 2) = (fun j => uK ^ d4.cartan (nd 2) j) (nd 2) := by
    apply Units.ext
    show ((b'' (nd 2) : Kˣ) : K) = ((uK ^ d4.cartan (nd 2) (nd 2) : Kˣ) : K)
    rw [show d4.cartan (nd 2) (nd 2) = 2 by decide, zpow_ofNat, Units.val_pow_eq_pow_val, huKc]
    have hβ0 : ((β : Kˣ) : K) ≠ 0 := β.ne_zero
    rw [hb10, hb30] at e
    field_simp
    linear_combination e
  have htup := tuple_eq_of_compat hb'' (twistedIncl_slLong_HSL hσ u) h0' h2'
  have hty : t'' = slLong σ hσ (HSL u) :=
    twistedIncl_injective σ (by rw [hb'', twistedIncl_slLong_HSL hσ, htup])
  have hz : t * slLong σ hσ A * slB σ hσ (HSL v) = slLong σ hσ (HSL u * A) := by
    calc t * slLong σ hσ A * slB σ hσ (HSL v)
        = t * slB σ hσ (HSL v) * slLong σ hσ A := by
          rw [mul_assoc, slLong_comm_slB hσ A (HSL v), ← mul_assoc]
      _ = t'' * slLong σ hσ A := rfl
      _ = slLong σ hσ (HSL u * A) := by rw [hty, map_mul]
  rw [hz] at hz2 ⊢
  have hM : (HSL u * A) * (HSL u * A) = 1 := by
    apply slLong_injective hσ
    rw [map_mul, map_one]
    exact hz2
  have h2F : (2 : fixedField σ) ≠ 0 := fun h => two_ne_zero_of_neg_one_ne_one hK (by
    have := congrArg (fixedField σ).subtype h
    rwa [map_ofNat, map_zero] at this)
  rcases sl2_sq_eq_one_of_two_ne_zero h2F _ hM with h | h
  · left
    rw [h, map_one]
  · right
    rw [h]

end ScalarCases

end CFSG.ClassicalInvolution.G2D4Models
