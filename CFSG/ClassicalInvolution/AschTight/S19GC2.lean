module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Class

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.ClassicalInvolution.G2D4Models
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

include hσ in
theorem mem_range_slB_of_centralizing {z : twistedGroup σ} (hz : z ∈ SProd σ hσ)
    (hc : ∀ C : SL(2, fixedField σ), z * slLong σ hσ C = slLong σ hσ C * z) :
    ∃ B' : SL(2, K), z = slB σ hσ B' := by
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
  exact ⟨HSL s₀ * B, by rw [hAu, ← ht', hty, map_mul]⟩

omit [Finite K] in
include hσ in
theorem mem_range_slLong_of_centralizing {z : twistedGroup σ} (hz : z ∈ SProd σ hσ)
    (hc : ∀ C : SL(2, K), z * slB σ hσ C = slB σ hσ C * z) :
    ∃ A' : SL(2, fixedField σ), z = slLong σ hσ A' := by
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
  refine ⟨HSL u * A, ?_⟩
  calc t * slLong σ hσ A * slB σ hσ (HSL v)
      = t * slB σ hσ (HSL v) * slLong σ hσ A := by
        rw [mul_assoc, slLong_comm_slB hσ A (HSL v), ← mul_assoc]
    _ = t'' * slLong σ hσ A := rfl
    _ = slLong σ hσ (HSL u * A) := by rw [hty, map_mul]

include hσ in
theorem centralizer_range_slLong (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ) :
    Subgroup.centralizer ((slLong σ hσ).range : Set (twistedGroup σ)) = (slB σ hσ).range := by
  refine le_antisymm (fun x hx => ?_) ?_
  · have hc : ∀ C, x * slLong σ hσ C = slLong σ hσ C * x := fun C =>
      (Subgroup.mem_centralizer_iff.mp hx _ ⟨C, rfl⟩).symm
    obtain ⟨B', hB'⟩ := mem_range_slB_of_centralizing hσ
      (mem_SProd_of_centralizes hσ hK hC₀ hgF (hc (-1))) hc
    exact ⟨B', hB'.symm⟩
  · rintro _ ⟨B, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨C, rfl⟩
    exact slLong_comm_slB hσ C B

omit [Finite K] in
include hσ in
theorem centralizer_range_slShort (hK : (-1 : Kˣ) ≠ 1)
    (hC₀ : graphFixedRootGroup TwistTag.D4 K σ ≤ (twistedIncl σ).range)
    (hgF : ∀ g : twistedGroup σ, twistedIncl σ g ∈ graphFixedRootGroup TwistTag.D4 K σ) :
    Subgroup.centralizer ((slShort σ hσ).range : Set (twistedGroup σ)) =
      ((MulAut.conj (nB σ)⁻¹).toMonoidHom.comp (slLong σ hσ)).range := by
  have hS : ∀ C', slShort σ hσ C' = (nB σ)⁻¹ * slB σ hσ C' * nB σ := fun C' => by
    rw [slB_apply]
    group
  refine le_antisymm (fun x hx => ?_) ?_
  · have hcB : ∀ C, (nB σ * x * (nB σ)⁻¹) * slB σ hσ C = slB σ hσ C * (nB σ * x * (nB σ)⁻¹) := by
      intro C
      have h := Subgroup.mem_centralizer_iff.mp hx _ ⟨C, rfl⟩
      rw [slB_apply]
      calc nB σ * x * (nB σ)⁻¹ * (nB σ * slShort σ hσ C * (nB σ)⁻¹) =
            nB σ * (x * slShort σ hσ C) * (nB σ)⁻¹ := by group
        _ = nB σ * (slShort σ hσ C * x) * (nB σ)⁻¹ := by rw [← h]
        _ = _ := by group
    have hmem : nB σ * x * (nB σ)⁻¹ ∈ SProd σ hσ :=
      mem_SProd_of_centralizes hσ hK hC₀ hgF (by rw [← slB_neg_one hσ]; exact hcB (-1))
    obtain ⟨A', hA'⟩ := mem_range_slLong_of_centralizing hσ hmem hcB
    refine ⟨A', ?_⟩
    change (nB σ)⁻¹ * slLong σ hσ A' * (nB σ)⁻¹⁻¹ = x
    rw [← hA', inv_inv]
    group
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨C, rfl⟩
    change slShort σ hσ C * ((nB σ)⁻¹ * slLong σ hσ A * (nB σ)⁻¹⁻¹) =
      ((nB σ)⁻¹ * slLong σ hσ A * (nB σ)⁻¹⁻¹) * slShort σ hσ C
    rw [hS, inv_inv]
    calc (nB σ)⁻¹ * slB σ hσ C * nB σ * ((nB σ)⁻¹ * slLong σ hσ A * nB σ) =
          (nB σ)⁻¹ * (slB σ hσ C * slLong σ hσ A) * nB σ := by group
      _ = (nB σ)⁻¹ * (slLong σ hσ A * slB σ hσ C) * nB σ := by rw [slLong_comm_slB hσ]
      _ = _ := by group

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
