module

public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.RankThree.PartOne.KE.SuzukiDescent

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Matrix CFSG.RankThree.Classical2
open scoped MatrixGroups

section Scalar

variable {L : Type} [Field L]

theorem exists_scalar_of_commute_transvection {M : Matrix (Fin 3) (Fin 3) L}
    (h : ∀ (i j : Fin 3) (_ : i ≠ j) (t : L),
      M * (1 + Matrix.single i j t) = (1 + Matrix.single i j t) * M) :
    ∃ a : L, M = Matrix.scalar (Fin 3) a := by
  obtain ⟨a, ha⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct (M := M) fun t =>
    (h t.i t.j t.hij t.c).symm
  exact ⟨a, ha.symm⟩

end Scalar


section GLTools

variable {L : Type} [Field L] {n : ℕ}

@[expose] def invTGL : GL (Fin n) L →* GL (Fin n) L where
  toFun g := ⟨((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ,
    (g : Matrix (Fin n) (Fin n) L)ᵀ,
    by rw [← Matrix.transpose_mul]; simp, by rw [← Matrix.transpose_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.transpose_mul])

@[simp] theorem coe_invTGL (g : GL (Fin n) L) :
    ((invTGL g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ := rfl

@[expose] def frobGL (σ : L →+* L) : GL (Fin n) L →* GL (Fin n) L :=
  Units.map (σ.mapMatrix : Matrix (Fin n) (Fin n) L →+* Matrix (Fin n) (Fin n) L).toMonoidHom

@[simp] theorem coe_frobGL (σ : L →+* L) (g : GL (Fin n) L) :
    ((frobGL σ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      (g : Matrix (Fin n) (Fin n) L).map σ := rfl

@[simp] theorem invTGL_invTGL (g : GL (Fin n) L) : invTGL (invTGL g) = g :=
  Units.ext (by simp [Matrix.transpose_nonsing_inv])

theorem frobGL_invTGL (σ : L →+* L) (g : GL (Fin n) L) :
    frobGL σ (invTGL g) = invTGL (frobGL σ g) := by
  refine Units.ext ?_
  simp [frobGL, Units.coe_map_inv, Matrix.transpose_map]

end GLTools

section Main

variable {ℓ f : ℕ} [Fact ℓ.Prime] {L k : Type} [Field L] [Field k] [Algebra k L] [IsAlgClosure k L]

theorem graph_matrix_form (Ψ : SL(3, L) ≃* SL(3, L)) (c : ∀ i j : Fin 3, i ≠ j → Lˣ)
    (hΨ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * t)) :
    ∃ B : GL (Fin 3) L, ∀ X : SL(3, L),
      Matrix.SpecialLinearGroup.toGL (Ψ X) = B * invTGL (Matrix.SpecialLinearGroup.toGL X) * B⁻¹ := by
  classical
  obtain ⟨B, hB⟩ := exists_conj_map_inv_transpose_of_root_permuting (n := 3) le_rfl
    (RingHom.id L) 1 Ψ.toMonoidHom (fun i j => if h : i = j then 1 else c i j h) (by
      intro i j hij t
      simp [hΨ i j hij t, Matrix.SpecialLinearGroup.transvection_coe, hij])
  refine ⟨B, fun X => ?_⟩
  refine Units.ext ?_
  simpa using hB X

theorem split_matrix_form [CharP L ℓ] (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ)
    (Φ Ψ : SL(3, L) ≃* SL(3, L))
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + Matrix.single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f))
    (c : ∀ i j : Fin 3, i ≠ j → Lˣ)
    (hΨ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * t)) :
    ∃ A : GL (Fin 3) L, ∀ X : SL(3, L),
      Matrix.SpecialLinearGroup.toGL (Φ (Ψ X)) =
        A * frobGL (iterateFrobenius L ℓ f) (Matrix.SpecialLinearGroup.toGL X) * A⁻¹ := by
  classical
  obtain ⟨A, hA⟩ := exists_conj_map_of_root_permuting (n := 3) le_rfl (iterateFrobenius L ℓ f) π
    (Φ.toMonoidHom.comp Ψ.toMonoidHom)
    (fun i j => if h : i = j then 1 else b j i * (c i j h) ^ ℓ ^ f) (by
      intro i j hij t
      have h1 := hΦ j i hij.symm ((c i j hij : L) * t)
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hΨ i j hij t, dite_eq_right hij]
      rw [h1, iterateFrobenius_def]
      congr 2
      simp [mul_pow]
      ring)
  refine ⟨A, fun X => Units.ext ?_⟩
  simpa using hA X

theorem coe_invTGL_frobGL_transvection (σ : L →+* L) {i j : Fin 3} (hij : i ≠ j) (s : L) :
    ((invTGL (frobGL σ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij s))) : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      1 + Matrix.single j i (-σ s) := by
  have hinv : (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij s))⁻¹ =
      Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij (-s)) := by
    rw [← map_inv, Matrix.SpecialLinearGroup.transvection_inv]
  rw [coe_invTGL, ← map_inv, hinv, coe_frobGL]
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.map_add, Matrix.transpose_single]

theorem exists_scalar_of_conj_eq {N₁ N₂ : GL (Fin 3) L}
    (h : ∀ (i j : Fin 3) (hij : i ≠ j) (u : L),
      N₁ * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij u) * N₁⁻¹ =
        N₂ * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij u) *
          N₂⁻¹) :
    ∃ a : L, (N₁ : Matrix (Fin 3) (Fin 3) L) = a • (N₂ : Matrix (Fin 3) (Fin 3) L) := by
  obtain ⟨a, ha⟩ := exists_scalar_of_commute_transvection (L := L)
    (M := ((N₂⁻¹ * N₁ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) (by
      intro i j hij t
      have := congrArg (fun w => N₂⁻¹ * w * N₁) (h i j hij t)
      simp only [mul_assoc, inv_mul_cancel_left] at this
      have h2 := congrArg (fun w : GL (Fin 3) L => (w : Matrix (Fin 3) (Fin 3) L)) this
      simpa [Matrix.SpecialLinearGroup.transvection_coe, mul_assoc] using h2)
  refine ⟨a, ?_⟩
  have h3 : (N₁ : Matrix (Fin 3) (Fin 3) L) = (N₂ : Matrix (Fin 3) (Fin 3) L) *
      ((N₂⁻¹ * N₁ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by simp
  rw [h3, ha, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

theorem rel_of_commute (σ : L →+* L) (hσ : Function.Surjective σ) (A B : GL (Fin 3) L)
    (h : ∀ X : SL(3, L),
      A * frobGL σ (B * invTGL (Matrix.SpecialLinearGroup.toGL X) * B⁻¹) * A⁻¹ =
        B * invTGL (A * frobGL σ (Matrix.SpecialLinearGroup.toGL X) * A⁻¹) * B⁻¹) :
    ∃ a : L, a ≠ 0 ∧ ((A * frobGL σ B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      a • ((B * invTGL A : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
  have key1 : ∀ x : GL (Fin 3) L, A * frobGL σ (B * invTGL x * B⁻¹) * A⁻¹ =
      (A * frobGL σ B) * invTGL (frobGL σ x) * (A * frobGL σ B)⁻¹ := by
    intro x
    simp only [map_mul, map_inv, frobGL_invTGL]
    group
  have key2 : ∀ x : GL (Fin 3) L, B * invTGL (A * frobGL σ x * A⁻¹) * B⁻¹ =
      (B * invTGL A) * invTGL (frobGL σ x) * (B * invTGL A)⁻¹ := by
    intro x
    simp only [map_mul, map_inv]
    group
  obtain ⟨a, ha⟩ := exists_scalar_of_conj_eq (N₁ := A * frobGL σ B) (N₂ := B * invTGL A) (by
    intro i j hij u
    obtain ⟨s, hs⟩ := hσ (-u)
    have hz : invTGL (frobGL σ (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection hij.symm s))) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij u) := by
      refine Units.ext ?_
      rw [coe_invTGL_frobGL_transvection σ hij.symm s, hs]
      simp [Matrix.SpecialLinearGroup.transvection_coe]
    have := h (Matrix.SpecialLinearGroup.transvection hij.symm s)
    rw [key1, key2, hz] at this
    exact this)
  refine ⟨a, ?_, ha⟩
  rintro rfl
  have h0 : ((A * frobGL σ B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = 0 := by
    rw [ha, zero_smul]
  have h1 := (A * frobGL σ B).mul_inv
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem symm_of_involution (h2 : (2 : L) ≠ 0) (B : GL (Fin 3) L)
    (h : ∀ X : SL(3, L), B * invTGL (B * invTGL (Matrix.SpecialLinearGroup.toGL X) * B⁻¹) * B⁻¹ =
      Matrix.SpecialLinearGroup.toGL X) :
    (B : Matrix (Fin 3) (Fin 3) L)ᵀ = B := by
  have hQ : ∀ x : GL (Fin 3) L, (∃ X : SL(3, L), Matrix.SpecialLinearGroup.toGL X = x) →
      (B * invTGL B) * x * (B * invTGL B)⁻¹ = x := by
    rintro x ⟨X, rfl⟩
    have := h X
    simp only [map_mul, map_inv, invTGL_invTGL] at this
    simpa [mul_assoc] using this
  obtain ⟨s, hs⟩ := exists_scalar_of_commute_transvection
    (M := ((B * invTGL B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) (by
      intro i j hij t
      have := hQ (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t))
        ⟨_, rfl⟩
      have h3 : (B * invTGL B) * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.transvection hij t) =
          Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) *
            (B * invTGL B) := by
        rw [mul_inv_eq_iff_eq_mul] at this
        exact this
      have h4 := congrArg (fun w : GL (Fin 3) L => (w : Matrix (Fin 3) (Fin 3) L)) h3
      simpa [Matrix.SpecialLinearGroup.transvection_coe] using h4)
  have hB1 : (B : Matrix (Fin 3) (Fin 3) L) =
      s • (B : Matrix (Fin 3) (Fin 3) L)ᵀ := by
    have h5 : (B : Matrix (Fin 3) (Fin 3) L) * ((B⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ =
        Matrix.scalar (Fin 3) s := by simpa using hs
    have h6 : ((B⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ *
        (B : Matrix (Fin 3) (Fin 3) L)ᵀ = 1 := by
      rw [← Matrix.transpose_mul]; simp
    calc (B : Matrix (Fin 3) (Fin 3) L) =
        (B : Matrix (Fin 3) (Fin 3) L) * (((B⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ *
          (B : Matrix (Fin 3) (Fin 3) L)ᵀ) := by rw [h6, Matrix.mul_one]
      _ = s • (B : Matrix (Fin 3) (Fin 3) L)ᵀ := by
        rw [← Matrix.mul_assoc, h5, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
          Matrix.smul_mul, Matrix.one_mul]
  have hB2 : (B : Matrix (Fin 3) (Fin 3) L)ᵀ = s • (B : Matrix (Fin 3) (Fin 3) L) := by
    conv_lhs => rw [hB1]
    rw [Matrix.transpose_smul, Matrix.transpose_transpose]
  have hB0 : (B : Matrix (Fin 3) (Fin 3) L) ≠ 0 := by
    intro h0
    have := (B : GL (Fin 3) L).mul_inv
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hss : s * s = 1 := by
    have : (B : Matrix (Fin 3) (Fin 3) L) = (s * s) • (B : Matrix (Fin 3) (Fin 3) L) := by
      conv_lhs => rw [hB1, hB2]
      rw [smul_smul]
    by_contra hne
    apply hB0
    have h7 : ((1 : L) - s * s) • (B : Matrix (Fin 3) (Fin 3) L) = 0 := by
      rw [sub_smul, one_smul, ← this, sub_self]
    rcases smul_eq_zero.1 h7 with h8 | h8
    · exact absurd (sub_eq_zero.1 h8).symm hne
    · exact h8
  rcases mul_self_eq_one_iff.1 hss with hs1 | hs1
  · rw [hB2, hs1, one_smul]
  · exfalso
    rw [hs1, neg_one_smul] at hB2
    have hdet : (B : Matrix (Fin 3) (Fin 3) L).det = -(B : Matrix (Fin 3) (Fin 3) L).det := by
      conv_lhs => rw [← Matrix.det_transpose, hB2]
      rw [Matrix.det_neg]
      norm_num
    have h9 : (2 : L) * (B : Matrix (Fin 3) (Fin 3) L).det = 0 := by linear_combination hdet
    rcases mul_eq_zero.1 h9 with h10 | h10
    · exact h2 h10
    · exact ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit B)).ne_zero h10


theorem group_fix_aux {G : Type*} [Group G] (B ig iy g B₁ y : G) (hBg : B * ig = g * B₁)
    (hc : B₁ * iy = y * B₁) : B * (ig * iy * ig⁻¹) * B⁻¹ = g * y * g⁻¹ := by
  calc B * (ig * iy * ig⁻¹) * B⁻¹ = (B * ig) * iy * (B * ig)⁻¹ := by group
    _ = (g * B₁) * iy * (g * B₁)⁻¹ := by rw [hBg]
    _ = g * (B₁ * iy) * B₁⁻¹ * g⁻¹ := by group
    _ = g * (y * B₁) * B₁⁻¹ * g⁻¹ := by rw [hc]
    _ = g * y * g⁻¹ := by group

theorem group_fix_aux' {G : Type*} [Group G] (A sg g y : G) (hAg : A * sg = g) :
    A * (sg * y * sg⁻¹) * A⁻¹ = g * y * g⁻¹ := by
  calc A * (sg * y * sg⁻¹) * A⁻¹ = (A * sg) * y * (A * sg)⁻¹ := by group
    _ = g * y * g⁻¹ := by rw [hAg]

theorem exists_orthogonal_frame [CharP L ℓ] (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hk : Nat.card k = ℓ ^ f)
    (π : Equiv.Perm (Fin 3)) (b : Fin 3 → Fin 3 → Lˣ) (Φ Ψ : SL(3, L) ≃* SL(3, L))
    (hΦ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Φ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        1 + Matrix.single (π j) (π i) ((b i j : L) * t ^ ℓ ^ f))
    (c : ∀ i j : Fin 3, i ≠ j → Lˣ)
    (hΨ : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection hij.symm ((c i j hij : L) * t))
    (hcomm : ∀ X, Φ (Ψ X) = Ψ (Φ X)) (hΨ2 : ∀ X, Ψ (Ψ X) = X) :
    ∃ (g : GL (Fin 3) L) (Bk : Matrix (Fin 3) (Fin 3) k), Bkᵀ = Bk ∧ Bk.det ≠ 0 ∧
      ∀ Y : SL(3, k), (Y : Matrix (Fin 3) (Fin 3) k) * Bk * (Y : Matrix (Fin 3) (Fin 3) k)ᵀ = Bk →
        Φ (conjSLn g (Matrix.SpecialLinearGroup.map (algebraMap k L) Y)) =
            conjSLn g (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∧
          Ψ (conjSLn g (Matrix.SpecialLinearGroup.map (algebraMap k L) Y)) =
            conjSLn g (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have hq2 : 2 ≤ ℓ ^ f :=
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have h2 : (2 : L) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : L) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff L ℓ 2).1 h'
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h1 | h1
    · exact hℓ.one_lt.ne' h1
    · exact hℓ2 h1
  set σ : L →+* L := iterateFrobenius L ℓ f with hσdef
  have hσq : ∀ x, σ x = x ^ ℓ ^ f := iterateFrobenius_def ℓ f
  have hσsurj : Function.Surjective σ := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hℓ.pos f)
    exact ⟨x, by rw [hσq]; exact hx⟩
  obtain ⟨B, hB⟩ := graph_matrix_form Ψ c hΨ
  obtain ⟨A, hA⟩ := split_matrix_form π b Φ Ψ hΦ c hΨ
  have hF4 : ∀ X : SL(3, L),
      A * frobGL σ (B * invTGL (Matrix.SpecialLinearGroup.toGL X) * B⁻¹) * A⁻¹ =
        B * invTGL (A * frobGL σ (Matrix.SpecialLinearGroup.toGL X) * A⁻¹) * B⁻¹ := by
    intro X
    rw [← hB X, ← hA (Ψ X), ← hA X, ← hB (Φ (Ψ X)), hcomm (Ψ X)]
  obtain ⟨a, ha0, ha⟩ := rel_of_commute σ hσsurj A B hF4
  have hBsymm : (B : Matrix (Fin 3) (Fin 3) L)ᵀ = B := by
    refine symm_of_involution h2 B fun X => ?_
    have := hB (Ψ X)
    rw [hΨ2 X, hB X] at this
    exact this.symm
  obtain ⟨H, hH⟩ := (matrix_frobenius_lang (K := k) (Ω := L) hℓ hf hk (n := 3) (by norm_num) A).1
  have hAH : A = H⁻¹ * frobGL σ H := by
    refine Units.ext ?_
    rw [hH]
    simp only [Units.val_mul, coe_frobGL]
    congr 2
  set g : GL (Fin 3) L := H⁻¹ with hg
  have hAg : A * frobGL σ g = g := by
    rw [hAH, hg, map_inv]
    group
  have hσg : frobGL σ g = A⁻¹ * g := eq_inv_mul_of_mul_eq hAg
  set B₁ : GL (Fin 3) L := g⁻¹ * B * invTGL g with hB₁
  have hB₁symm : (B₁ : Matrix (Fin 3) (Fin 3) L)ᵀ = B₁ := by
    simp [hB₁, Matrix.transpose_mul, hBsymm, Matrix.mul_assoc]
  have hσB₁ : ((frobGL σ B₁ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      a • (B₁ : Matrix (Fin 3) (Fin 3) L) := by
    have e : frobGL σ B₁ = g⁻¹ * (A * frobGL σ B) * (invTGL A)⁻¹ * invTGL g := by
      simp only [hB₁, map_mul, map_inv, frobGL_invTGL, hσg]
      group
    rw [e]
    simp only [Units.val_mul, ha, hB₁, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have := (invTGL A).mul_inv
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc, this, Matrix.one_mul]
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq a⁻¹ (show 0 < ℓ ^ f - 1 by omega)
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hlam
    exact ha0 (inv_eq_zero.1 hlam.symm)
  have hlamq : lam ^ ℓ ^ f * a = lam := by
    have h1 : lam ^ ℓ ^ f = lam ^ (ℓ ^ f - 1) * lam := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, hlam, mul_assoc, mul_comm lam a, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
  set M : Matrix (Fin 3) (Fin 3) L := lam • (B₁ : Matrix (Fin 3) (Fin 3) L) with hM
  have hMq : ∀ i j, (M i j) ^ ℓ ^ f = M i j := by
    intro i j
    have h1 := congrFun (congrFun hσB₁ i) j
    simp only [coe_frobGL, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hσq] at h1
    simp only [hM, Matrix.smul_apply, smul_eq_mul, mul_pow, h1]
    calc lam ^ ℓ ^ f * (a * B₁ i j) = (lam ^ ℓ ^ f * a) * B₁ i j := by ring
      _ = lam * B₁ i j := by rw [hlamq]
  have hMk : ∀ i j, ∃ r : k, algebraMap k L r = M i j := fun i j =>
    CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq (k := k) (L := L) (c := M i j)
      (by rw [hk]; exact hMq i j)
  choose Bk' hBk using hMk
  let Bk : Matrix (Fin 3) (Fin 3) k := Matrix.of Bk'
  have hBkmap : Bk.map (algebraMap k L) = M := by ext i j; exact hBk i j
  have hinj := (algebraMap k L).injective
  have hMsymm : Mᵀ = M := by rw [hM, Matrix.transpose_smul, hB₁symm]
  refine ⟨g, Bk, ?_, ?_, ?_⟩
  · apply Matrix.map_injective hinj
    show Bkᵀ.map (algebraMap k L) = Bk.map (algebraMap k L)
    rw [Matrix.transpose_map, hBkmap, hMsymm]
  · intro hdet0
    have h1 : (algebraMap k L) Bk.det = M.det := by
      rw [RingHom.map_det]
      exact congrArg Matrix.det hBkmap
    rw [hdet0, map_zero, hM, Matrix.det_smul] at h1
    have h2 : (B₁ : Matrix (Fin 3) (Fin 3) L).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit B₁)).ne_zero
    exact (mul_ne_zero (pow_ne_zero _ hlam0) h2) h1.symm
  · intro Y hY
    set Yk : SL(3, L) := Matrix.SpecialLinearGroup.map (algebraMap k L) Y with hYk
    set y : GL (Fin 3) L := Matrix.SpecialLinearGroup.toGL Yk with hy
    have hyc : (y : Matrix (Fin 3) (Fin 3) L) = (Y : Matrix (Fin 3) (Fin 3) k).map (algebraMap k L) :=
      rfl
    have hσy : frobGL σ y = y := by
      refine Units.ext ?_
      rw [coe_frobGL, hyc]
      ext i j
      simp only [Matrix.map_apply, hσq]
      rw [← map_pow]
      congr 1
      have := FiniteField.pow_card ((Y : Matrix (Fin 3) (Fin 3) k) i j)
      rwa [← Nat.card_eq_fintype_card, hk] at this
    have hyB : (y : Matrix (Fin 3) (Fin 3) L) * (B₁ : Matrix (Fin 3) (Fin 3) L) *
        (y : Matrix (Fin 3) (Fin 3) L)ᵀ = B₁ := by
      have h1 := congrArg (fun N : Matrix (Fin 3) (Fin 3) k => N.map (algebraMap k L)) hY
      simp only [Matrix.map_mul, Matrix.transpose_map, hBkmap] at h1
      rw [← hyc] at h1
      have h2 : lam • ((y : Matrix (Fin 3) (Fin 3) L) * (B₁ : Matrix (Fin 3) (Fin 3) L) *
          (y : Matrix (Fin 3) (Fin 3) L)ᵀ) = lam • (B₁ : Matrix (Fin 3) (Fin 3) L) := by
        simpa [hM, Matrix.mul_smul, Matrix.smul_mul] using h1
      exact smul_right_injective _ hlam0 h2
    have hcomm1 : B₁ * invTGL y = y * B₁ := by
      refine Units.ext ?_
      have h3 : ((y⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ * (y : Matrix (Fin 3) (Fin 3) L)ᵀ
          = 1 := by
        rw [← Matrix.transpose_mul]; simp
      have h4 : (y : Matrix (Fin 3) (Fin 3) L)ᵀ * ((y⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ
          = 1 := by
        rw [← Matrix.transpose_mul]; simp
      calc ((B₁ * invTGL y : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
          = (y : Matrix (Fin 3) (Fin 3) L) * B₁ * (y : Matrix (Fin 3) (Fin 3) L)ᵀ *
              ((y⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)ᵀ := by
            rw [hyB]; rfl
        _ = (y : Matrix (Fin 3) (Fin 3) L) * B₁ := by
            rw [Matrix.mul_assoc _ (y : Matrix (Fin 3) (Fin 3) L)ᵀ, h4, Matrix.mul_one]
        _ = ((y * B₁ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := rfl
    have hBg : B * invTGL g = g * B₁ := by
      rw [hB₁]; group
    set X : SL(3, L) := conjSLn g Yk with hXdef
    have hX : Matrix.SpecialLinearGroup.toGL X = g * y * g⁻¹ := by
      exact Units.ext rfl
    have hΨX : Ψ X = X := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [hB X, hX]
      simp only [map_mul, map_inv]
      exact group_fix_aux B (invTGL g) (invTGL y) g B₁ y hBg hcomm1
    refine ⟨?_, hΨX⟩
    have : Φ X = Φ (Ψ X) := by rw [hΨX]
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [this, hA X, hX]
    have hσy' : frobGL (iterateFrobenius L ℓ f) y = y := hσy
    simp only [map_mul, map_inv, hσy']
    exact group_fix_aux' A (frobGL σ g) g y hAg

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
