module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Basic

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K] {m n : ℕ}

section Incl

variable (σ : Fin m → Fin n)

@[expose] def inclMat : Matrix (Fin n) (Fin m) K :=
  Matrix.of fun a b => if a = σ b then (1 : K) else 0

@[expose] def spIncl : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) K :=
  fromBlocks (inclMat σ) 0 0 (inclMat σ)

variable {σ}

theorem spIncl_apply (a : Fin n ⊕ Fin n) (b : Fin m ⊕ Fin m) :
    spIncl (K := K) σ a b = if a = Sum.map σ σ b then 1 else 0 := by
  rcases a with i | i <;> rcases b with j | j <;> simp [spIncl, inclMat]

theorem inclMat_transpose_mul (hσ : Function.Injective σ) :
    (inclMat (K := K) σ)ᵀ * inclMat (K := K) σ = 1 := by
  ext b b'
  simp only [inclMat, mul_apply, transpose_apply, of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (σ b'), ite_eq_left (Finset.mem_univ _), one_apply]
  by_cases h : b = b'
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (hσ h'.symm)), ite_eq_right h]

theorem spIncl_transpose_mul (hσ : Function.Injective σ) :
    (spIncl (K := K) σ)ᵀ * spIncl (K := K) σ = 1 := by
  rw [spIncl, fromBlocks_transpose, fromBlocks_multiply, inclMat_transpose_mul hσ]
  simp [fromBlocks_one]

theorem gram_mul_spIncl :
    gram K n * spIncl (K := K) σ = spIncl (K := K) σ * gram K m := by
  rw [gram, gram, spIncl, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem spIncl_transpose_mul_gram :
    (spIncl (K := K) σ)ᵀ * gram K n = gram K m * (spIncl (K := K) σ)ᵀ := by
  rw [gram, gram, spIncl, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem spIncl_mul_single_mul_transpose (x y : Fin m ⊕ Fin m) (c : K) :
    spIncl (K := K) σ * Matrix.single x y c * (spIncl (K := K) σ)ᵀ =
      Matrix.single (Sum.map σ σ x) (Sum.map σ σ y) c := by
  ext a b
  simp only [spIncl_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single x]
    · by_cases ha : a = Sum.map σ σ x <;> by_cases hb : b = Sum.map σ σ y <;>
        simp [ha, hb, eq_comm]
    · intro u _ hu
      simp [Ne.symm hu]
    · intro h
      exact absurd (Finset.mem_univ x) h
  · intro v _ hv
    simp [Ne.symm hv]
  · intro h
    exact absurd (Finset.mem_univ y) h

end Incl

section Embed

variable (σ : Fin m → Fin n)

@[expose] def spEmbedMat (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  1 + spIncl (K := K) σ * (g - 1) * (spIncl (K := K) σ)ᵀ

variable {σ}

theorem spEmbedMat_one : spEmbedMat σ (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
  simp [spEmbedMat]

theorem spEmbedMat_mul (hσ : Function.Injective σ)
    (g h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    spEmbedMat σ (g * h) = spEmbedMat σ g * spEmbedMat σ h := by
  simp only [spEmbedMat]
  set P := spIncl (K := K) σ
  have hPP : Pᵀ * P = 1 := spIncl_transpose_mul hσ
  have e1 : g * h - 1 = (g - 1) + (h - 1) + (g - 1) * (h - 1) := by noncomm_ring
  have e2 : P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * ((g - 1) * (h - 1)) * Pᵀ := by
    calc P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) = P * (g - 1) * (Pᵀ * P) * (h - 1) * Pᵀ := by
          simp only [Matrix.mul_assoc]
      _ = P * ((g - 1) * (h - 1)) * Pᵀ := by
          rw [hPP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
  have e3 : P * (g * h - 1) * Pᵀ = P * (g - 1) * Pᵀ + P * (h - 1) * Pᵀ +
      P * (g - 1) * Pᵀ * (P * (h - 1) * Pᵀ) := by
    rw [e2, e1, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  rw [e3]
  noncomm_ring

theorem spEmbedMat_symplectic (hσ : Function.Injective σ)
    {g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K} (hg : gᵀ * gram K m * g = gram K m) :
    (spEmbedMat σ g)ᵀ * gram K n * spEmbedMat σ g = gram K n := by
  set P := spIncl (K := K) σ
  set J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := gram K n
  set J' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := gram K m
  have hPP : Pᵀ * P = 1 := spIncl_transpose_mul hσ
  have hJP : J * P = P * J' := gram_mul_spIncl
  have hPJ : Pᵀ * J = J' * Pᵀ := spIncl_transpose_mul_gram
  have hkey : (gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1) = 0 := by
    have : (gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1) = gᵀ * J' * g - J' := by
      noncomm_ring
    rw [this, hg, sub_self]
  have htr : (spEmbedMat σ g)ᵀ = 1 + P * (gᵀ - 1) * Pᵀ := by
    rw [spEmbedMat, transpose_add, transpose_one, transpose_mul, transpose_mul,
      transpose_transpose, transpose_sub, transpose_one, Matrix.mul_assoc]
  rw [htr, spEmbedMat]
  calc (1 + P * (gᵀ - 1) * Pᵀ) * J * (1 + P * (g - 1) * Pᵀ) =
      J + P * (gᵀ - 1) * (Pᵀ * J) + (J * P) * (g - 1) * Pᵀ +
        P * (gᵀ - 1) * (Pᵀ * J) * P * (g - 1) * Pᵀ := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = J + P * ((gᵀ - 1) * J' + J' * (g - 1) + (gᵀ - 1) * J' * (g - 1)) * Pᵀ := by
        rw [hPJ, hJP]
        have e : P * (gᵀ - 1) * (J' * Pᵀ) * P * (g - 1) * Pᵀ =
            P * ((gᵀ - 1) * J' * (g - 1)) * Pᵀ := by
          calc P * (gᵀ - 1) * (J' * Pᵀ) * P * (g - 1) * Pᵀ =
              P * (gᵀ - 1) * J' * (Pᵀ * P) * (g - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        rw [e]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        abel
    _ = J := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem spEmbedMat_injective (hσ : Function.Injective σ) :
    Function.Injective (spEmbedMat (K := K) σ) := by
  intro g h hgh
  set P := spIncl (K := K) σ
  have hPP : Pᵀ * P = 1 := spIncl_transpose_mul hσ
  have key : ∀ g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K, Pᵀ * spEmbedMat σ g * P = g := by
    intro g
    rw [spEmbedMat, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP]
    calc 1 + Pᵀ * (P * (g - 1) * Pᵀ) * P = 1 + (Pᵀ * P) * (g - 1) * (Pᵀ * P) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hPP, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]
  rw [← key g, ← key h, hgh]

variable (σ)

@[expose] def spEmbedGL (hσ : Function.Injective σ) :
    GL (Fin m ⊕ Fin m) K →* GL (Fin n ⊕ Fin n) K where
  toFun g :=
    { val := spEmbedMat σ (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      inv := spEmbedMat σ ((g⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      val_inv := by rw [← spEmbedMat_mul hσ, Units.mul_inv, spEmbedMat_one]
      inv_val := by rw [← spEmbedMat_mul hσ, Units.inv_mul, spEmbedMat_one] }
  map_one' := Units.ext spEmbedMat_one
  map_mul' g h := Units.ext (spEmbedMat_mul hσ (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) h)

@[expose] def spEmbed (hσ : Function.Injective σ) : StatedSp m K →* StatedSp n K :=
  ((spEmbedGL σ hσ).comp (StatedSp m K).subtype).codRestrict (StatedSp n K) fun g =>
    mem_statedSp_iff.2 (by
      rw [MonoidHom.comp_apply]
      exact spEmbedMat_symplectic hσ (mem_statedSp_iff.1 g.2))

variable {σ}

theorem mat_spEmbed (hσ : Function.Injective σ) (g : StatedSp m K) :
    mat n K (spEmbed σ hσ g) = spEmbedMat σ (mat m K g) := rfl

theorem spEmbed_injective (hσ : Function.Injective σ) :
    Function.Injective (spEmbed (K := K) σ hσ) := fun _ _ h =>
  Subtype.ext (Units.ext (spEmbedMat_injective hσ (congrArg (mat n K) h)))

end Embed

section Entries

variable {σ : Fin m → Fin n}

theorem spIncl_mul_apply_image (hσ : Function.Injective σ)
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (x b : Fin m ⊕ Fin m) :
    (spIncl (K := K) σ * M) (Sum.map σ σ x) b = M x b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single x]
  · simp [spIncl_apply]
  · intro u _ hu
    rw [spIncl_apply, ite_eq_right_iff.mpr (fun h => absurd
      (Sum.map_injective.2 ⟨hσ, hσ⟩ h).symm hu), zero_mul]
  · simp

theorem mul_spIncl_transpose_apply_image (hσ : Function.Injective σ)
    (M : Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) K) (a : Fin n ⊕ Fin n) (y : Fin m ⊕ Fin m) :
    (M * (spIncl (K := K) σ)ᵀ) a (Sum.map σ σ y) = M a y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single y]
  · simp [spIncl_apply]
  · intro v _ hv
    rw [transpose_apply, spIncl_apply, ite_eq_right_iff.mpr (fun h => absurd
      (Sum.map_injective.2 ⟨hσ, hσ⟩ h).symm hv), mul_zero]
  · simp

theorem spEmbedMat_apply_image (hσ : Function.Injective σ)
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (x y : Fin m ⊕ Fin m) :
    spEmbedMat σ g (Sum.map σ σ x) (Sum.map σ σ y) = g x y := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  rw [spEmbedMat, Matrix.add_apply, mul_spIncl_transpose_apply_image hσ,
    spIncl_mul_apply_image hσ, Matrix.sub_apply]
  have : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (Sum.map σ σ x) (Sum.map σ σ y) =
      (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y := by
    simp [Matrix.one_apply, hinj.eq_iff]
  rw [this]
  ring

theorem spEmbedMat_apply_of_not_mem
    (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) {a b : Fin n ⊕ Fin n}
    (h : ¬(a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ))) :
    spEmbedMat σ g a b = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) a b := by
  rw [spEmbedMat, Matrix.add_apply]
  suffices h0 : ((spIncl (K := K) σ * (g - 1) * (spIncl (K := K) σ)ᵀ :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) a b = 0 by
    rw [h0, add_zero]
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun v _ => ?_
  rcases not_and_or.1 h with ha | hb
  · have : ((spIncl (K := K) σ * (g - 1) :
        Matrix (Fin n ⊕ Fin n) (Fin m ⊕ Fin m) K)) a v = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [spIncl_apply, ite_eq_right_iff.mpr (fun h' => absurd ⟨u, h'.symm⟩ ha), zero_mul]
    rw [this, zero_mul]
  · rw [transpose_apply, spIncl_apply, ite_eq_right_iff.mpr (fun h' => absurd ⟨v, h'.symm⟩ hb),
      mul_zero]

theorem isSupp_spEmbed (hσ : Function.Injective σ) (g : StatedSp m K) :
    IsSupp (Set.range (Sum.map σ σ)) (mat n K (spEmbed σ hσ g)) :=
  fun _ _ h => spEmbedMat_apply_of_not_mem _ h

theorem spEmbed_longBlock (hσ : Function.Injective σ) (l : Fin m) (A : SL(2, K)) :
    spEmbed σ hσ (longBlock K m l A) = longBlock K n (σ l) A := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  refine mat_injective ?_
  rw [mat_longBlock, mat_spEmbed, mat_longBlock]
  set M := spEmbedMat σ (blockMat (Sum.inl l) (Sum.inr l) (A : Matrix (Fin 2) (Fin 2) K))
    with hMdef
  have hM : IsSupp (coords (σ l)) M := by
    intro r t hrt
    by_cases hrr : r ∈ Set.range (Sum.map σ σ) ∧ t ∈ Set.range (Sum.map σ σ)
    · obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := hrr
      have hxy : ¬(x ∈ coords l ∧ y ∈ coords l) := by
        rintro ⟨hx, hy⟩
        apply hrt
        have h1 : ∀ z : Fin m ⊕ Fin m, z ∈ coords l → Sum.map σ σ z ∈ coords (σ l) := by
          intro z hz
          rcases mem_coords.1 hz with rfl | rfl
          · exact inl_mem_coords (σ l)
          · exact inr_mem_coords (σ l)
        exact ⟨h1 x hx, h1 y hy⟩
      rw [hMdef, spEmbedMat_apply_image hσ, blockMat_apply_of_not_mem l _ hxy]
      simp [Matrix.one_apply, hinj.eq_iff]
    · rw [hMdef]
      exact spEmbedMat_apply_of_not_mem _ hrr
  have hstd : stdBlock (σ l) M = (A : Matrix (Fin 2) (Fin 2) K) := by
    rw [← stdBlock_blockMat l (A : Matrix (Fin 2) (Fin 2) K)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [stdBlock, hMdef, ← spEmbedMat_apply_image hσ, Sum.map]
  rw [eq_blockMat_stdBlock hM, hstd]

end Entries

section Range

variable {σ : Fin m → Fin n}

open Classical in
theorem spIncl_mul_transpose_apply (hσ : Function.Injective σ) (a b : Fin n ⊕ Fin n) :
    (spIncl (K := K) σ * (spIncl (K := K) σ)ᵀ) a b =
      if a = b ∧ a ∈ Set.range (Sum.map σ σ) then 1 else 0 := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  simp only [Matrix.mul_apply, transpose_apply, spIncl_apply]
  by_cases ha : a ∈ Set.range (Sum.map σ σ)
  · obtain ⟨u₀, rfl⟩ := ha
    rw [Finset.sum_eq_single u₀]
    · by_cases hb : b = Sum.map σ σ u₀
      · subst hb
        simp
      · simp [hb, eq_comm]
    · intro u _ hu
      rw [ite_eq_right_iff.mpr (fun h => absurd (hinj h).symm hu), zero_mul]
    · simp
  · rw [ite_eq_right (fun h => ha h.2)]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [ite_eq_right_iff.mpr (fun h => absurd ⟨u, h.symm⟩ ha), zero_mul]

theorem range_spEmbed (hσ : Function.Injective σ) :
    (spEmbed (K := K) σ hσ).range = suppGroup (Set.range (Sum.map σ σ)) := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact isSupp_spEmbed hσ y
  · intro hx
    set T : Set (Fin n ⊕ Fin n) := Set.range (Sum.map σ σ) with hT
    set P := spIncl (K := K) σ with hP
    set X := mat n K x with hX
    have hx' : IsSupp T X := hx
    set Pr : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := P * Pᵀ with hPr
    have hPrd : Pr = Matrix.diagonal (fun a => if a ∈ T then (1 : K) else 0) := by
      ext a b
      rw [hPr, spIncl_mul_transpose_apply hσ, Matrix.diagonal_apply]
      by_cases hab : a = b
      · subst hab
        simp [hT]
      · simp [hab]
    have hPP : Pᵀ * P = 1 := spIncl_transpose_mul hσ
    have hPrP : Pr * P = P := by rw [hPr, Matrix.mul_assoc, hPP, Matrix.mul_one]
    have hcomm : Pr * X = X * Pr := by
      rw [hPrd]
      ext a b
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
      by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
      · simp [ha, hb]
      · have : X a b = 0 := by
          rw [hx' a b (fun h => hb h.2)]
          exact Matrix.one_apply_ne (fun h => hb (h ▸ ha))
        simp [ha, hb, this]
      · have : X a b = 0 := by
          rw [hx' a b (fun h => ha h.1)]
          exact Matrix.one_apply_ne (fun h => ha (h ▸ hb))
        simp [ha, hb, this]
      · simp [ha, hb]
    have hXeq : X = 1 + Pr * X * Pr - Pr := by
      rw [hPrd]
      ext a b
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.diagonal_apply, Matrix.one_apply]
      by_cases ha : a ∈ T <;> by_cases hb : b ∈ T <;> by_cases hab : a = b
      · subst hab
        simp [ha]
      · simp [ha, hb, hab]
      · subst hab
        exact absurd ha hb
      · have : X a b = 0 := by
          rw [hx' a b (fun h => hb h.2)]
          exact Matrix.one_apply_ne hab
        simp [ha, hb, hab, this]
      · subst hab
        exact absurd hb ha
      · have : X a b = 0 := by
          rw [hx' a b (fun h => ha h.1)]
          exact Matrix.one_apply_ne hab
        simp [ha, hb, hab, this]
      · subst hab
        have : X a a = 1 := by
          rw [hx' a a (fun h => ha h.1)]
          simp
        simp [ha, this]
      · have : X a b = 0 := by
          rw [hx' a b (fun h => ha h.1)]
          exact Matrix.one_apply_ne hab
        simp [ha, hb, hab, this]
    set Y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Pᵀ * X * P with hY
    have hXsymp : Xᵀ * gram K n * X = gram K n := mat_transpose_mul_gram_mul x
    have hJP : gram K n * P = P * gram K m := gram_mul_spIncl
    have hPJ : Pᵀ * gram K n = gram K m * Pᵀ := spIncl_transpose_mul_gram
    have hYsymp : Yᵀ * gram K m * Y = gram K m := by
      have h1 : P * gram K m * Pᵀ = gram K n * Pr := by
        rw [← hJP, hPr, Matrix.mul_assoc]
      calc Yᵀ * gram K m * Y = Pᵀ * Xᵀ * (P * gram K m * Pᵀ) * X * P := by
            rw [hY, transpose_mul, transpose_mul, transpose_transpose]
            simp only [Matrix.mul_assoc]
        _ = Pᵀ * Xᵀ * (gram K n * Pr) * X * P := by rw [h1]
        _ = Pᵀ * (Xᵀ * gram K n * (Pr * X)) * P := by simp only [Matrix.mul_assoc]
        _ = Pᵀ * (Xᵀ * gram K n * X * Pr) * P := by
            rw [hcomm]
            simp only [Matrix.mul_assoc]
        _ = Pᵀ * gram K n * P := by
            rw [hXsymp]
            simp only [Matrix.mul_assoc]
            rw [hPrP]
        _ = gram K m := by
            rw [hPJ, Matrix.mul_assoc, hPP, Matrix.mul_one]
    refine ⟨ofSymplecticMat Y hYsymp, mat_injective ?_⟩
    rw [mat_spEmbed, mat_ofSymplecticMat, spEmbedMat, hY]
    have e : P * (Pᵀ * X * P - 1) * Pᵀ = Pr * X * Pr - Pr := by
      rw [hPr, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    rw [e]
    exact (hXeq.trans (add_sub_assoc _ _ _)).symm

end Range

end CFSG.ClassicalInvolution.Models.SymplecticPairs
