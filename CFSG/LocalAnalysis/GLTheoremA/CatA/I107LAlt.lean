module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LHerm

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly Matrix
open scoped commutatorElement

section Alt

variable {K : Type} [Field K] {m : ℕ}

@[expose] def offMat (f : OffIdx m → K) : Matrix (Fin m) (Fin m) K := Matrix.of (offEntry f)

@[expose] def unipBlk (X : Matrix (Fin m) (Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  fromBlocks 1 X 0 1

@[expose] def levi (A : Matrix (Fin m) (Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  fromBlocks A 0 0 Aᵀ

theorem offMat_add (f g : OffIdx m → K) : offMat (f + g) = offMat f + offMat g := by
  ext i j
  simp [offMat, offEntry_add]

theorem offMat_zero : offMat (0 : OffIdx m → K) = 0 := by
  ext i j
  simp [offMat, offEntry_zero]

theorem add_self_eq_zero_matrix (h2 : (2 : K) = 0) (M : Matrix (Fin m) (Fin m) K) : M + M = 0 := by
  ext a b
  rw [Matrix.add_apply, Matrix.zero_apply, ← two_mul, h2, zero_mul]

theorem unipBlk_mul (X Y : Matrix (Fin m) (Fin m) K) : unipBlk X * unipBlk Y = unipBlk (X + Y) := by
  simp [unipBlk, fromBlocks_multiply, add_comm]

theorem unipBlk_zero : unipBlk (0 : Matrix (Fin m) (Fin m) K) = 1 := by
  simp [unipBlk, fromBlocks_one]

theorem unipBlk_mul_self (h2 : (2 : K) = 0) (Y : Matrix (Fin m) (Fin m) K) :
    unipBlk Y * unipBlk Y = 1 := by
  rw [unipBlk_mul, add_self_eq_zero_matrix h2, unipBlk_zero]

theorem levi_mul_self {A : Matrix (Fin m) (Fin m) K} (hAA : A * A = 1) :
    levi A * levi A = 1 := by
  have hAt : Aᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAA, Matrix.transpose_one]
  simp [levi, fromBlocks_multiply, hAA, hAt, fromBlocks_one]

theorem levi_unip_comm {A Y : Matrix (Fin m) (Fin m) K} (hAA : A * A = 1) :
    levi A * unipBlk Y * levi A * unipBlk Y = unipBlk (Y + A * Y * Aᵀ) := by
  have hAt : Aᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, hAA, Matrix.transpose_one]
  simp only [levi, unipBlk, fromBlocks_multiply, Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.mul_add, Matrix.add_mul]
  rw [hAA, hAt]
  simp [fromBlocks_one, add_comm, Matrix.mul_assoc]

theorem quad_eq_dot (w : Fin m ⊕ Fin m → K) :
    CFSG.Open.StatedQuadPlus m K w = (w ∘ Sum.inl) ⬝ᵥ (w ∘ Sum.inr) := by
  simp only [CFSG.Open.StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, dotProduct, Function.comp]

theorem unipBlk_mulVec_inl (Y : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m → K) :
    (unipBlk Y *ᵥ v) ∘ Sum.inl = (v ∘ Sum.inl) + Y *ᵥ (v ∘ Sum.inr) := by
  funext i
  simp [unipBlk, fromBlocks_mulVec, Matrix.one_mulVec]

theorem unipBlk_mulVec_inr (Y : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m → K) :
    (unipBlk Y *ᵥ v) ∘ Sum.inr = v ∘ Sum.inr := by
  funext i
  simp [unipBlk, fromBlocks_mulVec, Matrix.one_mulVec]

theorem levi_mulVec_inl (A : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m → K) :
    (levi A *ᵥ v) ∘ Sum.inl = A *ᵥ (v ∘ Sum.inl) := by
  funext i
  simp [levi, fromBlocks_mulVec]

theorem levi_mulVec_inr (A : Matrix (Fin m) (Fin m) K) (v : Fin m ⊕ Fin m → K) :
    (levi A *ᵥ v) ∘ Sum.inr = Aᵀ *ᵥ (v ∘ Sum.inr) := by
  funext i
  simp [levi, fromBlocks_mulVec]

theorem quad_levi {A : Matrix (Fin m) (Fin m) K} (hAA : A * A = 1) (v : Fin m ⊕ Fin m → K) :
    CFSG.Open.StatedQuadPlus m K (levi A *ᵥ v) = CFSG.Open.StatedQuadPlus m K v := by
  rw [quad_eq_dot, quad_eq_dot, levi_mulVec_inl, levi_mulVec_inr, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec]

theorem dot_offMat_mulVec (h2 : (2 : K) = 0) (f : OffIdx m → K) (y : Fin m → K) :
    y ⬝ᵥ (offMat f *ᵥ y) = 0 := by
  simp only [dotProduct, Matrix.mulVec, offMat, Matrix.of_apply, Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_involution (fun p _ => p.swap)
  · intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [offEntry_comm f p.2 p.1]
    have : y p.1 * (offEntry f p.1 p.2 * y p.2) + y p.2 * (offEntry f p.1 p.2 * y p.1) =
        (2 : K) * (y p.1 * (offEntry f p.1 p.2 * y p.2)) := by ring
    rw [this, h2, zero_mul]
  · intro p _ hp hswap
    apply hp
    have h1 : p.1 = p.2 := by
      have := congrArg Prod.fst hswap
      simpa using this.symm
    have hd : offEntry f p.1 p.2 = 0 := by
      simp only [offEntry, dif_pos h1]
    simp [hd]
  · intro p _
    simp
  · intro p _
    simp

theorem quad_unipBlk (h2 : (2 : K) = 0) (f : OffIdx m → K) (v : Fin m ⊕ Fin m → K) :
    CFSG.Open.StatedQuadPlus m K (unipBlk (offMat f) *ᵥ v) = CFSG.Open.StatedQuadPlus m K v := by
  rw [quad_eq_dot, quad_eq_dot, unipBlk_mulVec_inl, unipBlk_mulVec_inr, add_dotProduct,
    dotProduct_comm (offMat f *ᵥ _), dot_offMat_mulVec h2, add_zero]

@[expose] noncomputable def altHom (m : ℕ) (K : Type) [Field K] :
    Multiplicative (OffIdx m → K) →* GL (Fin m ⊕ Fin m) K :=
  CFSG.SectionRank.ClassicalOdd.glOfAdd (fun f => unipBlk (offMat f))
    (by simp only [offMat_zero, unipBlk_zero])
    (fun f g => by rw [offMat_add, unipBlk_mul])

theorem altHom_val (f : Multiplicative (OffIdx m → K)) :
    ((altHom m K f : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      unipBlk (offMat f.toAdd) :=
  CFSG.SectionRank.ClassicalOdd.coe_glOfAdd _ _ _ _

@[expose] def leviU (A : Matrix (Fin m) (Fin m) K) (hAA : A * A = 1) : GL (Fin m ⊕ Fin m) K :=
  ⟨levi A, levi A, levi_mul_self hAA, levi_mul_self hAA⟩

@[expose] def unipU (h2 : (2 : K) = 0) (Y : Matrix (Fin m) (Fin m) K) : GL (Fin m ⊕ Fin m) K :=
  ⟨unipBlk Y, unipBlk Y, unipBlk_mul_self h2 Y, unipBlk_mul_self h2 Y⟩

theorem leviU_inv {A : Matrix (Fin m) (Fin m) K} (hAA : A * A = 1) :
    (leviU A hAA)⁻¹ = leviU A hAA :=
  inv_eq_of_mul_eq_one_right (Units.ext (levi_mul_self hAA))

theorem unipU_inv (h2 : (2 : K) = 0) (Y : Matrix (Fin m) (Fin m) K) :
    (unipU h2 Y)⁻¹ = unipU h2 Y :=
  inv_eq_of_mul_eq_one_right (Units.ext (unipBlk_mul_self h2 Y))

theorem offMat_pair {i j : Fin m} (hij : i ≠ j) (c : K) (hs : ¬ (s(i, j) : Sym2 (Fin m)).IsDiag) :
    offMat (Pi.single (⟨s(i, j), hs⟩ : OffIdx m) c) = Matrix.single i j c + Matrix.single j i c := by
  ext x y
  simp only [offMat, Matrix.of_apply, offEntry, Matrix.add_apply, Matrix.single_apply, Pi.single_apply,
    Subtype.mk.injEq, Sym2.eq_iff]
  by_cases hxy : x = y
  · subst hxy
    simp only [dif_pos rfl]
    split_ifs <;> simp_all [eq_comm]
  · simp only [dif_neg hxy]
    split_ifs <;> simp_all [eq_comm]

theorem key_identity {i j q : Fin m} (hij : i ≠ j) (hiq : i ≠ q) (hjq : j ≠ q) (c : K) (h2 : (2 : K) = 0) :
    (1 + Matrix.single i q (1 : K)) * (Matrix.single q j c + Matrix.single j q c) *
        (1 + Matrix.single q i (1 : K)) + (Matrix.single q j c + Matrix.single j q c) =
      Matrix.single i j c + Matrix.single j i c := by
  have hqj : q ≠ j := Ne.symm hjq
  have e1 : Matrix.single i q (1 : K) * (Matrix.single q j c + Matrix.single j q c) =
      Matrix.single i j c := by
    simp [Matrix.mul_add, hqj]
  have e2 : (Matrix.single q j c + Matrix.single j q c) * Matrix.single q i (1 : K) =
      Matrix.single j i c := by
    simp [Matrix.add_mul, hjq]
  have e3 : Matrix.single i j c * Matrix.single q i (1 : K) = 0 := by
    simp [hjq]
  have step : (1 + Matrix.single i q (1 : K)) * (Matrix.single q j c + Matrix.single j q c) *
      (1 + Matrix.single q i (1 : K)) =
      (Matrix.single q j c + Matrix.single j q c) + Matrix.single i j c + Matrix.single j i c := by
    rw [add_mul, one_mul, e1, mul_add, mul_one, add_mul, e2, e3, add_zero]
  have hY := add_self_eq_zero_matrix h2 (Matrix.single q j c + Matrix.single j q c)
  rw [step]
  calc (Matrix.single q j c + Matrix.single j q c) + Matrix.single i j c + Matrix.single j i c +
        (Matrix.single q j c + Matrix.single j q c)
      = Matrix.single i j c + Matrix.single j i c +
        ((Matrix.single q j c + Matrix.single j q c) + (Matrix.single q j c + Matrix.single j q c)) := by
        abel
    _ = Matrix.single i j c + Matrix.single j i c := by rw [hY, add_zero]

theorem exists_third {m : ℕ} (hm : 3 ≤ m) (i j : Fin m) : ∃ q : Fin m, q ≠ i ∧ q ≠ j := by
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin m)) ⊆ {i, j} := by
    intro q _
    by_cases hqi : q = i
    · simp [hqi]
    · simp [h q hqi]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem leviU_mem {K : Type} [Field K] {m : ℕ} {A : Matrix (Fin m) (Fin m) K} (hAA : A * A = 1) :
    leviU A hAA ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
  unfold LargeEvenOrthGroup CFSG.PGLModel.orthogonalGroup
  apply Subgroup.subset_closure
  intro v
  exact quad_levi hAA v

theorem unipU_mem {K : Type} [Field K] {m : ℕ} (h2 : (2 : K) = 0) (f : OffIdx m → K) :
    unipU h2 (offMat f) ∈ LargeEvenOrthGroup (LargeEvenQPlus K m) := by
  unfold LargeEvenOrthGroup CFSG.PGLModel.orthogonalGroup
  apply Subgroup.subset_closure
  intro v
  exact quad_unipBlk h2 f v

theorem comm_leviU_unipU {K : Type} [Field K] {m : ℕ} {A Y : Matrix (Fin m) (Fin m) K} (h2 : (2 : K) = 0)
    (hAA : A * A = 1) (f : OffIdx m → K) (hf : Y + A * Y * Aᵀ = offMat f) :
    ⁅leviU A hAA, unipU h2 Y⁆ = altHom m K (Multiplicative.ofAdd f) := by
  apply Units.ext
  rw [commutatorElement_def, leviU_inv, unipU_inv, altHom_val]
  simp only [Units.val_mul]
  show levi A * unipBlk Y * levi A * unipBlk Y = _
  rw [levi_unip_comm hAA, hf, toAdd_ofAdd]

theorem altHom_single_comm {K : Type} [Field K] {m : ℕ} (h2 : (2 : K) = 0) (hm : 3 ≤ m) (s : OffIdx m) (c : K) :
    ∃ (A : Matrix (Fin m) (Fin m) K) (hA : A * A = 1) (Yf : OffIdx m → K),
      altHom m K (Multiplicative.ofAdd (Pi.single s c)) = ⁅leviU A hA, unipU h2 (offMat Yf)⁆ := by
  obtain ⟨t, ht⟩ := s
  induction t using Sym2.ind with
  | _ i j =>
    have hij : i ≠ j := fun e => ht (Sym2.mk_isDiag_iff.2 e)
    obtain ⟨q, hqi, hqj⟩ := exists_third hm i j
    have hsq : ¬ (s(q, j) : Sym2 (Fin m)).IsDiag := by
      rw [Sym2.mk_isDiag_iff]
      exact hqj
    have hiq : i ≠ q := Ne.symm hqi
    have hjq : j ≠ q := Ne.symm hqj
    have hqi' : q ≠ i := hqi
    have hA : (1 + Matrix.single i q (1 : K)) * (1 + Matrix.single i q (1 : K)) = 1 := by
      have hE : Matrix.single i q (1 : K) * Matrix.single i q (1 : K) = 0 := by
        simp [hqi']
      calc (1 + Matrix.single i q (1 : K)) * (1 + Matrix.single i q (1 : K))
          = 1 + (Matrix.single i q (1 : K) + Matrix.single i q (1 : K)) +
            Matrix.single i q (1 : K) * Matrix.single i q (1 : K) := by noncomm_ring
        _ = 1 := by
          rw [add_self_eq_zero_matrix h2, hE]
          simp
    have hAt : (1 + Matrix.single i q (1 : K))ᵀ = 1 + Matrix.single q i (1 : K) := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have hY : offMat (Pi.single (⟨s(q, j), hsq⟩ : OffIdx m) c) =
        Matrix.single q j c + Matrix.single j q c := offMat_pair hqj c hsq
    have hf : offMat (Pi.single (⟨s(q, j), hsq⟩ : OffIdx m) c) +
        (1 + Matrix.single i q (1 : K)) * offMat (Pi.single (⟨s(q, j), hsq⟩ : OffIdx m) c) *
          (1 + Matrix.single i q (1 : K))ᵀ = offMat (Pi.single (⟨s(i, j), ht⟩ : OffIdx m) c) := by
      rw [hY, hAt, offMat_pair hij c ht, add_comm]
      exact key_identity hij hiq hjq c h2
    exact ⟨1 + Matrix.single i q (1 : K), hA, Pi.single (⟨s(q, j), hsq⟩ : OffIdx m) c,
      (comm_leviU_unipU h2 hA (Pi.single (⟨s(i, j), ht⟩ : OffIdx m) c) hf).symm⟩

theorem altHom_single_mem {K : Type} [Field K] {m : ℕ} (h2 : (2 : K) = 0) (hm : 3 ≤ m) (s : OffIdx m) (c : K) :
    altHom m K (Multiplicative.ofAdd (Pi.single s c)) ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
  obtain ⟨A, hA, Yf, heq⟩ := altHom_single_comm h2 hm s c
  rw [heq, largeEvenOmega_def]
  exact Subgroup.commutator_mem_commutator (leviU_mem hA) (unipU_mem h2 Yf)

theorem altHom_mem {K : Type} [Field K] {m : ℕ} (h2 : (2 : K) = 0) (hm : 3 ≤ m)
    (f : Multiplicative (OffIdx m → K)) : altHom m K f ∈ LargeEvenOmega (LargeEvenQPlus K m) := by
  have hsum : ∑ s : OffIdx m, Pi.single s (f.toAdd s) = f.toAdd := by
    funext t
    simp [Finset.sum_apply, Pi.single_apply]
  have hdec : f = ∏ s : OffIdx m, Multiplicative.ofAdd (Pi.single s (f.toAdd s)) := by
    rw [← ofAdd_sum, hsum, ofAdd_toAdd]
  let T : Subgroup (Multiplicative (OffIdx m → K)) :=
    (LargeEvenOmega (LargeEvenQPlus K m)).comap (altHom m K)
  have hf : f ∈ T := by
    rw [hdec]
    exact Subgroup.prod_mem T (fun s _ => altHom_single_mem h2 hm s _)
  exact hf

theorem unipBlk_eq_one_iff {X : Matrix (Fin m) (Fin m) K} (h : unipBlk X = 1) : X = 0 := by
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simpa [unipBlk, Matrix.fromBlocks_apply₁₂, Matrix.one_apply] using this

theorem eq_zero_of_offMat {f : OffIdx m → K} (h : offMat f = 0) : f = 0 := by
  funext s
  obtain ⟨t, ht⟩ := s
  induction t using Sym2.ind with
  | _ i j =>
    have hij : i ≠ j := fun e => ht (Sym2.mk_isDiag_iff.2 e)
    have hf : f ⟨s(i, j), ht⟩ = offEntry f i j := by
      simp only [offEntry, dif_neg hij]
    rw [hf]
    have := congrFun (congrFun h i) j
    simpa [offMat, hij] using this

theorem altHom_injective : Function.Injective (altHom m K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : unipBlk (offMat x.toAdd) = 1 := by
    rw [← altHom_val, hx, Units.val_one]
  have hf : x.toAdd = 0 := eq_zero_of_offMat (unipBlk_eq_one_iff h1)
  apply Multiplicative.toAdd.injective
  rw [hf, toAdd_one]

theorem altHom_fix (i0 : Fin m) (x : Multiplicative (OffIdx m → K)) :
    (altHom m K x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ Pi.single (Sum.inl i0) (1 : K) =
      Pi.single (Sum.inl i0) 1 := by
  rw [altHom_val]
  have hr : (Pi.single (Sum.inl i0) (1 : K) : Fin m ⊕ Fin m → K) ∘ Sum.inr = 0 := by
    funext t
    simp [Pi.single_apply]
  funext k
  rcases k with k | k
  · have h := congrFun (unipBlk_mulVec_inl (offMat x.toAdd) (Pi.single (Sum.inl i0) (1 : K))) k
    simp only [Function.comp_apply] at h
    rw [h, hr, Matrix.mulVec_zero, add_zero]
    simp [Pi.single_apply]
  · have h := congrFun (unipBlk_mulVec_inr (offMat x.toAdd) (Pi.single (Sum.inl i0) (1 : K))) k
    simp only [Function.comp_apply] at h
    rw [h]

theorem card_altParam {n : ℕ} {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card (Multiplicative (OffIdx m → K)) = 2 ^ (n * m.choose 2) := by
  rw [CFSG.SectionRank.ClassicalOdd.card_multiplicative_fun hK, Sym2.card_subtype_not_diag, Fintype.card_fin]

end Alt

theorem pRank_alt_plus_ge {m n : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) :
    n * m.choose 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hv : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin m)) (1 : K) : Fin m ⊕ Fin m → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl ⟨0, by omega⟩)
    simp at this
  exact CFSG.SectionRank.ClassicalOdd.le_pRank_statedProj (ι := Fin m ⊕ Fin m) (K := K)
    (H := LargeEvenOmega (LargeEvenQPlus K m)) (A := Multiplicative (OffIdx m → K)) (p := 2)
    (k := n * m.choose 2) (by norm_num) (fun a b => mul_comm a b)
    (fun a => CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) (p := 2) a)
    (card_altParam hK) (altHom m K) altHom_injective (altHom_mem h2 hm) hv
    (fun x => altHom_fix ⟨0, by omega⟩ x)

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
