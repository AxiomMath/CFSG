module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107LAlt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107L

open CFSG.Open CFSG.Assembly Matrix
open scoped commutatorElement

section AltM

variable {K : Type} [Field K] {m : ℕ}

@[expose] def blkMat (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K :=
  fromBlocks X 0 0 1

theorem blkMat_mul (X Y : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :
    blkMat (X * Y) = blkMat X * blkMat Y := by
  simp [blkMat, fromBlocks_multiply]

theorem blkMat_one : blkMat (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
  simp [blkMat, fromBlocks_one]

@[expose] def blkMonoid : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K →* Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K where
  toFun := blkMat
  map_one' := blkMat_one
  map_mul' := blkMat_mul

@[expose] def blkGL : GL (Fin m ⊕ Fin m) K →* GL (LargeEvenMinusIdx m) K :=
  Units.map blkMonoid

theorem blkGL_val (g : GL (Fin m ⊕ Fin m) K) :
    ((blkGL g : GL (LargeEvenMinusIdx m) K) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) =
      blkMat (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
  rfl

theorem quad_blkMat (b c : K) (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    (hA : ∀ w : Fin m ⊕ Fin m → K, CFSG.Open.StatedQuadPlus m K (A *ᵥ w) = CFSG.Open.StatedQuadPlus m K w)
    (v : LargeEvenMinusIdx m → K) :
    LargeEvenQMinus m b c (blkMat A *ᵥ v) = LargeEvenQMinus m b c v := by
  have hdec : ∀ w : LargeEvenMinusIdx m → K, LargeEvenQMinus m b c w =
      CFSG.Open.StatedQuadPlus m K (w ∘ Sum.inl) + w (Sum.inr 0) ^ 2 + b * w (Sum.inr 0) * w (Sum.inr 1) +
        c * w (Sum.inr 1) ^ 2 := by
    intro w
    simp [LargeEvenQMinus, CFSG.Open.StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Function.comp]
  have hl : (blkMat A *ᵥ v) ∘ Sum.inl = A *ᵥ (v ∘ Sum.inl) := by
    funext i
    simp [blkMat, fromBlocks_mulVec]
  have hr : (blkMat A *ᵥ v) ∘ Sum.inr = v ∘ Sum.inr := by
    funext i
    simp [blkMat, fromBlocks_mulVec]
  rw [hdec, hdec]
  have h1 : (blkMat A *ᵥ v) (Sum.inr 0) = v (Sum.inr 0) := congrFun hr 0
  have h2 : (blkMat A *ᵥ v) (Sum.inr 1) = v (Sum.inr 1) := congrFun hr 1
  have h3 : CFSG.Open.StatedQuadPlus m K ((blkMat A *ᵥ v) ∘ Sum.inl) =
      CFSG.Open.StatedQuadPlus m K (v ∘ Sum.inl) := by
    rw [hl]
    exact hA _
  rw [h1, h2, h3]

theorem blkGL_mem_orth (b c : K) (g : GL (Fin m ⊕ Fin m) K)
    (hA : ∀ w : Fin m ⊕ Fin m → K,
      CFSG.Open.StatedQuadPlus m K ((g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w) =
        CFSG.Open.StatedQuadPlus m K w) :
    blkGL g ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c) := by
  unfold LargeEvenOrthGroup CFSG.PGLModel.orthogonalGroup
  apply Subgroup.subset_closure
  intro v
  rw [blkGL_val]
  exact quad_blkMat b c _ hA v

theorem altM_single_mem (h2 : (2 : K) = 0) (hm : 3 ≤ m) (b c : K) (s : OffIdx m) (t : K) :
    blkGL (altHom m K (Multiplicative.ofAdd (Pi.single s t))) ∈ LargeEvenOmega (LargeEvenQMinus m b c) := by
  obtain ⟨A, hA, Yf, heq⟩ := altHom_single_comm h2 hm s t
  rw [heq, map_commutatorElement, largeEvenOmega_def]
  apply Subgroup.commutator_mem_commutator
  · apply blkGL_mem_orth b c (leviU A hA)
    intro w
    exact quad_levi hA w
  · apply blkGL_mem_orth b c (unipU h2 (offMat Yf))
    intro w
    exact quad_unipBlk h2 Yf w

theorem blkMat_altHom_fix (x : Multiplicative (OffIdx m → K)) (i0 : Fin m) :
    blkMat (altHom m K x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        Pi.single (Sum.inl (Sum.inl i0)) (1 : K) =
      Pi.single (Sum.inl (Sum.inl i0)) 1 := by
  have hX := altHom_fix i0 x
  have hl : (Pi.single (Sum.inl (Sum.inl i0)) (1 : K) : LargeEvenMinusIdx m → K) ∘ Sum.inl =
      Pi.single (Sum.inl i0) 1 := by
    funext t
    simp [Pi.single_apply]
  have hr : (Pi.single (Sum.inl (Sum.inl i0)) (1 : K) : LargeEvenMinusIdx m → K) ∘ Sum.inr = 0 := by
    funext t
    simp [Pi.single_apply]
  funext k
  rcases k with k | k
  · simp only [blkMat, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply]
    rw [hl, hX, hr, zero_mulVec, Pi.zero_apply, add_zero]
    simp [Pi.single_apply]
  · simp only [blkMat, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply]
    rw [hr]
    simp [Pi.single_apply]

end AltM

theorem pRank_alt_minus_ge {m n : ℕ} (hn : 1 ≤ n) (hm : 3 ≤ m) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (b c : K) :
    n * m.choose 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  haveI : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card (p := 2) (f := n) hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let φ : Multiplicative (OffIdx m → K) →* GL (LargeEvenMinusIdx m) K := (blkGL).comp (altHom m K)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : blkMat (unipBlk (offMat x.toAdd)) = 1 := by
      have := congrArg (fun g : GL (LargeEvenMinusIdx m) K => (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K)) hx
      simpa [φ, blkGL_val, altHom_val] using this
    have h1' : unipBlk (offMat x.toAdd) = 1 := by
      unfold blkMat at h1
      rw [← fromBlocks_one] at h1
      exact (Matrix.fromBlocks_inj.1 h1).1
    have hf : x.toAdd = 0 := eq_zero_of_offMat (unipBlk_eq_one_iff h1')
    apply Multiplicative.toAdd.injective
    rw [hf, toAdd_one]
  have hH : ∀ x, φ x ∈ LargeEvenOmega (LargeEvenQMinus m b c) := by
    intro x
    have hsum : ∑ s : OffIdx m, Pi.single s (x.toAdd s) = x.toAdd := by
      funext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hdec : x = ∏ s : OffIdx m, Multiplicative.ofAdd (Pi.single s (x.toAdd s)) := by
      rw [← ofAdd_sum, hsum, ofAdd_toAdd]
    let T : Subgroup (Multiplicative (OffIdx m → K)) :=
      (LargeEvenOmega (LargeEvenQMinus m b c)).comap φ
    have hx : x ∈ T := by
      rw [hdec]
      exact Subgroup.prod_mem T (fun s _ => altM_single_mem h2 hm b c s _)
    exact hx
  have hv : (Pi.single (Sum.inl (Sum.inl (⟨0, by omega⟩ : Fin m))) (1 : K) :
      LargeEvenMinusIdx m → K) ≠ 0 := by
    intro h
    have := congrFun h (Sum.inl (Sum.inl ⟨0, by omega⟩))
    simp at this
  have hfix : ∀ x, (φ x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K) *ᵥ
      Pi.single (Sum.inl (Sum.inl (⟨0, by omega⟩ : Fin m))) (1 : K) =
        Pi.single (Sum.inl (Sum.inl (⟨0, by omega⟩ : Fin m))) 1 :=
    fun x => blkMat_altHom_fix x ⟨0, by omega⟩
  exact CFSG.SectionRank.ClassicalOdd.le_pRank_statedProj (ι := LargeEvenMinusIdx m) (K := K)
    (H := LargeEvenOmega (LargeEvenQMinus m b c)) (A := Multiplicative (OffIdx m → K)) (p := 2)
    (k := n * m.choose 2) (by norm_num) (fun a b => mul_comm a b)
    (fun a => CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) (p := 2) a)
    (card_altParam hK) φ hinj hH hv hfix

end CFSG.LocalAnalysis.GLTheoremA.I107L

end
