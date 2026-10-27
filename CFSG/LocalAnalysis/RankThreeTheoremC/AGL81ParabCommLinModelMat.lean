module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding.LeviBlock
  CFSG.QuasithinUnique.Vol2Native.A312L

section Pattern

variable {K : Type*} [Field K] {n : ℕ} {I : Set ℕ}

@[expose] def BlockPat (I : Set ℕ) (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ c ∈ I, ∀ k l : Fin n, (l : ℕ) < c → c ≤ (k : ℕ) → M k l = 0

theorem BlockPat.one : BlockPat I (1 : Matrix (Fin n) (Fin n) K) := by
  intro c _ k l hl hk
  rw [Matrix.one_apply_ne]
  intro h
  subst h
  omega

theorem BlockPat.mul {M N : Matrix (Fin n) (Fin n) K} (hM : BlockPat I M) (hN : BlockPat I N) :
    BlockPat I (M * N) := by
  intro c hc k l hl hk
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : (j : ℕ) < c
  · rw [hM c hc k j hj hk, zero_mul]
  · rw [hN c hc j l hl (not_lt.mp hj), mul_zero]

theorem BlockPat.map {M : Matrix (Fin n) (Fin n) K} (hM : BlockPat I M) (f : K →+* K) :
    BlockPat I (M.map f) := by
  intro c hc k l hl hk
  rw [Matrix.map_apply, hM c hc k l hl hk, map_zero]

@[expose] def ScalarBlocks (I : Set ℕ) (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ a : Fin n, ∃ r : K, blkAt a (linBlockLen n I a) (linBlockLen_le a) M = r • 1

theorem blockPat_of_mem_flagStabilizer {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I) : BlockPat I (g : Matrix (Fin n) (Fin n) K) :=
  fun c hc k l hl hk => stabilizer_entries (mem_flagStabilizer.mp hg c hc) hl hk

theorem mem_flagStabilizer_of_blockPat {g : SpecialLinearGroup (Fin n) K}
    (h : BlockPat I (g : Matrix (Fin n) (Fin n) K)) : g ∈ flagStabilizer n K I :=
  mem_flagStabilizer_of_entries fun k l c hc hl hk => h c hc k l hl hk

theorem map_mem_flagStabilizer (τ : K →+* K) {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ flagStabilizer n K I) : SpecialLinearGroup.map τ g ∈ flagStabilizer n K I := by
  refine mem_flagStabilizer_of_blockPat ?_
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  exact (blockPat_of_mem_flagStabilizer hg).map τ

theorem blkAt_mul_of_blockPat {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a ∈ I)
    (hb : a + m = n ∨ a + m ∈ I) {M N : Matrix (Fin n) (Fin n) K}
    (hM : BlockPat I M) (hN : BlockPat I N) :
    blkAt a m h (M * N) = blkAt a m h M * blkAt a m h N := by
  refine blkAt_mul a m h M N (fun r l hr _ hl => ?_) (fun k c hk _ hc => ?_)
  · rcases ha with rfl | ha
    · exact absurd hl (Nat.not_lt_zero _)
    · exact hM a ha r l hl hr
  · rcases hb with hb | hb
    · exact absurd k.isLt (by omega)
    · exact hN (a + m) hb k c hc hk

theorem blkAt_map (a m : ℕ) (h : a + m ≤ n) (M : Matrix (Fin n) (Fin n) K) (f : K →+* K) :
    blkAt a m h (M.map f) = (blkAt a m h M).map f := rfl

theorem blkAt_smul (a m : ℕ) (h : a + m ≤ n) (M : Matrix (Fin n) (Fin n) K) (r : K) :
    blkAt a m h (r • M) = r • blkAt a m h M := rfl

end Pattern

section Key

variable {K : Type*} [Field K] [CharP K 2] {m : ℕ}

theorem transvection_mul_self {i j : Fin m} (hij : i ≠ j) (s : K) :
    (1 + Matrix.single i j s) * (1 + Matrix.single i j s) = (1 : Matrix (Fin m) (Fin m) K) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hEE : Matrix.single i j s * Matrix.single i j s = 0 :=
    Matrix.single_mul_single_of_ne s i j i hij.symm s
  have hE2 : Matrix.single i j s + Matrix.single i j s = 0 := by
    rw [← two_smul K, h2, zero_smul]
  calc (1 + Matrix.single i j s) * (1 + Matrix.single i j s)
      = 1 + (Matrix.single i j s + Matrix.single i j s) +
        Matrix.single i j s * Matrix.single i j s := by noncomm_ring
    _ = 1 := by rw [hE2, hEE, add_zero, add_zero]

theorem eq_scalar_of_transvection_rel (hm : 2 ≤ m) (σ : K →+* K)
    {B B' : Matrix (Fin m) (Fin m) K} (hBB' : B' * B = 1)
    (h : ∀ i j : Fin m, i ≠ j → ∀ t : K, ∃ c : K,
      B * (1 + Matrix.single i j (σ t)) = c • ((1 + Matrix.single i j t) * B)) :
    (∀ t : K, σ t = t) ∧ ∃ r : K, r ≠ 0 ∧ B = r • 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  let o : Fin m := ⟨0, by omega⟩
  let o' : Fin m := ⟨1, by omega⟩
  have hoo' : o ≠ o' := fun e => by simpa [o, o'] using congrArg Fin.val e
  have hc1 : ∀ i j : Fin m, i ≠ j → ∀ t : K,
      B * Matrix.single i j (σ t) = Matrix.single i j t * B := by
    intro i j hij t
    obtain ⟨c, hc⟩ := h i j hij t
    have hSS := transvection_mul_self hij (σ t)
    have hTT := transvection_mul_self hij t
    have hB : B = (c * c) • B := by
      calc B = B * ((1 + Matrix.single i j (σ t)) * (1 + Matrix.single i j (σ t))) := by
            rw [hSS, mul_one]
        _ = (B * (1 + Matrix.single i j (σ t))) * (1 + Matrix.single i j (σ t)) := by
            rw [mul_assoc]
        _ = (c • ((1 + Matrix.single i j t) * B)) * (1 + Matrix.single i j (σ t)) := by rw [hc]
        _ = c • ((1 + Matrix.single i j t) *
              (B * (1 + Matrix.single i j (σ t)))) := by
            rw [smul_mul_assoc, mul_assoc]
        _ = c • ((1 + Matrix.single i j t) *
              (c • ((1 + Matrix.single i j t) * B))) := by rw [hc]
        _ = (c * c) • (((1 + Matrix.single i j t) * (1 + Matrix.single i j t)) * B) := by
            rw [mul_smul_comm, smul_smul, mul_assoc]
        _ = (c * c) • B := by rw [hTT, one_mul]
    have hcc : c * c = 1 := by
      have h1 := congrArg (fun X => B' * X) hB
      simp only [Matrix.mul_smul, hBB'] at h1
      have h3 := congrFun (congrFun h1 o) o
      simpa [Matrix.smul_apply] using h3.symm
    have hc' : c = 1 := by
      have : (c - 1) * (c - 1) = 0 := by linear_combination hcc + (1 - c) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
    rw [hc', one_smul, mul_add, add_mul, mul_one, one_mul] at hc
    exact add_left_cancel hc
  have e1 : ∀ i j : Fin m, i ≠ j → ∀ t : K, ∀ k : Fin m, k ≠ i → B k i * σ t = 0 := by
    intro i j hij t k hk
    have h3 := congrFun (congrFun (hc1 i j hij t) k) j
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne t i j k j hk B] at h3
  have e2 : ∀ i j : Fin m, i ≠ j → ∀ t : K, B i i * σ t = t * B j j := by
    intro i j hij t
    have h3 := congrFun (congrFun (hc1 i j hij t) i) j
    rwa [Matrix.mul_single_apply_same, Matrix.single_mul_apply_same] at h3
  have hex : ∀ i : Fin m, ∃ j : Fin m, i ≠ j := fun i => by
    by_cases hi : i = o
    · exact ⟨o', fun e => hoo' (hi ▸ e)⟩
    · exact ⟨o, hi⟩
  have hoff : ∀ k i : Fin m, k ≠ i → B k i = 0 := by
    intro k i hki
    obtain ⟨j, hj⟩ := hex i
    have h3 := e1 i j hj 1 k hki
    rwa [map_one, mul_one] at h3
  have hdiag : ∀ i j : Fin m, B i i = B j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h3 := e2 i j hij 1
      rwa [map_one, mul_one, one_mul] at h3
  have hBr : B = B o o • 1 := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      simp [Matrix.one_apply, hdiag k o]
    · simp [Matrix.one_apply, hkl, hoff k l hkl]
  have hr0 : B o o ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hBr
    rw [hBr, mul_zero] at hBB'
    have h3 := congrFun (congrFun hBB' o) o
    simp at h3
  refine ⟨fun t => ?_, B o o, hr0, hBr⟩
  have h3 := e2 o o' hoo' t
  rw [hdiag o' o] at h3
  exact mul_left_cancel₀ hr0 (h3.trans (mul_comm _ _))

end Key

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin
