module

public import CFSG.ClassicalInvolution.Phan.Parabolic.Defs
public import CFSG.ClassicalInvolution.Phan.Parabolic.TorusHom

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ}

theorem eq_one_of_blockEmb2_eq_far {a b : Fin n} (hab : (a : ℕ) + 1 < b) {A B : Su K p f 2}
    (h : blockEmb2 K p f n a A = blockEmb2 K p f n b B) : A = 1 := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  have hx : ¬ ((b : ℕ) ≤ (blockIdx (a : ℕ) (by omega : (a : ℕ) + 2 ≤ n + 1) x).val ∧
      (blockIdx (a : ℕ) (by omega : (a : ℕ) + 2 ≤ n + 1) x).val < b + 2) := by
    have := x.isLt
    simp only [blockIdx_val]
    omega
  have h' := congrFun (congrFun (congrArg (fun g : Su K p f (n + 1) =>
    ((g : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) h)
    (blockIdx (a : ℕ) (by omega : (a : ℕ) + 2 ≤ n + 1) x))
    (blockIdx (a : ℕ) (by omega : (a : ℕ) + 2 ≤ n + 1) y)
  simp only [coe_coe_blockEmb2] at h'
  rw [blockMat_apply_blockIdx, blockMat_apply_of_not_mem_left _ hx] at h'
  rw [h']
  simp [Matrix.one_apply, (blockIdx_injective (by omega : (a : ℕ) + 2 ≤ n + 1)).eq_iff]

theorem range_blockEmb2_inf_far {a b : Fin n} (hab : (a : ℕ) + 1 < b) :
    (blockEmb2 K p f n a).range ⊓ (blockEmb2 K p f n b).range = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  rw [Subgroup.mem_bot, eq_one_of_blockEmb2_eq_far hab hB.symm, map_one]

theorem range_blockEmb2_le_normalizer_far {a b : Fin n} (hab : (a : ℕ) + 1 < b) :
    (blockEmb2 K p f n b).range ≤
      Subgroup.normalizer ((blockEmb2 K p f n a).range : Set (Su K p f (n + 1))) := by
  refine le_trans (fun y hy => ?_) (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨A, rfl⟩
  obtain ⟨B, rfl⟩ := hy
  exact blockEmb2_comm n a b hab A B

theorem mem_torus_of_mul_mem_torus_far {a b : Fin n} (hab : (a : ℕ) + 1 < b)
    {x y : Su K p f (n + 1)} (hx : x ∈ (blockEmb2 K p f n a).range)
    (hy : y ∈ (blockEmb2 K p f n b).range)
    (h : x * y ∈ torus (unitaryInvolution K p f) (n + 1)) :
    x ∈ torus (unitaryInvolution K p f) (n + 1) := by
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  rw [mem_torus_iff] at h ⊢
  intro c d hcd
  have hxy := h c d hcd
  by_cases hd : (b : ℕ) ≤ d.val ∧ d.val < b + 2
  · have hd' : ¬ ((a : ℕ) ≤ d.val ∧ d.val < a + 2) := by omega
    change blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) c d = 0
    rw [blockMat_apply_of_not_mem_right _ _ hd', Matrix.one_apply_ne hcd]
  · change blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) c d = 0
    have hcol : ∀ e, blockMat (n + 1) b.val ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) e d =
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) e d := fun e =>
      blockMat_apply_of_not_mem_right _ e hd
    have hxy' : (blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        blockMat (n + 1) b.val ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) c d = 0 := hxy
    rw [Matrix.mul_apply] at hxy'
    calc blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) c d
        = (blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
            (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c d := by rw [Matrix.mul_one]
      _ = ∑ e, blockMat (n + 1) a.val ((A : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) c e *
            blockMat (n + 1) b.val ((B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) e d := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun e _ => by rw [hcol e]
      _ = 0 := hxy'

theorem exists_blockEmb3_diag {i : Fin n} (h : (i : ℕ) + 1 < n) {A : Su K p f 3}
    (hA : blockEmb3 K p f n i h A ∈ torus (unitaryInvolution K p f) (n + 1)) :
    ∃ u v : normOne (unitaryInvolution K p f),
      blockEmb3 K p f n i h A =
        blockEmb2 K p f n i (torusTwo (unitaryInvolution K p f) u) *
          blockEmb2 K p f n ⟨i + 1, h⟩ (torusTwo (unitaryInvolution K p f) v) := by
  have hAT : A ∈ torus (unitaryInvolution K p f) 3 := by
    rw [mem_torus_iff] at hA ⊢
    intro x y hxy
    have h1 := hA (blockIdx (i : ℕ) (by omega : (i : ℕ) + 3 ≤ n + 1) x)
      (blockIdx (i : ℕ) (by omega : (i : ℕ) + 3 ≤ n + 1) y)
      (fun h' => hxy (blockIdx_injective _ h'))
    rw [coe_coe_blockEmb3, blockMat_apply_blockIdx] at h1
    exact h1
  obtain ⟨s, hs⟩ := (torusEquiv (unitaryInvolution K p f) 2).surjective ⟨A, hAT⟩
  have hsA : A = ((torusEquiv (unitaryInvolution K p f) 2 s : torus (unitaryInvolution K p f) 3) :
      Su K p f 3) := by rw [hs]
  have hs2 : s = Pi.mulSingle (0 : Fin 2) (s 0) * Pi.mulSingle (1 : Fin 2) (s 1) := by
    funext x
    fin_cases x <;> simp
  have hs3 := congrArg (torusEquiv (unitaryInvolution K p f) 2) hs2
  rw [map_mul] at hs3
  refine ⟨s 0, s 1, ?_⟩
  rw [hsA, hs3, Subgroup.coe_mul, coe_torusEquiv_mulSingle, coe_torusEquiv_mulSingle,
    blockEmb2_zero_eq, blockEmb2_one_eq, map_mul]
  exact congrArg₂ _ (DFunLike.congr_fun (blockEmb3_comp_embSUid_two n i h) _)
    (DFunLike.congr_fun (blockEmb3_comp_embSUid_zero n i h) _)

theorem torus_inf_blockSup {J : Set (Fin n)} (hJ : J.encard ≤ 2) {g : Su K p f (n + 1)}
    (hg : g ∈ blockSup K p f n J) (hT : g ∈ torus (unitaryInvolution K p f) (n + 1)) :
    g = 1 ∨ ∃ a ∈ J, ∃ b ∈ J, ∃ u v : normOne (unitaryInvolution K p f),
      g = blockEmb2 K p f n a (torusTwo (unitaryInvolution K p f) u) *
        blockEmb2 K p f n b (torusTwo (unitaryInvolution K p f) v) := by
  have hpair : ∀ a b : Fin n, a < b → g ∈ blockSup K p f n {a, b} →
      ∃ u v : normOne (unitaryInvolution K p f),
        g = blockEmb2 K p f n a (torusTwo (unitaryInvolution K p f) u) *
          blockEmb2 K p f n b (torusTwo (unitaryInvolution K p f) v) := by
    intro a b hab hgab
    rw [blockSup_pair] at hgab
    by_cases hfar : (a : ℕ) + 1 < b
    · have hmem : g ∈ ((blockEmb2 K p f n a).range : Set (Su K p f (n + 1))) *
          ((blockEmb2 K p f n b).range : Set (Su K p f (n + 1))) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _
          (range_blockEmb2_le_normalizer_far hfar)]
        exact hgab
      obtain ⟨x, hx, y, hy, rfl⟩ := hmem
      have hxT : x ∈ torus (unitaryInvolution K p f) (n + 1) :=
        mem_torus_of_mul_mem_torus_far hfar hx hy hT
      have hyT : y ∈ torus (unitaryInvolution K p f) (n + 1) := by
        have := (torus (unitaryInvolution K p f) (n + 1)).mul_mem
          ((torus (unitaryInvolution K p f) (n + 1)).inv_mem hxT) hT
        simpa using this
      obtain ⟨u, hu⟩ := exists_torusTwo_of_mem_torus a hxT hx
      obtain ⟨v, hv⟩ := exists_torusTwo_of_mem_torus b hyT hy
      exact ⟨u, v, by rw [hu, hv]⟩
    · have hb : (b : ℕ) = a + 1 := by omega
      have hai : (a : ℕ) + 1 < n := by omega
      obtain rfl : b = ⟨a + 1, hai⟩ := Fin.ext hb
      have hle : (blockEmb2 K p f n a).range ⊔ (blockEmb2 K p f n ⟨a + 1, hai⟩).range ≤
          (blockEmb3 K p f n a hai).range :=
        sup_le (range_blockEmb2_le_range_blockEmb3 n a hai)
          (range_blockEmb2_succ_le_range_blockEmb3 n a hai)
      obtain ⟨A, hA⟩ := hle hgab
      subst hA
      exact exists_blockEmb3_diag hai hT
  rcases hJ.lt_or_eq with h | h
  · have h1 : J.encard ≤ 1 := by
      have : (2 : ℕ∞) = 1 + 1 := by norm_num
      rw [this] at h
      exact (ENat.lt_add_one_iff (by simp)).1 h
    rcases Set.encard_le_one_iff_eq.1 h1 with rfl | ⟨a, rfl⟩
    · left
      rw [blockSup_empty] at hg
      exact hg
    · right
      rw [blockSup_singleton] at hg
      obtain ⟨u, hu⟩ := exists_torusTwo_of_mem_torus a hT hg
      refine ⟨a, rfl, a, rfl, u, 1, ?_⟩
      rw [map_one, map_one, mul_one, hu]
  · obtain ⟨a, b, hab, rfl⟩ := Set.encard_eq_two.1 h
    right
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · obtain ⟨u, v, huv⟩ := hpair a b hlt hg
      exact ⟨a, by simp, b, by simp, u, v, huv⟩
    · rw [Set.pair_comm] at hg
      obtain ⟨u, v, huv⟩ := hpair b a hlt hg
      exact ⟨b, by simp, a, by simp, u, v, huv⟩

end CFSG.ClassicalInvolution.Phan
