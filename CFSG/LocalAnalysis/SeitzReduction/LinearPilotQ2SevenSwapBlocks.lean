module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SwapRow

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Transvections

variable {n : ℕ} {K : Type*} [Field K]

theorem transvection_mul_transvection_mul_inv_mul_inv {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (s u : K) :
    SpecialLinearGroup.transvection hij s * SpecialLinearGroup.transvection hjk u *
        (SpecialLinearGroup.transvection hij s)⁻¹ * (SpecialLinearGroup.transvection hjk u)⁻¹ =
      SpecialLinearGroup.transvection hik (s * u) := by
  rw [SpecialLinearGroup.transvection_inv, SpecialLinearGroup.transvection_inv]
  apply Subtype.ext
  change (SpecialLinearGroup.transvection hij s : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hjk u : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hij (-s) : Matrix (Fin n) (Fin n) K) *
      (SpecialLinearGroup.transvection hjk (-u) : Matrix (Fin n) (Fin n) K) =
      (SpecialLinearGroup.transvection hik (s * u) : Matrix (Fin n) (Fin n) K)
  simp only [SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    mul_one, one_mul, single_mul_single_same, single_mul_single_of_ne _ _ _ _ hjk.symm,
    single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hik.symm]
  simp only [zero_mul, add_zero, mul_neg, neg_mul, neg_neg, ← single_neg]
  abel

theorem blockSL_union_le_sup {A B : Finset (Fin n)} {x : Fin n} (hxA : x ∈ A) (hxB : x ∈ B) :
    blockSL (K := K) (A ∪ B) ≤ blockSL A ⊔ blockSL B := by
  rw [blockSL_eq_closure (A ∪ B), Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, hi, hj, rfl⟩
  have key : ∀ (A B : Finset (Fin n)), x ∈ A → x ∈ B → i ∈ A → j ∈ B → i ∉ B → j ∉ A →
      LinearFlag.proj n K (SpecialLinearGroup.transvection hij c) ∈
        blockSL (K := K) A ⊔ blockSL B := by
    intro A B hxA hxB hiA hjB hiB hjA
    have hix : i ≠ x := fun h => hiB (h ▸ hxB)
    have hxj : x ≠ j := fun h => hjA (h ▸ hxA)
    have hA : LinearFlag.proj n K (SpecialLinearGroup.transvection hix c) ∈
        blockSL (K := K) A ⊔ blockSL B :=
      mem_sup_left (proj_mem_blockSL (transvection_mem_blockSpecialLinear hix hiA hxA c))
    have hB : LinearFlag.proj n K (SpecialLinearGroup.transvection hxj (1 : K)) ∈
        blockSL (K := K) A ⊔ blockSL B :=
      mem_sup_right (proj_mem_blockSL (transvection_mem_blockSpecialLinear hxj hxB hjB 1))
    rw [← mul_one c, ← transvection_mul_transvection_mul_inv_mul_inv hix hxj hij c 1, map_mul,
      map_mul, map_mul, map_inv, map_inv]
    exact mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  rw [Finset.mem_union] at hi hj
  by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A
  · exact mem_sup_left (proj_mem_blockSL (transvection_mem_blockSpecialLinear hij hiA hjA c))
  · have hjB : j ∈ B := hj.resolve_left hjA
    by_cases hiB : i ∈ B
    · exact mem_sup_right (proj_mem_blockSL (transvection_mem_blockSpecialLinear hij hiB hjB c))
    · exact key A B hxA hxB hiA hjB hiB hjA
  · have hiB : i ∈ B := hi.resolve_left hiA
    by_cases hjB : j ∈ B
    · exact mem_sup_right (proj_mem_blockSL (transvection_mem_blockSpecialLinear hij hiB hjB c))
    · rw [sup_comm]
      exact key B A hxB hxA hiB hjA hiA hjB
  · exact mem_sup_right (proj_mem_blockSL (transvection_mem_blockSpecialLinear hij
      (hi.resolve_left hiA) (hj.resolve_left hjA) c))

theorem blockSL_sup_sup_eq_top_seven {m : ℕ} (K : Type*) [Field K]
    {i₀ i₁ i₂ i₃ i₄ i₅ i₆ : Fin (m + 1)} (h₀ : (i₀ : ℕ) = 0) (h₁ : (i₁ : ℕ) = 1)
    (h₂ : (i₂ : ℕ) = 2) (h₃ : (i₃ : ℕ) = 3) (h₄ : (i₄ : ℕ) = 4) (h₅ : (i₅ : ℕ) = 5)
    (h₆ : (i₆ : ℕ) = 6) :
    blockSL (K := K) (({i₀, i₁} : Finset (Fin (m + 1)))ᶜ \ {i₂, i₃}) ⊔
      blockSL (K := K) (({i₀, i₁} : Finset (Fin (m + 1)))ᶜ \ {i₄, i₅}) ⊔
        blockSL (K := K) (({i₂, i₃} : Finset (Fin (m + 1)))ᶜ \ {i₄, i₅}) = ⊤ := by
  have hU : (Finset.univ : Finset (Fin (m + 1))) =
      ((({i₀, i₁} : Finset (Fin (m + 1)))ᶜ \ {i₂, i₃}) ∪
        (({i₀, i₁} : Finset (Fin (m + 1)))ᶜ \ {i₄, i₅})) ∪
          (({i₂, i₃} : Finset (Fin (m + 1)))ᶜ \ {i₄, i₅}) := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_union, mem_compl_pair_sdiff_pair_iff, true_iff]
    omega
  rw [eq_top_iff, ← blockSL_univ, hU]
  refine (blockSL_union_le_sup (x := i₆) ?_ ?_).trans
    (sup_le_sup_right (blockSL_union_le_sup (x := i₆) ?_ ?_) _)
  · simp only [Finset.mem_union, mem_compl_pair_sdiff_pair_iff]
    omega
  · simp only [mem_compl_pair_sdiff_pair_iff]
    omega
  · simp only [mem_compl_pair_sdiff_pair_iff]
    omega
  · simp only [mem_compl_pair_sdiff_pair_iff]
    omega

end Transvections

section NotCommute

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem not_commute_symm_proj_transvection (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    ¬Commute ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))) : L) : G)
      ((e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hjk (1 : K))) : L) : G) := by
  intro h
  apply symm_proj_transvection_ne_one hK e hik
  have hc : Commute (e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hij (1 : K))))
      (e.symm (LinearFlag.proj n K (SpecialLinearGroup.transvection hjk (1 : K)))) :=
    Subtype.ext h
  have h1 : ⁅SpecialLinearGroup.transvection hij (1 : K),
      SpecialLinearGroup.transvection hjk (1 : K)⁆ = SpecialLinearGroup.transvection hik 1 := by
    rw [commutatorElement_def, transvection_mul_transvection_mul_inv_mul_inv hij hjk hik, mul_one]
  rw [← h1, map_commutatorElement, map_commutatorElement,
    commutatorElement_eq_one_iff_commute.2 hc]
  rfl

end NotCommute

end CFSG.SeitzReduction.LinearPilot
