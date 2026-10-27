module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowPieces

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open scoped commutatorElement

section Order3

variable {n : ℕ} {F : Type*} [Field F]

@[expose] def Order3Pattern (a b : Fin n) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ k, k ≠ a → k ≠ b → M k a = 0 ∧ M k b = 0 ∧ M a k = 0 ∧ M b k = 0) ∧
    M a b = M b a ∧ M a a = M b b + M a b

theorem order3Pattern_of_mul_comm {M : Matrix (Fin n) (Fin n) F} {a b : Fin n} (hab : a ≠ b)
    (h : M * (single a b (1 : F) + single b a 1 + single a a 1) =
      (single a b 1 + single b a 1 + single a a 1) * M) : Order3Pattern a b M := by
  have e : ∀ k l, (M * single a b (1 : F)) k l + (M * single b a (1 : F)) k l +
      (M * single a a (1 : F)) k l =
      (single a b (1 : F) * M) k l + (single b a (1 : F) * M) k l +
        (single a a (1 : F) * M) k l := by
    intro k l
    have := congrFun (congrFun h k) l
    simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply] using this
  refine ⟨fun k hka hkb => ?_, ?_, ?_⟩
  · have e1 := e k b
    have e2 := e k a
    have e3 := e b k
    have e4 := e a k
    simp [hab, Ne.symm hab, hka, hkb] at e1 e2 e3 e4
    refine ⟨e1, ?_, e3.symm, ?_⟩
    · linear_combination e2 - e1
    · linear_combination -e4 + e3
  · have e5 := e a a
    simp [hab] at e5
    linear_combination e5
  · have e6 := e a b
    simp [hab, Ne.symm hab] at e6
    linear_combination e6

theorem order3Pattern_of_commute {A : SpecialLinearGroup (Fin n) F} {a b : Fin n} (hab : a ≠ b)
    (h : A * (SpecialLinearGroup.transvection hab 1 *
        SpecialLinearGroup.transvection (Ne.symm hab) 1) =
      (SpecialLinearGroup.transvection hab 1 *
        SpecialLinearGroup.transvection (Ne.symm hab) 1) * A) :
    Order3Pattern a b (A : Matrix (Fin n) (Fin n) F) := by
  have h' : (A : Matrix (Fin n) (Fin n) F) * ((1 + single a b (1 : F)) * (1 + single b a 1)) =
      ((1 + single a b (1 : F)) * (1 + single b a 1)) * (A : Matrix (Fin n) (Fin n) F) :=
    congrArg Subtype.val h
  have hy : (1 + single a b (1 : F)) * (1 + single b a 1) =
      1 + (single a b 1 + single b a 1 + single a a 1) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, single_mul_single_same, mul_one]
    abel
  rw [hy, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h'
  exact order3Pattern_of_mul_comm hab (add_left_cancel h')

theorem mul_apply_of_order3Pattern {M M' : Matrix (Fin n) (Fin n) F} {a b : Fin n} (hab : a ≠ b)
    (hM : Order3Pattern a b M) {i : Fin n} (hi : i = a ∨ i = b) (j : Fin n) :
    (M * M') i j = M i a * M' a j + M i b * M' b j := by
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · intro c _ hc
    rcases hi with rfl | rfl
    · rw [(hM.1 c hc.1 hc.2).2.2.1, zero_mul]
    · rw [(hM.1 c hc.1 hc.2).2.2.2, zero_mul]
  · exact fun h => absurd (Finset.mem_univ a) h
  · exact fun h => absurd (Finset.mem_univ b) h

theorem mul_apply_comm_of_order3Pattern {M M' : Matrix (Fin n) (Fin n) F} {a b : Fin n}
    (hab : a ≠ b) (hM : Order3Pattern a b M) (hM' : Order3Pattern a b M') {i j : Fin n}
    (hi : i = a ∨ i = b) (hj : j = a ∨ j = b) : (M * M') i j = (M' * M) i j := by
  rw [mul_apply_of_order3Pattern hab hM hi, mul_apply_of_order3Pattern hab hM' hi]
  obtain ⟨-, h1, h2⟩ := hM
  obtain ⟨-, h1', h2'⟩ := hM'
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rw [← h1, ← h1']; ring
  · rw [h2, h2']; ring
  · rw [← h1, ← h1', h2, h2']; ring
  · rw [← h1, ← h1']; ring

theorem commutator_mem_blockSpecialLinear_compl_of_order3
    {Q : Subgroup (SpecialLinearGroup (Fin n) F)} {a b : Fin n} (hab : a ≠ b)
    (hQ : ∀ A ∈ Q, Order3Pattern a b (A : Matrix (Fin n) (Fin n) F))
    {x y : SpecialLinearGroup (Fin n) F} (hx : x ∈ Q) (hy : y ∈ Q) :
    ⁅x, y⁆ ∈ blockSpecialLinear (K := F) ({a, b} : Finset (Fin n))ᶜ := by
  have hxy : x * y ∈ Q := Q.mul_mem hx hy
  have hyx : y * x ∈ Q := Q.mul_mem hy hx
  have hc : ⁅x, y⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem hxy (Q.inv_mem hx)) (Q.inv_mem hy)
  have hcomm : ⁅x, y⁆ = (x * y) * (x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  have hone : (y * x) * (x⁻¹ * y⁻¹) = 1 := by group
  have hblock : ∀ i j : Fin n, (i = a ∨ i = b) → (j = a ∨ j = b) →
      ((⁅x, y⁆ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
        (1 : Matrix (Fin n) (Fin n) F) i j := by
    intro i j hi _
    have h1 : ∀ k, (k = a ∨ k = b) →
        ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i k =
          ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i k :=
      fun k hk => by
        rw [coe_mul_specialLinear, coe_mul_specialLinear]
        exact mul_apply_comm_of_order3Pattern hab (hQ _ hx) (hQ _ hy) hi hk
    calc ((⁅x, y⁆ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
        = ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i a *
            ((x⁻¹ * y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a j +
          ((x * y : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i b *
            ((x⁻¹ * y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) b j := by
          rw [hcomm, coe_mul_specialLinear (x * y), mul_apply_of_order3Pattern hab (hQ _ hxy) hi]
      _ = ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i a *
            ((x⁻¹ * y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) a j +
          ((y * x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i b *
            ((x⁻¹ * y⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) b j := by
          rw [h1 a (Or.inl rfl), h1 b (Or.inr rfl)]
      _ = ((y * x * (x⁻¹ * y⁻¹) : SpecialLinearGroup (Fin n) F) :
            Matrix (Fin n) (Fin n) F) i j := by
          rw [coe_mul_specialLinear (y * x), mul_apply_of_order3Pattern hab (hQ _ hyx) hi]
      _ = (1 : Matrix (Fin n) (Fin n) F) i j := by rw [hone, coe_one_specialLinear]
  intro i j hij
  have hmem : ∀ k : Fin n, k ∉ ({a, b} : Finset (Fin n))ᶜ → k = a ∨ k = b := by
    intro k hk
    simpa only [Finset.mem_compl, not_not, Finset.mem_insert, Finset.mem_singleton] using hk
  rcases hij with hi | hj
  · have hi := hmem i hi
    by_cases hj : j = a ∨ j = b
    · exact hblock i j hi hj
    · obtain ⟨hja, hjb⟩ := not_or.1 hj
      have hij : i ≠ j := by
        rintro rfl
        exact hj hi
      rw [Matrix.one_apply_ne hij]
      rcases hi with rfl | rfl
      · exact ((hQ _ hc).1 j hja hjb).2.2.1
      · exact ((hQ _ hc).1 j hja hjb).2.2.2
  · have hj := hmem j hj
    by_cases hi : i = a ∨ i = b
    · exact hblock i j hi hj
    · obtain ⟨hia, hib⟩ := not_or.1 hi
      have hij : i ≠ j := by
        rintro rfl
        exact hi hj
      rw [Matrix.one_apply_ne hij]
      rcases hj with rfl | rfl
      · exact ((hQ _ hc).1 i hia hib).1
      · exact ((hQ _ hc).1 i hia hib).2.1

end Order3

section Bound

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {K : Type*} [Field K]
  {F : Type*} [Field F] [Finite F]

@[expose] noncomputable def order3Elt (K : Type*) [Field K] {a b : Fin n} (hab : a ≠ b) :
    LinearFlag.projectiveSL n K :=
  LinearFlag.proj n K (SpecialLinearGroup.transvection hab (1 : K) *
    SpecialLinearGroup.transvection (Ne.symm hab) 1)

theorem order3Elt_mem_rootSL2 {a b : Fin n} (hab : a ≠ b) :
    order3Elt K hab ∈ rootSL2 (K := K) a b :=
  proj_mem_blockSL ((blockSpecialLinear _).mul_mem
    (transvection_mem_blockSpecialLinear hab (by simp) (by simp) 1)
    (transvection_mem_blockSpecialLinear (Ne.symm hab) (by simp) (by simp) 1))

omit [Finite G] [Finite F] in
theorem map_le_centralizer_map_of_disjoint {N A B : Finset (Fin n)}
    (Φ : blockSpecialLinear (K := F) N →* G) (hAB : Disjoint A B) :
    ((blockSpecialLinear (K := F) A).subgroupOf (blockSpecialLinear N)).map Φ ≤
      centralizer (((blockSpecialLinear (K := F) B).subgroupOf (blockSpecialLinear N)).map Φ :
        Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (commute_blockSpecialLinear_of_disjoint hAB (mem_subgroupOf.1 hx)
    (mem_subgroupOf.1 hy)).symm.eq

end Bound

end CFSG.SeitzReduction.LinearPilot
