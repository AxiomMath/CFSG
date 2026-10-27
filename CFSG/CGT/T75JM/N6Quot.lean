module

public import CFSG.CGT.T75JM.N6Basic
public import CFSG.CGT.T75JM.N6Words
public import CFSG.CGT.T75JM.N6Class

public section

namespace CFSG.CGT.T75JM

variable {G : Type*} [Group G] {T : Subgroup G}

instance normal_subgroupOf_normalizer' (T : Subgroup G) :
    (T.subgroupOf (Subgroup.normalizer (T : Set G))).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl

abbrev NQ (T : Subgroup G) : Type _ :=
  ↥(Subgroup.normalizer (T : Set G)) ⧸ T.subgroupOf (Subgroup.normalizer (T : Set G))

section Cols

variable (c : Coords T)

@[expose] noncomputable def colsQ (q : NQ T) : Cols := colsOf c (Quotient.out q)

theorem colsQ_mk (g : Subgroup.normalizer (T : Set G)) :
    colsQ c (QuotientGroup.mk g) = colsOf c g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (T.subgroupOf (Subgroup.normalizer (T : Set G))) g
  have h1 : (h : Subgroup.normalizer (T : Set G)) ∈
      T.subgroupOf (Subgroup.normalizer (T : Set G)) := h.2
  have h2 : ((h : Subgroup.normalizer (T : Set G)) : G) ∈ T := h1
  show colsOf c (Quotient.out (QuotientGroup.mk g)) = _
  rw [show (Quotient.out (QuotientGroup.mk g : NQ T)) = (QuotientGroup.mk g : NQ T).out from rfl,
    hh, colsOf_mul, colsOf_of_mem c _ h2]
  unfold compC
  congr 1
  · exact applyC_basis (colsOf c g) 0
  · exact applyC_basis (colsOf c g) 1
  · exact applyC_basis (colsOf c g) 2
  · exact applyC_basis (colsOf c g) 3

theorem colsQ_mul (a b : NQ T) : colsQ c (a * b) = compC (colsQ c a) (colsQ c b) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, colsQ_mk, colsQ_mk, colsQ_mk, colsOf_mul]

theorem colsQ_one : colsQ c (1 : NQ T) = idC := by
  rw [← QuotientGroup.mk_one, colsQ_mk, colsOf_one]

theorem colsQ_pow (a : NQ T) (n : ℕ) : colsQ c (a ^ n) = powC (colsQ c a) n := by
  induction n with
  | zero => simpa [powC] using colsQ_one c
  | succ n ih => rw [pow_succ', colsQ_mul, ih]; rfl

theorem colsQ_evalG (a b : NQ T) (w : List ℕ) :
    colsQ c (evalG a b w) = evalC (colsQ c a) (colsQ c b) w := by
  induction w with
  | nil => simpa [evalG, evalC] using colsQ_one c
  | cons l w ih =>
    simp only [evalG, evalC, colsQ_mul, ih]
    by_cases hl : l = 0 <;> simp [hl]

theorem eq_one_of_colsQ (hC : Subgroup.centralizer (T : Set G) = T) (q : NQ T)
    (h : colsQ c q = idC) : q = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [colsQ_mk] at h
  rw [QuotientGroup.eq_one_iff]
  show ((g : Subgroup.normalizer (T : Set G)) : G) ∈ T
  have hg : ((g : Subgroup.normalizer (T : Set G)) : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (commute_of_colsOf c g h ⟨t, ht⟩).symm
  rwa [hC] at hg

end Cols

end CFSG.CGT.T75JM
