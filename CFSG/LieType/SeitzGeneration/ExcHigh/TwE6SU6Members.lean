module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6SU6Frob

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6

open CFSG.LieType.Chevalley.E6GraphLevi CFSG.Timmesfeld Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem tv_commute_of_disjoint {i j k l : Fin 6} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hli : l ≠ i) (a b : K) : tv i j a * tv k l b = tv k l b * tv i j a := by
  rw [tv_of_ne hij, tv_of_ne hkl]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.single_mul_single_of_ne, ne_eq, hjk, hli, not_false_eq_true, add_zero]
  abel

theorem succ_ne_rev_castSucc (t : Fin 5) :
    t.succ ≠ (Fin.rev t).castSucc ∧ (Fin.rev t).succ ≠ t.castSucc := by
  have ht := t.isLt
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.val_rev] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_castSucc, Fin.val_rev] at h'
    omega

theorem mem_unitarySL_upper_pair (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) (t : Fin 5)
    (ht : t ≠ Fin.rev t) (x : K) :
    tv t.castSucc t.succ x * tv (Fin.rev t).castSucc (Fin.rev t).succ (-σ x) ∈ unitarySL σ := by
  obtain ⟨hjk, hli⟩ := succ_ne_rev_castSucc t
  have hne : t.castSucc ≠ t.succ := Fin.castSucc_lt_succ.ne
  have hne' : (Fin.rev t).castSucc ≠ (Fin.rev t).succ := Fin.castSucc_lt_succ.ne
  rw [mem_unitarySL_iff_unitaryTwist, map_mul, unitaryTwist_tv σ hne,
    unitaryTwist_tv σ hne']
  simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev, map_neg, hσσ, neg_neg]
  exact (tv_commute_of_disjoint hne hne' hjk hli x (-σ x)).symm

theorem mem_unitarySL_lower_pair (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c) (t : Fin 5)
    (ht : t ≠ Fin.rev t) (x : K) :
    tv t.succ t.castSucc x * tv (Fin.rev t).succ (Fin.rev t).castSucc (-σ x) ∈ unitarySL σ := by
  obtain ⟨hjk, hli⟩ := succ_ne_rev_castSucc t
  have hne : t.succ ≠ t.castSucc := Fin.castSucc_lt_succ.ne.symm
  have hne' : (Fin.rev t).succ ≠ (Fin.rev t).castSucc := Fin.castSucc_lt_succ.ne.symm
  rw [mem_unitarySL_iff_unitaryTwist, map_mul, unitaryTwist_tv σ hne,
    unitaryTwist_tv σ hne']
  simp only [Fin.rev_succ, Fin.rev_castSucc, Fin.rev_rev, map_neg, hσσ, neg_neg]
  exact (tv_commute_of_disjoint hne hne' hli.symm hjk.symm x (-σ x)).symm

theorem mem_unitarySL_upper_mid (σ : K →+* K) (x : K) (hx : σ x = -x) :
    tv (2 : Fin 5).castSucc (2 : Fin 5).succ x ∈ unitarySL σ := by
  have hne : (2 : Fin 5).castSucc ≠ (2 : Fin 5).succ := Fin.castSucc_lt_succ.ne
  have e1 : Fin.rev (2 : Fin 5).succ = (2 : Fin 5).castSucc := by decide
  have e2 : Fin.rev (2 : Fin 5).castSucc = (2 : Fin 5).succ := by decide
  rw [mem_unitarySL_iff_unitaryTwist, unitaryTwist_tv σ hne, hx, neg_neg, e1, e2]

theorem mem_unitarySL_lower_mid (σ : K →+* K) (x : K) (hx : σ x = -x) :
    tv (2 : Fin 5).succ (2 : Fin 5).castSucc x ∈ unitarySL σ := by
  have hne : (2 : Fin 5).succ ≠ (2 : Fin 5).castSucc := Fin.castSucc_lt_succ.ne.symm
  have e1 : Fin.rev (2 : Fin 5).castSucc = (2 : Fin 5).succ := by decide
  have e2 : Fin.rev (2 : Fin 5).succ = (2 : Fin 5).castSucc := by decide
  rw [mem_unitarySL_iff_unitaryTwist, unitaryTwist_tv σ hne, hx, neg_neg, e1, e2]

end CFSG.LieType.SeitzGeneration.ExcHigh.TwSU6
