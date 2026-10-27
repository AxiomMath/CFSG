module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFE8CentModelAux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {ε : ZMod 3}

private theorem exists_sep (k : Fin 4) (y : FFE8Idx) (hy : y ≠ Sum.inr k) :
    ∃ m : Fin 4, m ≠ k ∧ y ∉ ffE8Hat {k, m} := by
  revert k y
  decide

theorem ffOutFFE8CentModel_offdiag (fr : PFrame Q FFE8Idx (ffE8Norm ε)) {γ : V ≃ₗ[ZMod 3] V}
    (h : ∀ k m : Fin 4, k ≠ m → ∀ v,
      ((fr.signChange (ffE8Hat {k, m}) : OGroup Q) : V ≃ₗ[ZMod 3] V) (γ v) =
        γ (((fr.signChange (ffE8Hat {k, m}) : OGroup Q) : V ≃ₗ[ZMod 3] V) v))
    {i j : FFE8Idx} (hij : i ≠ j) (hinr : (∃ k, i = Sum.inr k) ∨ (∃ l, j = Sum.inr l)) :
    fr.b.repr (γ (fr.b j)) i = 0 := by
  rcases hinr with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · obtain ⟨m, hmk, hj⟩ := exists_sep k j (Ne.symm hij)
    have h1 := ffOutFFE8CentModel_repr_comm fr (ffE8Hat {k, m}) (h k m (Ne.symm hmk)) (Sum.inr k) j
    have hi : (Sum.inr k : FFE8Idx) ∈ ffE8Hat {k, m} := by simp [ffE8Hat]
    rw [if_pos hi, if_neg hj] at h1
    revert h1
    generalize fr.b.repr (γ (fr.b j)) (Sum.inr k) = x
    revert x
    decide
  · obtain ⟨m, hml, hi⟩ := exists_sep l i hij
    have h1 := ffOutFFE8CentModel_repr_comm fr (ffE8Hat {l, m}) (h l m (Ne.symm hml)) i (Sum.inr l)
    have hj : (Sum.inr l : FFE8Idx) ∈ ffE8Hat {l, m} := by simp [ffE8Hat]
    rw [if_pos hj, if_neg hi] at h1
    revert h1
    generalize fr.b.repr (γ (fr.b (Sum.inr l))) i = x
    revert x
    decide

private theorem col_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ι → ZMod 3}
    (fr : PFrame Q ι c) (γ : V ≃ₗ[ZMod 3] V) (j : ι)
    (h : ∀ i, i ≠ j → fr.b.repr (γ (fr.b j)) i = 0) :
    γ (fr.b j) = fr.b.repr (γ (fr.b j)) j • fr.b j := by
  apply fr.b.ext_elem
  intro i
  by_cases hij : i = j
  · subst hij
    simp [Module.Basis.repr_self]
  · rw [h i hij]
    simp [Module.Basis.repr_self, Finsupp.single_apply, Ne.symm hij]

private theorem sq_eq_unit {x m : ZMod 3} (hm : m = 1 ∨ m = -1) (h : x ^ 2 = m) : m = 1 := by
  revert h hm
  revert x m
  decide

private theorem cancel_norm {ε x m : ZMod 3} (hε : ε = 1 ∨ ε = -1) (h : ε * x ^ 2 = m * ε) :
    x ^ 2 = m := by
  revert h hε
  revert ε x m
  decide

private theorem hyp_plus {x y : ZMod 3} (h : x ^ 2 - y ^ 2 = 1) : y = 0 ∧ x * x = 1 := by
  revert h
  revert x y
  decide

private theorem hyp_minus {x y : ZMod 3} (h : x ^ 2 - y ^ 2 = -1) : x = 0 ∧ y * y = 1 := by
  revert h
  revert x y
  decide

theorem ffOutFFE8CentModel_diag (hε : ε = 1 ∨ ε = -1) (fr : PFrame Q FFE8Idx (ffE8Norm ε))
    {γ : V ≃ₗ[ZMod 3] V} {μ : (ZMod 3)ˣ} (hγ : IsSimilitude Q γ μ)
    (hoff : ∀ i j : FFE8Idx, i ≠ j → ((∃ k, i = Sum.inr k) ∨ (∃ l, j = Sum.inr l)) →
      fr.b.repr (γ (fr.b j)) i = 0) :
    ∃ g : OGroup Q, (g : V ≃ₗ[ZMod 3] V) = γ ∧ ∃ K : Finset FFE8Idx, g = fr.signChange K := by
  have hnorm : ∀ j, ∑ i, ffE8Norm ε i * (fr.b.repr (γ (fr.b j)) i) ^ 2 =
      (μ : ZMod 3) * ffE8Norm ε j := by
    intro j
    rw [← fr.map_eq, hγ, fr.norm]
  have hinr : ∀ l : Fin 4, fr.b.repr (γ (fr.b (Sum.inr l))) (Sum.inr l) ^ 2 = (μ : ZMod 3) := by
    intro l
    have h1 := hnorm (Sum.inr l)
    rw [Finset.sum_eq_single (Sum.inr l)] at h1
    · exact cancel_norm hε h1
    · intro i _ hi
      rw [hoff i (Sum.inr l) hi (Or.inr ⟨l, rfl⟩)]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hμ : (μ : ZMod 3) = 1 :=
    sq_eq_unit (by rcases aux_unit_eq_one_or_neg_one μ with h | h <;> simp [h])
      (hinr 0)
  have hμ' : μ = 1 := Units.ext hμ
  subst hμ'
  have hg : γ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := isSimilitude_one_iff.mp hγ
  have hsplit : ∀ j : FFE8Idx, (∀ k : Fin 4, fr.b.repr (γ (fr.b j)) (Sum.inr k) = 0) →
      (fr.b.repr (γ (fr.b j)) (Sum.inl 0)) ^ 2 - (fr.b.repr (γ (fr.b j)) (Sum.inl 1)) ^ 2 =
        ffE8Norm ε j := by
    intro j hj
    have h1 := hnorm j
    rw [Fintype.sum_sum_type, Fin.sum_univ_two] at h1
    simp only [hj, ffE8Norm, Sum.elim_inl, Sum.elim_inr, Units.val_one, one_mul] at h1 ⊢
    simp at h1
    linear_combination h1
  have hzero : ∀ j : FFE8Idx, ∀ k : Fin 4, j ≠ Sum.inr k → fr.b.repr (γ (fr.b j)) (Sum.inr k) = 0 :=
    fun j k hjk => hoff (Sum.inr k) j (Ne.symm hjk) (Or.inl ⟨k, rfl⟩)
  refine ⟨⟨γ, hg⟩, rfl, ?_⟩
  apply fg_exists_signChange_eq fr
  intro o
  rcases o with p | l
  · fin_cases p
    · have h1 := hsplit (Sum.inl 0) (fun k => hzero _ k (by simp))
      have h2 : ffE8Norm ε (Sum.inl 0) = 1 := rfl
      rw [h2] at h1
      obtain ⟨hy, hx⟩ := hyp_plus h1
      refine ⟨fr.b.repr (γ (fr.b (Sum.inl 0))) (Sum.inl 0), hx, ?_⟩
      apply col_eq fr γ (Sum.inl 0)
      intro i hi
      rcases i with q | k
      · fin_cases q
        · exact absurd rfl hi
        · exact hy
      · exact hzero _ k (by simp)
    · have h1 := hsplit (Sum.inl 1) (fun k => hzero _ k (by simp))
      have h2 : ffE8Norm ε (Sum.inl 1) = -1 := rfl
      rw [h2] at h1
      obtain ⟨hx, hy⟩ := hyp_minus h1
      refine ⟨fr.b.repr (γ (fr.b (Sum.inl 1))) (Sum.inl 1), hy, ?_⟩
      apply col_eq fr γ (Sum.inl 1)
      intro i hi
      rcases i with q | k
      · fin_cases q
        · exact hx
        · exact absurd rfl hi
      · exact hzero _ k (by simp)
  · refine ⟨fr.b.repr (γ (fr.b (Sum.inr l))) (Sum.inr l), ?_, ?_⟩
    · have h1 := hinr l
      rw [Units.val_one] at h1
      rw [← pow_two]
      exact h1
    · exact col_eq fr γ _ (fun i hi => hoff i (Sum.inr l) hi (Or.inr ⟨l, rfl⟩))


end CFSG.OddStandard.SmallF3.Omega
