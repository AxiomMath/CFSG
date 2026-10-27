module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneIsL2
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

instance finite_tailModel [Finite K] [FiniteDimensional K A] : Finite (TailModel K A r) := by
  haveI : Finite A := Module.finite_of_finite K
  haveI : Finite (((Fin r ⊕ Fin r → K) × A) → ((Fin r ⊕ Fin r → K) × A)) := inferInstance
  exact Finite.of_injective
    (fun f : TailModel K A r => (f : ((Fin r ⊕ Fin r → K) × A) → ((Fin r ⊕ Fin r → K) × A)))
    DFunLike.coe_injective

@[expose] def tailCoeff (g : TailModel K A r) (a b : Fin r) : K :=
  (g (hypVec K A (.inl b))).1 (.inl a)

variable (r qA) in
@[expose] noncomputable def tailLeviDom (i : Fin r) : Subgroup (TailModel K A r) :=
  orthElementaryGroup (quadTail r qA) ⊓
    ⨅ k ∈ (Set.Icc 1 r \ {i.val + 1}),
      MulAction.stabilizer (TailModel K A r) (tailFlag K A r k)

theorem eq_sum_hypVec_of_mem_tailFlag {v : (Fin r ⊕ Fin r → K) × A}
    (hv : v ∈ tailFlag K A r r) :
    v = ∑ j : Fin r, v.1 (.inl j) • hypVec K A (.inl j) := by
  obtain ⟨h1, h2⟩ := mem_tailFlag_iff.1 hv
  obtain ⟨h1a, _⟩ := mem_flag_iff_coord.1 h1
  have hsum : v.1 = ∑ j : Fin r,
      v.1 (.inl j) • (Pi.single (Sum.inl j) (1 : K) : Fin r ⊕ Fin r → K) := by
    ext c
    rcases c with c | c
    · simp [Finset.sum_apply, Pi.single_apply]
    · simp [Finset.sum_apply, h1a c]
  refine Prod.ext ?_ ?_
  · simpa [hypVec, Prod.fst_sum, Prod.smul_fst] using hsum
  · simp [hypVec, h2, Prod.snd_sum, Prod.smul_snd]

theorem mem_tailLeviDom {i : Fin r} {g : TailModel K A r} :
    g ∈ tailLeviDom r qA i ↔ g ∈ orthElementaryGroup (quadTail r qA) ∧
      ∀ k, 1 ≤ k → k ≤ r → k ≠ i.val + 1 →
        (tailFlag K A r k).map (g : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r k := by
  simp only [tailLeviDom, Subgroup.mem_inf, Subgroup.mem_iInf, Set.mem_diff, Set.mem_Icc,
    Set.mem_singleton_iff, and_imp, Submodule.mem_stabilizer_submodule_iff_map_eq]
  rfl

theorem tailLeviDom_le (i : Fin r) : tailLeviDom r qA i ≤ orthElementaryGroup (quadTail r qA) :=
  inf_le_left

theorem tailBorel_le_tailLeviDom (i : Fin r) : tailBorel r qA ≤ tailLeviDom r qA i := by
  intro g hg
  rw [mem_tailBorel] at hg
  rw [mem_tailLeviDom]
  exact ⟨hg.1, fun k h1 h2 _ => hg.2 k h1 h2⟩

theorem tailCoeff_eq_zero_of_mem_tailLeviDom {i : Fin r} (hi : i.val + 1 < r)
    {g : TailModel K A r} (hg : g ∈ tailLeviDom r qA i) {a b : Fin r} (hba : b.val < a.val)
    (hne : ¬ (b.val = i.val ∧ a.val = i.val + 1)) : tailCoeff g a b = 0 := by
  obtain ⟨k, hk1, hkr, hkne, hbk, hka⟩ : ∃ k : ℕ, 1 ≤ k ∧ k ≤ r ∧ k ≠ i.val + 1 ∧
      b.val < k ∧ k ≤ a.val := by
    have ha := a.isLt
    by_cases hbi : b.val = i.val
    · have hane : a.val ≠ i.val + 1 := fun h => hne ⟨hbi, h⟩
      exact ⟨i.val + 2, by omega, by omega, by omega, by omega, by omega⟩
    · exact ⟨b.val + 1, by omega, by omega, by omega, by omega, by omega⟩
  have hfix := (mem_tailLeviDom.1 hg).2 k hk1 hkr hkne
  have hmemF : hypVec K A (.inl b) ∈ tailFlag K A r k :=
    Submodule.subset_span ⟨b, hbk, rfl⟩
  have hmap : g (hypVec K A (.inl b)) ∈ tailFlag K A r k := by
    rw [← hfix]
    exact ⟨hypVec K A (.inl b), hmemF, rfl⟩
  have hcoord : (g (hypVec K A (.inl b))).1 (.inl a) = 0 := by
    have h1 := (mem_tailFlag_iff.1 hmap).1
    exact (mem_flag_iff_coord.1 h1).2 a hka
  exact hcoord

theorem tailLeviDom_apply_hypVec_inl {i : Fin r} (hi : i.val + 1 < r) {g : TailModel K A r}
    (hg : g ∈ tailLeviDom r qA i) (j : Fin r) :
    g (hypVec K A (.inl j)) = ∑ k : Fin r, tailCoeff g k j • hypVec K A (.inl k) := by
  have hfix := (mem_tailLeviDom.1 hg).2 r (by omega) le_rfl (by omega)
  have hmemF : hypVec K A (.inl j) ∈ tailFlag K A r r :=
    Submodule.subset_span ⟨j, j.isLt, rfl⟩
  have hmap : g (hypVec K A (.inl j)) ∈ tailFlag K A r r := by
    rw [← hfix]
    exact ⟨hypVec K A (.inl j), hmemF, rfl⟩
  rw [eq_sum_hypVec_of_mem_tailFlag hmap]
  rfl

theorem tailCoeff_one (a b : Fin r) :
    tailCoeff (1 : TailModel K A r) a b = if a = b then 1 else 0 := by
  simp [tailCoeff, hypVec, Pi.single_apply, Sum.inl.injEq]

theorem tailCoeff_mul {i : Fin r} (hi : i.val + 1 < r) {g h : TailModel K A r}
    (hh : h ∈ tailLeviDom r qA i) (a b : Fin r) :
    tailCoeff (g * h) a b = ∑ k : Fin r, tailCoeff g a k * tailCoeff h k b := by
  have h1 : (g * h) (hypVec K A (.inl b)) =
      ∑ k : Fin r, tailCoeff h k b • g (hypVec K A (.inl k)) := by
    rw [LinearEquiv.mul_apply, tailLeviDom_apply_hypVec_inl (qA := qA) hi hh b]
    simp only [map_sum, map_smul]
  show ((g * h) (hypVec K A (.inl b))).1 (.inl a) =
    ∑ k : Fin r, tailCoeff g a k * tailCoeff h k b
  rw [h1]
  simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
