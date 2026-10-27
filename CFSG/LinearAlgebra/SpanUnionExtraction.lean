module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LinearAlgebra

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_fin_indep_span_union {a : V} (ha : a ≠ 0) (v : ι → V) {m : ℕ}
    (hm : Module.finrank K (Submodule.span K ({a} ∪ Set.range v)) = m + 1)
    [FiniteDimensional K (Submodule.span K ({a} ∪ Set.range v))] :
    ∃ b : Set V, a ∈ b ∧ b ⊆ {a} ∪ Set.range v ∧
      Submodule.span K b = Submodule.span K ({a} ∪ Set.range v) ∧
      b.Finite ∧ b.ncard = m + 1 := by
  classical
  let t : Set V := {a} ∪ Set.range v
  obtain ⟨T, hT_sub, -, hT_span, -⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K t
  let T' : Set V := {a} ∪ (T : Set V)
  have hT'_finite : T'.Finite := (Set.finite_singleton a).union T.finite_toSet
  have hs : LinearIndepOn K id ({a} : Set V) := by
    rw [linearIndepOn_singleton_iff]
    exact ha
  have hst : ({a} : Set V) ⊆ T' := Set.subset_union_left
  let b : Set V := hs.extend hst
  have hb_sub : b ⊆ T' := hs.extend_subset hst
  have ha_mem : a ∈ b := hs.subset_extend hst (by simp)
  have hb_sub_t : b ⊆ t := by
    intro x hx
    rcases hb_sub hx with hxa | hxT
    · exact Or.inl hxa
    · exact hT_sub hxT
  have hspan_a_le : Submodule.span K ({a} : Set V) ≤ Submodule.span K t := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.subset_span (Or.inl rfl)
  have hb_span : Submodule.span K b = Submodule.span K t := by
    rw [hs.span_extend_eq_span hst, Submodule.span_union, hT_span]
    exact le_antisymm (sup_le hspan_a_le le_rfl) le_sup_right
  have hb_ind : LinearIndepOn K id b := hs.linearIndepOn_extend hst
  have hb_finite : b.Finite := hT'_finite.subset hb_sub
  haveI : Fintype b := hb_finite.fintype
  have hb_card : Fintype.card b = m + 1 := by
    have h1 : Module.finrank K (Submodule.span K b) = Fintype.card b := by
      rw [finrank_span_set_eq_card hb_ind, ← hb_finite.toFinset_eq_toFinset]
      exact hb_finite.card_toFinset
    rw [hb_span, hm] at h1
    exact h1.symm
  refine ⟨b, ha_mem, hb_sub_t, hb_span, hb_finite, ?_⟩
  rw [← Set.fintypeCard_eq_ncard]
  exact hb_card

theorem exists_fin_span_union_eq_of_indep {a : V} (v : ι → V) {b : Set V} (hbf : b.Finite)
    (ha_mem : a ∈ b) (hb_sub : b ⊆ {a} ∪ Set.range v) {m : ℕ}
    (hcard : b.ncard = m + 1) :
    ∃ s : Fin m → ι, Submodule.span K ({a} ∪ Set.range (v ∘ s)) = Submodule.span K b := by
  classical
  haveI : Fintype b := hbf.fintype
  have hcardF : Fintype.card b = m + 1 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hcard
  let bF : Finset V := hbf.toFinset
  have hbF_card : bF.card = m + 1 := by
    simpa [bF] using hbf.card_toFinset.trans hcardF
  let bNE : Finset V := bF.erase a
  have hbNE_card : bNE.card = m := by
    rw [show bNE = bF.erase a from rfl,
      Finset.card_erase_of_mem (hbf.mem_toFinset.mpr ha_mem), hbF_card]
    omega
  let e : bNE ≃ Fin m := Finset.equivFinOfCardEq hbNE_card
  have hpre : ∀ i : Fin m, ∃ j : ι, v j = ((e.symm i : bNE) : V) := by
    intro i
    have hxNE : ((e.symm i : bNE) : V) ∈ bNE := (e.symm i).2
    have hxNE' : ((e.symm i : bNE) : V) ∈ bF.erase a := by simpa [bNE] using hxNE
    have hx_ne : ((e.symm i : bNE) : V) ≠ a := (Finset.mem_erase.mp hxNE').1
    have hxF : ((e.symm i : bNE) : V) ∈ bF := Finset.mem_of_mem_erase hxNE'
    have hxb : ((e.symm i : bNE) : V) ∈ b := by
      rw [← hbf.mem_toFinset]
      exact hxF
    rcases hb_sub hxb with hxa | ⟨j, hj⟩
    · exact absurd hxa hx_ne
    · exact ⟨j, hj⟩
  choose s hs using hpre
  refine ⟨s, ?_⟩
  have hrange_vs : Set.range (v ∘ s) = (bNE : Set V) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      simpa [Function.comp_apply, hs i] using (e.symm i).2
    · intro hy
      refine ⟨e ⟨y, hy⟩, ?_⟩
      simpa using hs (e ⟨y, hy⟩)
  have hset : ({a} ∪ (bNE : Set V)) = b := by
    have hins : insert a bNE = bF := Finset.insert_erase (hbf.mem_toFinset.mpr ha_mem)
    calc ({a} ∪ (bNE : Set V)) = ((insert a bNE : Finset V) : Set V) := by simp
      _ = (bF : Set V) := by rw [hins]
      _ = b := by simpa [bF] using hbf.coe_toFinset
  rw [hrange_vs, hset]

theorem exists_fin_span_union_eq {a : V} (ha : a ≠ 0) (v : ι → V) {m : ℕ}
    (hm : Module.finrank K (Submodule.span K ({a} ∪ Set.range v)) = m + 1)
    [FiniteDimensional K (Submodule.span K ({a} ∪ Set.range v))] :
    ∃ s : Fin m → ι, Submodule.span K ({a} ∪ Set.range (v ∘ s)) =
      Submodule.span K ({a} ∪ Set.range v) := by
  obtain ⟨b, ha_mem, hb_sub, hb_span, hbf, hcard⟩ :=
    exists_fin_indep_span_union ha v hm
  obtain ⟨s, hs⟩ :=
    exists_fin_span_union_eq_of_indep (K := K) (V := V) (ι := ι) v hbf ha_mem hb_sub hcard
  exact ⟨s, hs.trans hb_span⟩

end CFSG.LinearAlgebra

