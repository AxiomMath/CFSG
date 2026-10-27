module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.GroupTheory.ThreeTranspositions

theorem exists_forall_form_eq {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite ι] (b : LinearMap.BilinForm K V)
    (hcomm : ∀ u w, b u w = b w u) (hnd : ∀ u, (∀ w, b u w = 0) → u = 0)
    (v : ι → V) (hv : LinearIndependent K v) (c : ι → K) :
    ∃ w : V, ∀ i, b (v i) w = c i := by
  have hnd' : b.Nondegenerate :=
    ⟨hnd, fun w hw => hnd w fun u => by rw [← hcomm u w]; exact hw u⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hv).constr K c)
  refine ⟨(b.toDual hnd').symm g, fun i => ?_⟩
  rw [hcomm (v i)]
  rw [LinearMap.BilinForm.apply_toDual_symm_apply]
  have h1 := LinearMap.congr_fun hg (Module.Basis.span hv i)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coe_span_apply,
    Module.Basis.constr_basis] at h1
  exact h1

theorem linearIndependent_pair_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    LinearIndependent (ZMod 2) ![x, y] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 s with hs | hs
  · rcases h01 t with ht | ht
    · exact ⟨hs, ht⟩
    · exact absurd (by simpa [hs, ht] using hst) hy
  · rcases h01 t with ht | ht
    · exact absurd (by simpa [hs, ht] using hst) hx
    · exact absurd ((eq_neg_of_add_eq_zero_left (by simpa [hs, ht] using hst)).trans
        (ZModModule.neg_eq_self y)) hxy

theorem linearIndependent_triple_zmod_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : x + y + z ≠ 0) : LinearIndependent (ZMod 2) ![x, y, z] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  rw [Fin.sum_univ_three] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hc
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 (c 0) with h0 | h0 <;>
    rcases h01 (c 1) with h1 | h1 <;>
    rcases h01 (c 2) with h2 | h2 <;>
    rw [h0, h1, h2] at hc <;>
    simp only [zero_smul, one_smul, zero_add, add_zero] at hc
  · fin_cases i <;> simp [h0, h1, h2]
  · exact absurd hc hz
  · exact absurd hc hy
  · exact absurd ((eq_neg_of_add_eq_zero_left hc).trans (ZModModule.neg_eq_self z)) hyz
  · exact absurd hc hx
  · exact absurd ((eq_neg_of_add_eq_zero_left hc).trans (ZModModule.neg_eq_self z)) hxz
  · exact absurd ((eq_neg_of_add_eq_zero_left hc).trans (ZModModule.neg_eq_self y)) hxy
  · exact absurd hc hs

theorem exists_form_eq_pair {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (b : LinearMap.BilinForm (ZMod 2) V)
    (hcomm : ∀ u w, b u w = b w u) (hnd : ∀ u, (∀ w, b u w = 0) → u = 0)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) (c₁ c₂ : ZMod 2) :
    ∃ w : V, b x w = c₁ ∧ b y w = c₂ := by
  obtain ⟨w, hw⟩ := exists_forall_form_eq b hcomm hnd ![x, y]
    (linearIndependent_pair_zmod_two hx hy hxy) ![c₁, c₂]
  exact ⟨w, by simpa using hw 0, by simpa using hw 1⟩

theorem exists_form_eq_triple {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (b : LinearMap.BilinForm (ZMod 2) V)
    (hcomm : ∀ u w, b u w = b w u) (hnd : ∀ u, (∀ w, b u w = 0) → u = 0)
    {x y z : V} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hs : x + y + z ≠ 0) (c₁ c₂ c₃ : ZMod 2) :
    ∃ w : V, b x w = c₁ ∧ b y w = c₂ ∧ b z w = c₃ := by
  obtain ⟨w, hw⟩ := exists_forall_form_eq b hcomm hnd ![x, y, z]
    (linearIndependent_triple_zmod_two hx hy hz hxy hxz hyz hs) ![c₁, c₂, c₃]
  exact ⟨w, by simpa using hw 0, by simpa using hw 1, by simpa using hw 2⟩

end CFSG.GroupTheory.ThreeTranspositions
