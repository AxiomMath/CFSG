module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Submodule Module

namespace CFSG.HardMathSupport.Kantor79

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

@[expose] def commutatorSpace (H : Subgroup (E ≃ₗ[K] E)) : Submodule K E :=
  Submodule.span K {w : E | ∃ h ∈ H, ∃ v : E, w = h v - v}

@[expose] noncomputable def movedSpace (x : E ≃ₗ[K] E) : Submodule K E :=
  LinearMap.range ((x : E →ₗ[K] E) - 1)

theorem movedSpace_le_commutatorSpace {H : Subgroup (E ≃ₗ[K] E)} {x : E ≃ₗ[K] E} (hx : x ∈ H) :
    movedSpace x ≤ commutatorSpace H := by
  rintro w ⟨v, rfl⟩
  exact Submodule.subset_span ⟨x, hx, v, rfl⟩

section FiniteDimensional

variable [FiniteDimensional K E]

private def trivialModulo (D : Submodule K E) : Subgroup (E ≃ₗ[K] E) where
  carrier := {g | (∀ v : E, g v - v ∈ D) ∧ ∀ d ∈ D, g d ∈ D}
  one_mem' := by
    refine ⟨fun v => ?_, fun d hd => ?_⟩
    · simp
    · simpa using hd
  mul_mem' := by
    rintro g k ⟨hg1, hg2⟩ ⟨hk1, hk2⟩
    refine ⟨fun v => ?_, fun d hd => ?_⟩
    · have h1 : g (k v) - k v ∈ D := hg1 (k v)
      have h2 : k v - v ∈ D := hk1 v
      have h3 : (g * k) v - v = (g (k v) - k v) + (k v - v) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [h3]
      exact D.add_mem h1 h2
    · exact hg2 (k d) (hk2 d hd)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hsurj : ∀ d ∈ D, ∃ e ∈ D, g e = d := by
      intro d hd
      let φ : D →ₗ[K] D :=
        { toFun := fun e => ⟨g (e : E), hg2 (e : E) e.2⟩
          map_add' := by
            intro e f
            ext
            simp
          map_smul' := by
            intro c e
            ext
            simp }
      have hφinj : Function.Injective φ := by
        intro e f h
        have h' : g (e : E) = g (f : E) := congrArg Subtype.val h
        exact Subtype.ext (g.injective h')
      have hφsurj : Function.Surjective φ := by
        have hrange : LinearMap.range φ = ⊤ := by
          apply Submodule.eq_top_of_finrank_eq
          rw [LinearMap.finrank_range_of_inj hφinj]
        exact LinearMap.range_eq_top.mp hrange
      obtain ⟨e, he⟩ := hφsurj ⟨d, hd⟩
      exact ⟨(e : E), e.2, congrArg Subtype.val he⟩
    have hg2inv : ∀ d ∈ D, g⁻¹ d ∈ D := by
      intro d hd
      obtain ⟨e, heD, he⟩ := hsurj d hd
      have : g⁻¹ d = e := by
        rw [← he]
        simp
      rw [this]
      exact heD
    refine ⟨fun v => ?_, hg2inv⟩
    have hvd : v - g v ∈ D := by
      have h := hg1 v
      have hneg : -(g v - v) ∈ D := D.neg_mem h
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    have heq : g⁻¹ v - v = g⁻¹ (v - g v) := by
      rw [map_sub]
      simp
    rw [heq]
    exact hg2inv (v - g v) hvd

theorem commutatorSpace_closure_eq_iSup_movedSpace {ι : Type*} (x : ι → E ≃ₗ[K] E) :
    commutatorSpace (Subgroup.closure (Set.range x)) = ⨆ i, movedSpace (x i) := by
  set D : Submodule K E := ⨆ i, movedSpace (x i)
  have hmem : ∀ i, x i ∈ trivialModulo D := by
    intro i
    refine ⟨fun v => ?_, fun d hd => ?_⟩
    · exact Submodule.mem_iSup_of_mem i ⟨v, rfl⟩
    · have h1 : (x i : E →ₗ[K] E) d - d ∈ D := Submodule.mem_iSup_of_mem i ⟨d, rfl⟩
      have h2 : d + ((x i : E →ₗ[K] E) d - d) ∈ D := D.add_mem hd h1
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2
  have hcl : Subgroup.closure (Set.range x) ≤ trivialModulo D :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  refine le_antisymm ?_ (iSup_le fun i => movedSpace_le_commutatorSpace (Subgroup.subset_closure ⟨i, rfl⟩))
  rw [commutatorSpace, Submodule.span_le]
  rintro w ⟨h, hh, v, rfl⟩
  exact (hcl hh).1 v

theorem finrank_span_pair_le_two (a b : E) :
    finrank K ↥(Submodule.span K ({a, b} : Set E)) ≤ 2 := by
  have hEq : Submodule.span K ({a, b} : Set E) =
      Submodule.span K ({a} : Set E) ⊔ Submodule.span K ({b} : Set E) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.mem_sup_left (Submodule.subset_span (by simp))
      · exact Submodule.mem_sup_right (Submodule.subset_span (by simp))
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span (by simp)
    · rw [Submodule.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Submodule.subset_span (by simp)
  rw [hEq]
  have h1 : finrank K ↥(Submodule.span K ({a} : Set E)) ≤ 1 := by
    have := finrank_span_le_card (R := K) ({a} : Set E)
    simpa using this
  have h2 : finrank K ↥(Submodule.span K ({b} : Set E)) ≤ 1 := by
    have := finrank_span_le_card (R := K) ({b} : Set E)
    simpa using this
  have hsup : finrank K ↥(Submodule.span K ({a} : Set E) ⊔ Submodule.span K ({b} : Set E)) ≤
      finrank K ↥(Submodule.span K ({a} : Set E)) +
        finrank K ↥(Submodule.span K ({b} : Set E)) :=
    Submodule.finrank_add_le_finrank_add_finrank _ _
  omega

theorem finrank_iSup_le_sum {ι : Type*} [Fintype ι] (M : ι → Submodule K E) :
    finrank K ↥(⨆ i, M i) ≤ ∑ i, finrank K ↥(M i) := by
  classical
  have hsup : (⨆ i, M i) = Finset.univ.sup (α := Submodule K E) M := by
    rw [Finset.sup_eq_iSup]
    simp
  rw [hsup]
  have hfin : ∀ s : Finset ι,
      finrank K ↥(s.sup (α := Submodule K E) M) ≤ ∑ i ∈ s, finrank K ↥(M i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.sum_insert ha]
      have h1 : finrank K ↥(M a ⊔ s.sup (α := Submodule K E) M) ≤
          finrank K ↥(M a) + finrank K ↥(s.sup (α := Submodule K E) M) :=
        Submodule.finrank_add_le_finrank_add_finrank (M a) _
      omega
  simpa using hfin Finset.univ

theorem finrank_commutatorSpace_le {ι : Type*} [Fintype ι] (x : ι → E ≃ₗ[K] E) {r : ℕ}
    (hr : ∀ i, finrank K ↥(movedSpace (x i)) ≤ r) :
    finrank K ↥(commutatorSpace (Subgroup.closure (Set.range x))) ≤ Fintype.card ι * r := by
  rw [commutatorSpace_closure_eq_iSup_movedSpace]
  refine (finrank_iSup_le_sum (fun i => movedSpace (x i))).trans ?_
  calc ∑ i, finrank K ↥(movedSpace (x i)) ≤ ∑ _i : ι, r :=
        Finset.sum_le_sum fun i _ => hr i
    _ = Fintype.card ι * r := by simp [Finset.sum_const]

end FiniteDimensional

end CFSG.HardMathSupport.Kantor79
