module

public import CFSG.Geometry.ProjectiveSpaces.Dimension
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open scoped LinearAlgebra.Projectivization
open Module

namespace CFSG.Geometry.ProjectiveSpaces

namespace ProjectiveSpace

universe u v w

variable {P : Type u} (G : ProjectiveSpace P) {E : Type v} [DivisionRing E] {V : Type w}
  [AddCommGroup V] [Module E V]

@[expose] def IsModel (ψ : P ≃ ℙ E V) : Prop :=
  ∀ p q r : P, p ≠ q → (r ∈ G.line p q ↔ (ψ r).submodule ≤ (ψ p).submodule ⊔ (ψ q).submodule)

variable {G} {ψ : P ≃ ℙ E V}

@[expose] def pointSet (ψ : P ≃ ℙ E V) (W : Submodule E V) : Set P := {p | (ψ p).submodule ≤ W}

theorem mk_eq_of_mem_submodule {x : ℙ E V} {v : V} (hv : v ≠ 0) (h : v ∈ x.submodule) :
    Projectivization.mk E v hv = x := by
  rw [Projectivization.submodule_eq, Submodule.mem_span_singleton] at h
  obtain ⟨a, rfl⟩ := h
  conv_rhs => rw [← Projectivization.mk_rep x]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨a, rfl⟩

theorem symm_mk_mem_pointSet {W : Submodule E V} {v : V} (hv : v ≠ 0) :
    ψ.symm (Projectivization.mk E v hv) ∈ pointSet ψ W ↔ v ∈ W := by
  change (ψ (ψ.symm _)).submodule ≤ W ↔ _
  rw [Equiv.apply_symm_apply, Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

theorem IsModel.isSubspace_pointSet (hψ : G.IsModel ψ) (W : Submodule E V) :
    G.IsSubspace (pointSet ψ W) :=
  fun p hp q hq hpq _ hr => ((hψ p q _ hpq).1 hr).trans (sup_le hp hq)

theorem pointSet_nonempty {W : Submodule E V} (hW : W ≠ ⊥) : (pointSet ψ W).Nonempty := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  exact ⟨_, (symm_mk_mem_pointSet hv0).2 hv⟩

theorem pointSet_mono {W W' : Submodule E V} (h : W ≤ W') : pointSet ψ W ⊆ pointSet ψ W' :=
  fun _ hp => le_trans hp h

theorem pointSet_ssubset {W W' : Submodule E V} (h : W < W') :
    pointSet ψ W ⊂ pointSet ψ W' := by
  refine Set.ssubset_iff_subset_ne.2 ⟨pointSet_mono h.le, fun he => ?_⟩
  obtain ⟨v, hv, hvW⟩ := IsConcreteLE.exists_of_lt h
  have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ W.zero_mem)
  have hp := (symm_mk_mem_pointSet (ψ := ψ) hv0).2 hv
  rw [← he, symm_mk_mem_pointSet] at hp
  exact hvW hp

@[expose] noncomputable def spanOf (ψ : P ≃ ℙ E V) (X : Set P) : Submodule E V :=
  ⨆ p ∈ X, (ψ p).submodule

theorem submodule_le_spanOf {X : Set P} {p : P} (hp : p ∈ X) :
    (ψ p).submodule ≤ spanOf ψ X :=
  le_iSup₂ (f := fun p (_ : p ∈ X) => (ψ p).submodule) p hp

theorem spanOf_mono {X Y : Set P} (h : X ⊆ Y) : spanOf ψ X ≤ spanOf ψ Y :=
  iSup₂_le fun _ hp => submodule_le_spanOf (h hp)

theorem spanOf_ne_bot {X : Set P} (hX : X.Nonempty) : spanOf ψ X ≠ ⊥ := by
  obtain ⟨p, hp⟩ := hX
  intro h
  have := submodule_le_spanOf (ψ := ψ) hp
  rw [h, le_bot_iff, Projectivization.submodule_eq, Submodule.span_singleton_eq_bot] at this
  exact (ψ p).rep_nonzero this

@[expose] noncomputable def IsModel.submoduleOf (hψ : G.IsModel ψ) {X : Set P}
    (hX : G.IsSubspace X) : Submodule E V where
  carrier := {v | ∀ hv : v ≠ 0, ψ.symm (Projectivization.mk E v hv) ∈ X}
  zero_mem' := fun h => absurd rfl h
  add_mem' := by
    intro v w hv hw hvw
    by_cases hv0 : v = 0
    · have hw0 : w ≠ 0 := fun h => hvw (by rw [hv0, h, add_zero])
      have e : Projectivization.mk E (v + w) hvw = Projectivization.mk E w hw0 := by
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨1, by rw [one_smul, hv0, zero_add]⟩
      rw [e]
      exact hw hw0
    by_cases hw0 : w = 0
    · have e : Projectivization.mk E (v + w) hvw = Projectivization.mk E v hv0 := by
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨1, by rw [one_smul, hw0, add_zero]⟩
      rw [e]
      exact hv hv0
    by_cases hpq : ψ.symm (Projectivization.mk E v hv0) = ψ.symm (Projectivization.mk E w hw0)
    · have h1 := ψ.symm.injective hpq
      rw [Projectivization.mk_eq_mk_iff'] at h1
      obtain ⟨a, ha⟩ := h1
      have e : Projectivization.mk E (v + w) hvw = Projectivization.mk E w hw0 := by
        rw [Projectivization.mk_eq_mk_iff']
        exact ⟨a + 1, by rw [add_smul, one_smul, ha]⟩
      rw [e]
      exact hw hw0
    · refine hX.line_subset (hv hv0) (hw hw0) ?_
      rw [hψ _ _ _ hpq, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        Projectivization.submodule_mk, Projectivization.submodule_mk,
        Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]
      exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self v)
        (Submodule.mem_span_singleton_self w)
  smul_mem' := by
    intro a v hv hav
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hav (smul_zero a)
    have e : Projectivization.mk E (a • v) hav = Projectivization.mk E v hv0 := by
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨a, rfl⟩
    rw [e]
    exact hv hv0

theorem IsModel.pointSet_spanOf (hψ : G.IsModel ψ) {X : Set P} (hX : G.IsSubspace X) :
    pointSet ψ (spanOf ψ X) = X := by
  refine Set.Subset.antisymm (fun r hr => ?_) (fun p hp => submodule_le_spanOf hp)
  have hle : spanOf ψ X ≤ hψ.submoduleOf hX := by
    refine iSup₂_le fun p hp v hv hv0 => ?_
    rw [mk_eq_of_mem_submodule hv0 hv, Equiv.symm_apply_apply]
    exact hp
  have hrep : (ψ r).rep ∈ hψ.submoduleOf hX := hle (hr (by
    rw [Projectivization.submodule_eq]
    exact Submodule.mem_span_singleton_self _))
  have := hrep (ψ r).rep_nonzero
  rwa [Projectivization.mk_rep, Equiv.symm_apply_apply] at this

theorem IsModel.spanOf_lt (hψ : G.IsModel ψ) {X Y : Set P} (hX : G.IsSubspace X)
    (hY : G.IsSubspace Y) (h : X ⊂ Y) : spanOf ψ X < spanOf ψ Y :=
  lt_of_le_of_ne (spanOf_mono h.subset) fun e => h.ne (by
    rw [← hψ.pointSet_spanOf hX, e, hψ.pointSet_spanOf hY])

theorem IsModel.le_of_linearIndependent (hψ : G.IsModel ψ) {n : ℕ} (hG : G.HasDimension n)
    {m : ℕ} {u : Fin (m + 1) → V} (hu : LinearIndependent E u) : m ≤ n := by
  let W : Fin (m + 1) → Submodule E V := fun i => Submodule.span E (u '' Set.Iic i)
  have hmem : ∀ i, u i ∈ W i := fun i =>
    Submodule.subset_span (Set.mem_image_of_mem u (Set.mem_Iic.2 le_rfl))
  have hW : StrictMono W := fun i j hij => by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hij.le)))
      fun e => ?_
    have h1 := hmem j
    rw [← e] at h1
    exact hu.notMem_span_image (s := Set.Iic i) (x := j) (fun h => absurd h (not_le.2 hij)) h1
  have hW0 : ∀ i, W i ≠ ⊥ := fun i h => by
    have h1 := hmem i
    rw [h, Submodule.mem_bot] at h1
    exact hu.ne_zero i h1
  have hne : Nonempty P := ⟨(pointSet_nonempty (ψ := ψ) (hW0 0)).some⟩
  let X : Fin (m + 1) → Set P := fun i => if i = Fin.last m then Set.univ else pointSet ψ (W i)
  refine hG.2 m X ⟨fun i => ?_, fun i j hij => ?_, by simp [X]⟩
  · by_cases hi : i = Fin.last m
    · simp only [X, hi, ite_true]
      exact ⟨G.isSubspace_univ, Set.univ_nonempty⟩
    · simp only [X, hi, ite_false]
      exact ⟨hψ.isSubspace_pointSet _, pointSet_nonempty (hW0 i)⟩
  · have hi : i ≠ Fin.last m := ne_of_lt (lt_of_lt_of_le hij (Fin.le_last j))
    simp only [X, hi, ite_false]
    by_cases hj : j = Fin.last m
    · simp only [hj, ite_true]
      exact (pointSet_ssubset (hW hij)).trans_subset (Set.subset_univ _)
    · simp only [hj, ite_false]
      exact pointSet_ssubset (hW hij)

theorem IsModel.finiteDimensional (hψ : G.IsModel ψ) {n : ℕ} (hG : G.HasDimension n) :
    FiniteDimensional E V := by
  let b := Module.Basis.ofVectorSpace E V
  have : Finite (Module.Basis.ofVectorSpaceIndex E V) := by
    by_contra h
    have : Infinite (Module.Basis.ofVectorSpaceIndex E V) := not_finite_iff_infinite.1 h
    let f : Fin (n + 2) ↪ Module.Basis.ofVectorSpaceIndex E V :=
      Fin.valEmbedding.trans (Infinite.natEmbedding _)
    have := hψ.le_of_linearIndependent hG (b.linearIndependent.comp f f.injective)
    omega
  exact Module.Finite.of_basis b

theorem IsModel.finrank_eq (hψ : G.IsModel ψ) {n : ℕ} (hG : G.HasDimension n) :
    FiniteDimensional E V ∧ finrank E V = n + 1 := by
  have hfd := hψ.finiteDimensional hG
  refine ⟨hfd, le_antisymm ?_ ?_⟩
  · obtain ⟨S, hS, -, -⟩ := hG.1
    obtain ⟨p, -⟩ := (hS 0).2
    have : Nontrivial V := nontrivial_of_ne _ _ (ψ p).rep_nonzero
    obtain ⟨m, hm⟩ : ∃ m, finrank E V = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := E) (M := V)).ne'
    have := hψ.le_of_linearIndependent hG
      ((Module.finBasis E V).reindex (finCongr hm)).linearIndependent
    omega
  · obtain ⟨S, hS, hmono, -⟩ := hG.1
    let W : Fin (n + 1) → Submodule E V := fun i => spanOf ψ (S i)
    have hW : StrictMono W := fun i j hij => hψ.spanOf_lt (hS i).1 (hS j).1 (hmono hij)
    have key : ∀ k (hk : k < n + 1), k + 1 ≤ finrank E (W ⟨k, hk⟩) := by
      intro k
      induction k with
      | zero =>
        intro hk
        refine Nat.one_le_iff_ne_zero.2 fun h => spanOf_ne_bot (ψ := ψ) (hS ⟨0, hk⟩).2 ?_
        exact (Submodule.finrank_eq_zero (R := E) (M := V) (S := W ⟨0, hk⟩)).1 h
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 : W ⟨k, by omega⟩ < W ⟨k + 1, hk⟩ := hW (Fin.mk_lt_mk.2 (Nat.lt_succ_self k))
        have := Submodule.finrank_lt_finrank_of_lt h2
        omega
    exact (key n (Nat.lt_succ_self n)).trans (Submodule.finrank_le _)

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
