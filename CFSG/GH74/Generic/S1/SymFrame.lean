module

public import CFSG.GH74.Generic.S1.SymLocal
public import CFSG.GH74.Generic.S1.SymTransport

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic

section SymX

variable {G : Type}

@[expose] def symX (x : G) (u : Fin 4 → G) (i : Fin 5) : G :=
  if h : i.val < 4 then u ⟨i.val, h⟩ else x

theorem symX_castSucc (x : G) (u : Fin 4 → G) (k : Fin 4) : symX x u (Fin.castSucc k) = u k := by
  simp [symX]

theorem symX_last (x : G) (u : Fin 4 → G) : symX x u (Fin.last 4) = x := by
  simp [symX]

theorem symX_zero (x : G) (u : Fin 4 → G) : symX x u 0 = u 0 := by simp [symX]
theorem symX_one (x : G) (u : Fin 4 → G) : symX x u 1 = u 1 := by simp [symX]
theorem symX_two (x : G) (u : Fin 4 → G) : symX x u 2 = u 2 := by simp [symX]
theorem symX_three (x : G) (u : Fin 4 → G) : symX x u 3 = u 3 := by simp [symX]
theorem symX_four (x : G) (u : Fin 4 → G) : symX x u 4 = x := by simp [symX]

end SymX

variable {G : Type} [Group G]

section Defs

variable [Finite G]

@[expose] def S1LocalFrameLin (y : G) (K' : Subgroup (CentralizerBar y)) (w : Fin 4 → G)
    (hw : ∀ j, w j ∈ centralizer ({y} : Set G)) (F : Type) [Field F] : Prop :=
  S1Setup G y K' ∧ S1Front G y K' ∧ S1Frame y K' w hw ∧
    ∃ e : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e (barOf (hw j)) (reflDiag F j)

@[expose] def S1LocalFrameUni (y : G) (K' : Subgroup (CentralizerBar y)) (w : Fin 4 → G)
    (hw : ∀ j, w j ∈ centralizer ({y} : Set G)) (q : ℕ) (F : Type) [Field F] : Prop :=
  S1Setup G y K' ∧ S1Front G y K' ∧ S1Frame y K' w hw ∧
    ∃ e : ↥K' ≃* ↥(StatedSU 4 q F), ∀ j, ActsAsReflOn e (barOf (hw j)) (reflDiag F j)

@[expose] def S1SymFrameLin (x : G) (u : Fin 4 → G) (F : Type) [Field F] : Prop :=
  ∀ i : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u i)))
    (hw : ∀ j, symX x u (i.succAbove j) ∈ centralizer ({symX x u i} : Set G)),
      S1LocalFrameLin (symX x u i) K' (fun j => symX x u (i.succAbove j)) hw F

@[expose] def S1SymFrameUni (x : G) (u : Fin 4 → G) (q : ℕ) (F : Type) [Field F] : Prop :=
  ∀ i : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u i)))
    (hw : ∀ j, symX x u (i.succAbove j) ∈ centralizer ({symX x u i} : Set G)),
      S1LocalFrameUni (symX x u i) K' (fun j => symX x u (i.succAbove j)) hw q F

@[expose] def S1SymFrame (x : G) (u : Fin 4 → G) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 4 = 3 ∧ S1SymFrameLin x u F) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      S1SymFrameUni x u q F)

end Defs

variable [Finite G]

theorem sym_at {x : G} {K : Subgroup (CentralizerBar x)} [K.Normal] (hset : S1Setup G x K)
    (hfront : S1Front G x K) {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)}
    (ops : ModelOps F S) (e : ↥K ≃* ↥S)
    (reflOf : ∀ (y : G) (K' : Subgroup (CentralizerBar y)) [K'.Normal], S1Setup G y K' →
      S1Front G y K' → ∀ (e' : ↥K' ≃* ↥S) {v : G} (hv : v ∈ centralizer ({y} : Set G)),
        IsConj y v → v ≠ y → v * v = 1 → barOf hv ∉ K' →
          IsReflection S (MulAut.congr e' (MulAut.conjNormal (barOf hv) : MulAut ↥K')))
    {y : G} (hy : IsConj x y) (w : Fin 4 → G) (hw : ∀ j, w j ∈ centralizer ({y} : Set G))
    (hw2 : ∀ j, w j * w j = 1) (hwc : ∀ j k, w j * w k = w k * w j)
    (hwconj : ∀ j, IsConj y (w j)) (hwne : ∀ j, w j ≠ y)
    (hind2 : ∀ j k, j ≠ k → w j * w k ≠ 1) (hind3 : ∀ j k, j ≠ k → w j * w k * y ≠ 1)
    (hprod : w 0 * w 1 * w 2 * w 3 = y) :
    ∃ K' : Subgroup (CentralizerBar y), S1Setup G y K' ∧ S1Front G y K' ∧
      (∀ j, IsConj y (w j) ∧ w j * w j = 1 ∧ barOf (hw j) ∉ K') ∧
        (∀ j k, w j * w k = w k * w j) ∧ w 0 * w 1 * w 2 * w 3 = y ∧
          (∀ j k, j ≠ k → w j ≠ w k) ∧
            ∃ e'' : ↥K' ≃* ↥S, ∀ j, ActsAsReflOn e'' (barOf (hw j)) (reflDiag F j) := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 hy
  have hset' := hset.conj g
  have hfront' := hfront.conj g
  have hKn : (K.map (barConj x g).toMonoidHom).Normal := normal_of_layer_eq hfront'.layer_eq
  let e' : ↥(K.map (barConj x g).toMonoidHom) ≃* ↥S :=
    (K.equivMapOfInjective (barConj x g).toMonoidHom (barConj x g).injective).symm.trans e
  have hnotK : ∀ j, barOf (hw j) ∉ K.map (barConj x g).toMonoidHom := fun j =>
    barOf_notMem hset' hfront' (hw j) (hw2 j) (hwconj j) (hwne j)
  have hR : ∀ j, IsReflection S (MulAut.congr e'
      (MulAut.conjNormal (barOf (hw j)) : MulAut ↥(K.map (barConj x g).toMonoidHom))) := fun j =>
    reflOf _ _ hset' hfront' e' (hw j) (hwconj j) (hwne j) (hw2 j) (hnotK j)
  obtain ⟨h1, h2, h3, h4, e'', h5⟩ :=
    sym_local hset' hfront' ops e' w hw hw2 hwc hwconj hwne hind2 hind3 hprod hR
  exact ⟨_, hset', hfront', h1, h2, h3, h4, e'', h5⟩

omit [Finite G] in
theorem symX_facts {x : G} {K : Subgroup (CentralizerBar x)} (hxK : xbar x ∈ K)
    (hx : orderOf x = 2) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) :
    (∀ i, IsConj x (symX x u i)) ∧ (∀ i, symX x u i * symX x u i = 1) ∧
      (∀ i j, symX x u i * symX x u j = symX x u j * symX x u i) ∧
        symX x u 0 * symX x u 1 * symX x u 2 * symX x u 3 * symX x u 4 = 1 ∧
          (∀ i j, i ≠ j → symX x u i ≠ symX x u j) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hf
  have hxx : x * x = 1 := by rw [← sq, ← hx]; exact pow_orderOf_eq_one x
  have hxu : ∀ k, u k * x = x * u k := fun k => mem_centralizer_singleton_iff.1 (hu k)
  have hne : ∀ k, u k ≠ x := by
    intro k hk
    apply (h1 k).2.2
    have key : ∀ (a : G) (ha : a ∈ centralizer ({x} : Set G)), a = x → barOf ha = xbar x := by
      rintro a ha rfl
      rfl
    rw [key (u k) (hu k) hk]
    exact hxK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [symX_last]
    · rw [symX_castSucc]
      exact (h1 k).1
  · intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · rw [symX_last]
      exact hxx
    · rw [symX_castSucc]
      exact (h1 k).2.1
  · intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases rfl (fun b => ?_) j
      rw [symX_last, symX_castSucc]
      exact (hxu b).symm
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · rw [symX_last, symX_castSucc]
        exact hxu a
      · rw [symX_castSucc, symX_castSucc]
        exact h2 a b
  · rw [symX_zero, symX_one, symX_two, symX_three, symX_four, h3, hxx]
  · intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases (fun h => (h rfl).elim) (fun b => ?_) j
      intro _
      rw [symX_last, symX_castSucc]
      exact (hne b).symm
    · refine Fin.lastCases ?_ (fun b => ?_) j
      · intro _
        rw [symX_last, symX_castSucc]
        exact hne a
      · intro hij
        rw [symX_castSucc, symX_castSucc]
        exact h4 a b (fun hab => hij (by rw [hab]))

end CFSG.GH74.Generic.S1
