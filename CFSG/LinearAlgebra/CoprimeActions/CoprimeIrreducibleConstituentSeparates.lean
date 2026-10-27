module


public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Maschke

public section

namespace CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates

open Representation

variable {F H V : Type*} [Field F] [Group H] [AddCommGroup V] [Module F V]
  (ρ : Representation F H V)

theorem exists_constituent {F : Type*} {H : Type*} {V : Type*} [Field F] [Group H] [Finite H]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (ρ : Representation F H V)
    (hcard : (Nat.card H : F) ≠ 0) (h : H) (hh : ρ h ≠ 1) :
    ∃ W : Submodule F V, ∃ hW : ∀ g, W ≤ W.comap (ρ g), Nontrivial W ∧
      (Representation.subrepresentation ρ W hW).IsIrreducible ∧
      (Representation.subrepresentation ρ W hW) h ≠ 1 := by
  let MinimalSub (ρ : Representation F H V) (U : Subrepresentation ρ) : Prop :=
    U ≠ ⊥ ∧ ∀ X : Subrepresentation ρ, X ≤ U → X = ⊥ ∨ X = U
  have exists_isCompl (ρ : Representation F H V) [Finite H]
      (hcard : (Nat.card H : F) ≠ 0) (X : Subrepresentation ρ) :
      ∃ C : Subrepresentation ρ, IsCompl X C := by
    haveI : NeZero (Nat.card H : F) := ⟨hcard⟩
    obtain ⟨q, hq⟩ := MonoidAlgebra.Submodule.exists_isCompl
      (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ) X)
    refine ⟨Subrepresentation.subrepresentationSubmoduleOrderIso.symm q, ?_⟩
    have := (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).symm.isCompl hq
    rwa [OrderIso.symm_apply_apply] at this
  have exists_minimal (ρ : Representation F H V) [Finite H] [FiniteDimensional F V]
      (hcard : (Nat.card H : F) ≠ 0)
      (h : H) :
      ∀ (n : ℕ) (U : Subrepresentation ρ), Module.finrank F U.toSubmodule ≤ n →
        (∃ u ∈ U, ρ h u ≠ u) →
        ∃ W : Subrepresentation ρ, MinimalSub ρ W ∧ ∃ w ∈ W, ρ h w ≠ w := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hn ⟨u, huU, hu⟩
      by_cases hmin : MinimalSub ρ U
      · exact ⟨U, hmin, u, huU, hu⟩
      have hU0 : U ≠ ⊥ := by
        rintro rfl
        apply hu
        have h0 : u ∈ (⊥ : Submodule F V) := huU
        have : u = 0 := by simpa using h0
        simp [this]
      have : ∃ X : Subrepresentation ρ, X ≤ U ∧ X ≠ ⊥ ∧ X ≠ U := by
        by_contra hcon
        push Not at hcon
        exact hmin ⟨hU0, fun X hX => by
          by_cases h1 : X = ⊥
          · exact Or.inl h1
          · exact Or.inr (hcon X hX h1)⟩
      obtain ⟨X, hXU, hX0, hXU'⟩ := this
      obtain ⟨C, hC⟩ := exists_isCompl ρ hcard X
      let Y : Subrepresentation ρ := U ⊓ C
      have hXlt : X.toSubmodule < U.toSubmodule := by
        refine lt_of_le_of_ne hXU ?_
        intro heq; exact hXU' (Subrepresentation.toSubmodule_injective heq)
      have hYlt : Y.toSubmodule < U.toSubmodule := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro heq
        have hUC : U ≤ C := by
          intro x hx
          have : x ∈ Y.toSubmodule := by rw [heq]; exact hx
          exact (Submodule.mem_inf.mp this).2
        apply hX0
        have hXC : X ≤ C := hXU.trans hUC
        exact Disjoint.eq_bot_of_le hC.disjoint hXC
      have hdec : ∀ v ∈ U, ∃ x ∈ X, ∃ y ∈ Y, v = x + y := by
        intro v hv
        have htop : v ∈ (X ⊔ C).toSubmodule := by
          rw [hC.codisjoint.eq_top]; trivial
        rw [Subrepresentation.toSubmodule_sup, Submodule.mem_sup] at htop
        obtain ⟨x, hx, c, hc, rfl⟩ := htop
        refine ⟨x, hx, c, ⟨?_, hc⟩, rfl⟩
        have hxU : x ∈ U := hXU hx
        have := U.toSubmodule.sub_mem hv hxU
        simpa using this
      have hnl : (∃ u ∈ X, ρ h u ≠ u) ∨ (∃ u ∈ Y, ρ h u ≠ u) := by
        by_contra hcon
        push Not at hcon
        obtain ⟨x, hx, y, hy, rfl⟩ := hdec u huU
        apply hu
        rw [map_add, hcon.1 x hx, hcon.2 y hy]
      rcases hnl with hx | hy
      · exact ih _ (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hXlt) hn) X le_rfl hx
      · exact ih _ (lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hYlt) hn) Y le_rfl hy
  have irreducible_of_minimal (ρ : Representation F H V)
      (W : Subrepresentation ρ) (hmin : MinimalSub ρ W) :
      (Representation.subrepresentation ρ W.toSubmodule
        (fun g x hx => W.apply_mem_toSubmodule g hx)).IsIrreducible := by
    set σ := Representation.subrepresentation ρ W.toSubmodule
        (fun g x hx => W.apply_mem_toSubmodule g hx) with hσ
    have hne : ∃ w : W.toSubmodule, w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hmin.1
      ext x
      constructor
      · intro hx
        have := hcon ⟨x, hx⟩
        have h2 : x = 0 := congrArg Subtype.val this
        simp [h2]
      · intro hx
        have h0 : x ∈ (⊥ : Submodule F V) := hx
        have : x = 0 := by simpa using h0
        rw [this]; exact W.toSubmodule.zero_mem
    have key : ∀ X : Subrepresentation σ, X = ⊥ ∨ X = ⊤ := by
      intro X
      let Xp : Subrepresentation ρ :=
        ⟨X.toSubmodule.map W.toSubmodule.subtype, by
          rintro g v ⟨x, hx, rfl⟩
          exact ⟨σ g x, X.apply_mem_toSubmodule g hx, rfl⟩⟩
      have hXp : Xp ≤ W := by
        rintro v ⟨x, hx, rfl⟩
        exact x.2
      rcases hmin.2 Xp hXp with h | h
      · left
        ext x
        constructor
        · intro hx
          have h1 : (x : V) ∈ Xp := ⟨x, hx, rfl⟩
          rw [h] at h1
          have h2 : (x : V) ∈ (⊥ : Submodule F V) := h1
          have h3 : x = 0 := Subtype.ext (by simpa using h2)
          rw [h3]; exact Submodule.zero_mem _
        · intro hx
          have h0 : x ∈ (⊥ : Submodule F W.toSubmodule) := hx
          have : x = 0 := by simpa using h0
          rw [this]; exact X.toSubmodule.zero_mem
      · right
        ext x
        constructor
        · intro _; trivial
        · intro _
          have h1 : (x : V) ∈ Xp := by rw [h]; exact x.2
          obtain ⟨y, hy, hyx⟩ := h1
          have : y = x := Subtype.ext hyx
          rw [← this]; exact hy
    haveI : Nontrivial (Subrepresentation σ) := by
      refine ⟨⊥, ⊤, fun hbt => ?_⟩
      obtain ⟨w, hw⟩ := hne
      apply hw
      have : w ∈ (⊤ : Subrepresentation σ) := trivial
      rw [← hbt] at this
      have h0 : w ∈ (⊥ : Submodule F W.toSubmodule) := this
      simpa using h0
    exact ⟨key⟩
  have hu : ∃ u ∈ (⊤ : Subrepresentation ρ), ρ h u ≠ u := by
    by_contra hcon
    push Not at hcon
    apply hh
    ext x
    simpa using hcon x trivial
  obtain ⟨W, hmin, w, hw, hwne⟩ :=
    exists_minimal ρ hcard h _ ⊤ le_rfl hu
  refine ⟨W.toSubmodule, fun g x hx => W.apply_mem_toSubmodule g hx, ?_,
    irreducible_of_minimal ρ W hmin, ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hmin.1
    ext x
    constructor
    · intro hx
      have : (⟨x, hx⟩ : W.toSubmodule) = 0 := Subsingleton.elim _ _
      have h2 : x = 0 := congrArg Subtype.val this
      simp [h2]
    · intro hx
      have h0 : x ∈ (⊥ : Submodule F V) := hx
      have : x = 0 := by simpa using h0
      rw [this]; exact W.toSubmodule.zero_mem
  · intro h1
    apply hwne
    have := LinearMap.congr_fun h1 ⟨w, hw⟩
    exact congrArg Subtype.val this

end CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates
