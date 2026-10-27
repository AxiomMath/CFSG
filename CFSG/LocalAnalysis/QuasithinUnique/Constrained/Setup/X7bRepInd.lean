module

public import CFSG.CharacterTheory.Semidihedral.Principal.CompositionMultiplicity

public section

namespace CFSG.QuasithinUnique.Setup.X7b

open scoped MonoidAlgebra
open CFSG.Semidihedral.Principal Representation

variable {k G : Type} [Field k] [Monoid G]

section Basic

variable {V : Type} [AddCommGroup V] [Module k V]

@[expose] def subIncl (ρ : Representation k G V) (W : Subrepresentation ρ) :
    IntertwiningMap W.toRepresentation ρ where
  toLinearMap := W.toSubmodule.subtype
  isIntertwining' g := by ext x; rfl

@[expose] def quotProj (ρ : Representation k G V) (W : Subrepresentation ρ) :
    IntertwiningMap ρ W.quotient where
  toLinearMap := W.toSubmodule.mkQ
  isIntertwining' g := by ext x; rfl

theorem repMultiplicity_sub_quot [Module.Finite k V] (ρ : Representation k G V)
    (W : Subrepresentation ρ) {E : Type} [AddCommGroup E] [Module k E]
    (σ : Representation k G E) :
    repMultiplicity ρ σ = repMultiplicity W.toRepresentation σ + repMultiplicity W.quotient σ := by
  have : Module.Finite k W.toSubmodule := inferInstance
  have : Module.Finite k (V ⧸ W.toSubmodule) := inferInstance
  exact repMultiplicity_eq_add_of_exact (subIncl ρ W) (quotProj ρ W)
    W.toSubmodule.injective_subtype W.toSubmodule.mkQ_surjective
    (LinearMap.exact_subtype_mkQ _) σ

theorem exists_isCoatom_subrep [Module.Finite k V] (ρ : Representation k G V) [Nontrivial V] :
    ∃ W : Subrepresentation ρ, IsCoatom W := by
  have hfin : Module.Finite k[G] ρ.asModule := Module.Finite.of_restrictScalars_finite k _ _
  have : Nontrivial ρ.asModule := (Equiv.nontrivial_congr ρ.asModuleEquiv.toEquiv).mpr inferInstance
  have : Nontrivial (Submodule k[G] ρ.asModule) := (Submodule.nontrivial_iff k[G]).mpr inferInstance
  obtain ⟨N, hN⟩ := IsCoatomic.exists_coatom (α := Submodule k[G] ρ.asModule)
  exact ⟨Subrepresentation.subrepresentationSubmoduleOrderIso.symm N,
    (OrderIso.isCoatom_iff _ _).mpr hN⟩

theorem quotient_isIrreducible_of_isCoatom (ρ : Representation k G V) (W : Subrepresentation ρ)
    (hW : IsCoatom W) : W.quotient.IsIrreducible := by
  have hne : W.toSubmodule ≠ ⊤ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have : Nontrivial (V ⧸ W.toSubmodule) := (Submodule.Quotient.nontrivial_iff).mpr hne
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top this
  · intro S
    let T : Subrepresentation ρ := ⟨S.toSubmodule.comap W.toSubmodule.mkQ, by
      intro g v hv
      exact S.apply_mem_toSubmodule g (show W.toSubmodule.mkQ v ∈ S.toSubmodule from hv)⟩
    have hWT : W ≤ T := by
      intro v hv
      show W.toSubmodule.mkQ v ∈ S.toSubmodule
      have h0 : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
      rw [h0]
      exact S.toSubmodule.zero_mem
    rcases eq_or_lt_of_le hWT with h | h
    · left
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule y
      have hvT : v ∈ T := show W.toSubmodule.mkQ v ∈ S.toSubmodule from hy
      rw [← h] at hvT
      show W.toSubmodule.mkQ v = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr hvT
    · right
      have hT : T = ⊤ := hW.2 T h
      apply Subrepresentation.toSubmodule_injective
      show S.toSubmodule = ⊤
      rw [eq_top_iff]
      intro y _
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W.toSubmodule y
      have : v ∈ T := by rw [hT]; exact Submodule.mem_top
      exact this

theorem rep_induction
    (Q : ∀ {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V],
      Representation k G V → Prop)
    (h0 : ∀ {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
      (ρ : Representation k G V), Subsingleton V → Q ρ)
    (h1 : ∀ {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
      (ρ : Representation k G V), ρ.IsIrreducible → Q ρ)
    (h2 : ∀ {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
      (ρ : Representation k G V) (W : Subrepresentation ρ),
      Q W.toRepresentation → Q W.quotient → Q ρ) :
    ∀ (n : ℕ) {V : Type} [AddCommGroup V] [Module k V] [Module.Finite k V]
      (ρ : Representation k G V), Module.finrank k V = n → Q ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ ρ hn
    by_cases hsub : Subsingleton V
    · exact h0 ρ hsub
    · have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
      by_cases hirr : ρ.IsIrreducible
      · exact h1 ρ hirr
      · obtain ⟨W, hW⟩ := exists_isCoatom_subrep ρ
        have hWbot : W ≠ ⊥ := by
          rintro rfl
          exact hirr (isSimpleOrder_iff_isCoatom_bot.mpr hW)
        have hlt : Module.finrank k W.toSubmodule < n := by
          rw [← hn]
          apply Submodule.finrank_lt
          exact fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
        refine h2 ρ W (ih _ hlt W.toRepresentation rfl) ?_
        exact h1 _ (quotient_isIrreducible_of_isCoatom ρ W hW)

end Basic

section TwistGroup

variable {H : Type} [Monoid H] (α : H →* G) (hα : Function.Surjective α)

include hα

variable {V : Type} [AddCommGroup V] [Module k V]

@[expose] def subrepComp (ρ : Representation k G V) :
    Subrepresentation (ρ.comp α) ≃o Subrepresentation ρ where
  toFun S := ⟨S.toSubmodule, fun g v hv => by
    obtain ⟨h, rfl⟩ := hα g
    exact S.apply_mem_toSubmodule h hv⟩
  invFun S := ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (α h) hv⟩
  left_inv S := rfl
  right_inv S := rfl
  map_rel_iff' := Iff.rfl

theorem isIrreducible_comp (ρ : Representation k G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (ρ.comp α) :=
  (OrderIso.isSimpleOrder_iff (subrepComp α hα ρ)).mpr hρ

theorem nonempty_equiv_comp {W : Type} [AddCommGroup W] [Module k W] (ρ : Representation k G V)
    (σ : Representation k G W) :
    Nonempty (Representation.Equiv (ρ.comp α) (σ.comp α)) ↔ Nonempty (Representation.Equiv ρ σ) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨Representation.Equiv.mk e.toLinearEquiv (fun g => by
      obtain ⟨h, rfl⟩ := hα g
      exact e.isIntertwining' h)⟩
  · rintro ⟨e⟩
    exact ⟨Representation.Equiv.mk e.toLinearEquiv (fun h => e.isIntertwining' (α h))⟩

theorem repMultiplicity_comp_surjective {V : Type} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) {E : Type} [AddCommGroup E] [Module k E]
    (σ : Representation k G E) :
    repMultiplicity (ρ.comp α) (σ.comp α) = repMultiplicity ρ σ := by
  have key := rep_induction (k := k) (G := G)
    (fun {V} _ _ _ ρ => ∀ {E : Type} [AddCommGroup E] [Module k E] (σ : Representation k G E),
      repMultiplicity (ρ.comp α) (σ.comp α) = repMultiplicity ρ σ)
    (fun {V} _ _ _ ρ hsub {E} _ _ σ => by
      have : Subsingleton (Representation.asModule ρ) := inferInstanceAs (Subsingleton V)
      have : Subsingleton (Representation.asModule (ρ.comp α)) := inferInstanceAs (Subsingleton V)
      unfold repMultiplicity
      rw [compositionMultiplicity_of_subsingleton, compositionMultiplicity_of_subsingleton])
    (fun {V} _ _ _ ρ hρ {E} _ _ σ => by
      rw [repMultiplicity_of_isIrreducible (isIrreducible_comp α hα ρ hρ),
        repMultiplicity_of_isIrreducible hρ]
      have := nonempty_equiv_comp α hα ρ σ
      by_cases h : Nonempty (Representation.Equiv ρ σ)
      · simp only [h, this.mpr h, ↓reduceIte]
      · have h2 : ¬ Nonempty (Representation.Equiv (ρ.comp α) (σ.comp α)) :=
          fun h' => h (this.mp h')
        simp only [h, h2, ↓reduceIte])
    (fun {V} _ _ _ ρ W hW1 hW2 {E} _ _ σ => by
      have e1 := repMultiplicity_sub_quot ρ W σ
      have e2 := repMultiplicity_sub_quot (ρ.comp α) ((subrepComp α hα ρ).symm W) (σ.comp α)
      rw [e1, e2]
      exact congrArg₂ (· + ·) (hW1 σ) (hW2 σ))
  exact key _ ρ rfl σ

end TwistGroup

end CFSG.QuasithinUnique.Setup.X7b
