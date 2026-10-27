module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bRepInd
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.TotallySplit

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped Classical
open CFSG.Semidihedral.Principal CFSG.QuasithinUnique.Setup.X7b Representation

section Count

variable {k G : Type} [Field k] [Group G]

@[expose] noncomputable def repLength {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ℕ :=
  (Module.length (MonoidAlgebra k G) ρ.asModule).toNat

@[expose] noncomputable def nontrivCount {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ℕ :=
  repLength ρ - repMultiplicity ρ (Representation.trivial k G k)

variable {V V₁ V₂ V₃ : Type} [AddCommGroup V] [Module k V] [AddCommGroup V₁] [Module k V₁]
  [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]

theorem repLength_eq_add_of_exact [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {ρ₃ : Representation k G V₃} (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    repLength ρ₂ = repLength ρ₁ + repLength ρ₃ := by
  have n1 := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₁.asModule)
  have a1 := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₁.asModule)
  have n3 := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₃.asModule)
  have a3 := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ₃.asModule)
  have h := Module.length_eq_add_of_exact (IntertwiningMap.equivLinearMapAsModule ρ₁ ρ₂ f)
    (IntertwiningMap.equivLinearMapAsModule ρ₂ ρ₃ g) hf hg H
  unfold repLength
  rw [h, ENat.toNat_add Module.length_ne_top Module.length_ne_top]

theorem repMultiplicity_le_repLength [FiniteDimensional k V] (ρ : Representation k G V)
    {E : Type} [AddCommGroup E] [Module k E] (σ : Representation k G E) :
    repMultiplicity ρ σ ≤ repLength ρ := by
  have n1 := isNoetherian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ.asModule)
  have a1 := isArtinian_of_finiteDimensional k (A := MonoidAlgebra k G) (M := ρ.asModule)
  obtain ⟨s, h₁, h₂⟩ :=
    exists_compositionSeries_of_isNoetherian_isArtinian (MonoidAlgebra k G) ρ.asModule
  have h3 : repMultiplicity ρ σ = factorCount (MonoidAlgebra k G) s σ.asModule :=
    compositionMultiplicity_eq_factorCount s h₁ h₂ _
  have h4 : repLength ρ = s.length := by
    unfold repLength
    rw [← Module.length_compositionSeries s h₁ h₂]
    simp
  rw [h3, h4]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem nontrivCount_eq_add_of_exact [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] {ρ₁ : Representation k G V₁} {ρ₂ : Representation k G V₂}
    {ρ₃ : Representation k G V₃} (f : ρ₁.IntertwiningMap ρ₂) (g : ρ₂.IntertwiningMap ρ₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    nontrivCount ρ₂ = nontrivCount ρ₁ + nontrivCount ρ₃ := by
  have h1 := repLength_eq_add_of_exact f g hf hg H
  have h2 := repMultiplicity_eq_add_of_exact f g hf hg H (Representation.trivial k G k)
  have h3 := repMultiplicity_le_repLength ρ₁ (Representation.trivial k G k)
  have h4 := repMultiplicity_le_repLength ρ₃ (Representation.trivial k G k)
  unfold nontrivCount
  omega

theorem nontrivCount_sub_quot [FiniteDimensional k V] (ρ : Representation k G V)
    (W : Subrepresentation ρ) :
    nontrivCount ρ = nontrivCount W.toRepresentation + nontrivCount W.quotient :=
  nontrivCount_eq_add_of_exact (subIncl ρ W) (quotProj ρ W) W.toSubmodule.injective_subtype
    W.toSubmodule.mkQ_surjective (LinearMap.exact_subtype_mkQ _)

theorem nontrivCount_of_subsingleton [Subsingleton V] (ρ : Representation k G V) :
    nontrivCount ρ = 0 := by
  have : Subsingleton ρ.asModule := inferInstanceAs (Subsingleton V)
  unfold nontrivCount repLength
  rw [Module.length_eq_zero]
  simp

theorem nontrivCount_of_isIrreducible [FiniteDimensional k V] (ρ : Representation k G V)
    (hρ : ρ.IsIrreducible) :
    nontrivCount ρ = if Nonempty (ρ.Equiv (Representation.trivial k G k)) then 0 else 1 := by
  have hs : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  have hlen : repLength ρ = 1 := by
    unfold repLength
    rw [Module.length_eq_one]
    rfl
  have hmul := repMultiplicity_of_isIrreducible hρ (Representation.trivial k G k)
  unfold nontrivCount
  rw [hlen, hmul]
  split_ifs <;> simp

theorem nontrivCount_le_one_of_isIrreducible [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) : nontrivCount ρ ≤ 1 := by
  rw [nontrivCount_of_isIrreducible ρ hρ]
  split_ifs <;> simp

theorem toRepresentation_trivial {ρ : Representation k G V} (W : Subrepresentation ρ)
    (h : ∀ g, ρ g = 1) : ∀ g, W.toRepresentation g = 1 := by
  intro g
  refine LinearMap.ext fun w => Subtype.ext ?_
  show ρ g w.1 = w.1
  rw [h g]
  rfl

theorem quotient_trivial {ρ : Representation k G V} (W : Subrepresentation ρ)
    (h : ∀ g, ρ g = 1) : ∀ g, W.quotient g = 1 := by
  intro g
  refine LinearMap.ext fun q => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show Submodule.Quotient.mk (ρ g v) = Submodule.Quotient.mk v
  rw [h g]
  rfl

theorem equiv_trivial_of_trivial_isIrreducible [FiniteDimensional k V]
    (ρ : Representation k G V) (hρ : ρ.IsIrreducible) (h : ∀ g, ρ g = 1) :
    Nonempty (ρ.Equiv (Representation.trivial k G k)) := by
  have hnt : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have h1 : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      show (⊥ : Submodule k V) = ⊤
      exact Submodule.eq_top_iff'.mpr fun x => (Submodule.mem_bot k).mpr (Subsingleton.elim x 0)
    exact bot_ne_top h1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ :=
    ⟨Submodule.span k {v}, fun g w hw => by rw [h g]; exact hw⟩
  have hvS : v ∈ S.toSubmodule := Submodule.mem_span_singleton_self v
  have htop : S = ⊤ := by
    rcases eq_bot_or_eq_top S with h0 | h0
    · exfalso
      rw [h0] at hvS
      exact hv ((Submodule.mem_bot k).mp hvS)
    · exact h0
  have hall : ∀ w : V, ∃ c : k, c • v = w := fun w => by
    have : w ∈ S.toSubmodule := by rw [htop]; trivial
    exact Submodule.mem_span_singleton.mp this
  have hrank : Module.finrank k V = 1 := (finrank_eq_one_iff_of_nonzero' v hv).mpr hall
  let e : V ≃ₗ[k] k := LinearEquiv.ofFinrankEq V k (by rw [hrank, Module.finrank_self])
  exact ⟨Representation.Equiv.mk e fun g => by rw [h g]; rfl⟩

theorem nontrivCount_eq_zero_of_trivial [Module.Finite k V] (ρ : Representation k G V)
    (h : ∀ g, ρ g = 1) : nontrivCount ρ = 0 := by
  have key := rep_induction (k := k) (G := G)
    (fun {V} _ _ _ ρ => (∀ g, ρ g = 1) → nontrivCount ρ = 0)
    (fun {V} _ _ _ ρ hsub _ => by haveI := hsub; exact nontrivCount_of_subsingleton ρ)
    (fun {V} _ _ _ ρ hρ htriv => by
      rw [nontrivCount_of_isIrreducible ρ hρ,
        if_pos (equiv_trivial_of_trivial_isIrreducible ρ hρ htriv)])
    (fun {V} _ _ _ ρ W hW1 hW2 htriv => by
      rw [nontrivCount_sub_quot ρ W, hW1 (toRepresentation_trivial W htriv),
        hW2 (quotient_trivial W htriv)])
  exact key _ ρ rfl h

theorem extension_trivial (hperf : commutator G = ⊤) {ρ : Representation k G V}
    (W : Subrepresentation ρ) (hWt : ∀ g, W.toRepresentation g = 1)
    (hQt : ∀ g, W.quotient g = 1) : ∀ g, ρ g = 1 := by
  have hW : ∀ g, ∀ w ∈ W.toSubmodule, ρ g w = w := fun g w hw => by
    have := LinearMap.congr_fun (hWt g) ⟨w, hw⟩
    exact (Subrepresentation.toRepresentation_apply_mk).mp this
  have hQ : ∀ g v, ρ g v - v ∈ W.toSubmodule := fun g v => by
    have h1 : W.quotient g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := by
      have := LinearMap.congr_fun (hQt g) (Submodule.Quotient.mk v)
      simpa using this
    have h2 : (Submodule.Quotient.mk (ρ g v) : V ⧸ W.toSubmodule) = Submodule.Quotient.mk v := h1
    exact (Submodule.Quotient.eq _).mp h2
  let φ : G →* Multiplicative (V →ₗ[k] V) :=
    { toFun := fun g => Multiplicative.ofAdd (ρ g - 1)
      map_one' := by simp
      map_mul' := fun g h => by
        show Multiplicative.ofAdd (ρ (g * h) - 1) =
          Multiplicative.ofAdd (ρ g - 1) * Multiplicative.ofAdd (ρ h - 1)
        rw [← ofAdd_add]
        congr 1
        refine LinearMap.ext fun v => ?_
        have h1 := hW g _ (hQ h v)
        rw [map_sub] at h1
        simp only [map_mul, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
          Module.End.one_apply]
        rw [← h1]
        abel }
  have hker := Abelianization.commutator_subset_ker φ
  rw [hperf] at hker
  intro g
  have h1 : Multiplicative.ofAdd (ρ g - 1) = (1 : Multiplicative (V →ₗ[k] V)) :=
    hker (Subgroup.mem_top g)
  exact sub_eq_zero.mp (ofAdd_eq_one.mp h1)

theorem trivial_of_nontrivCount_eq_zero (hperf : commutator G = ⊤) [Module.Finite k V]
    (ρ : Representation k G V) (h : nontrivCount ρ = 0) : ∀ g, ρ g = 1 := by
  have key := rep_induction (k := k) (G := G)
    (fun {V} _ _ _ ρ => nontrivCount ρ = 0 → ∀ g, ρ g = 1)
    (fun {V} _ _ _ ρ hsub _ g => by haveI := hsub; exact Subsingleton.elim _ _)
    (fun {V} _ _ _ ρ hρ h0 g => by
      rw [nontrivCount_of_isIrreducible ρ hρ] at h0
      have hne : Nonempty (ρ.Equiv (Representation.trivial k G k)) := by
        by_contra hn
        rw [if_neg hn] at h0
        exact one_ne_zero h0
      obtain ⟨φ⟩ := hne
      refine LinearMap.ext fun v => ?_
      apply φ.injective
      have := LinearMap.congr_fun (φ.isIntertwining' g) v
      simpa using this)
    (fun {V} _ _ _ ρ W hW1 hW2 h0 => by
      rw [nontrivCount_sub_quot ρ W] at h0
      exact extension_trivial hperf W (hW1 (by omega)) (hW2 (by omega)))
  exact key _ ρ rfl h

end Count

end CFSG.LocalAnalysis.RankThreeUC.S15
