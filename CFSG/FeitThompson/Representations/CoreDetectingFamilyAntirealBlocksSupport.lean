module

public import CFSG.FeitThompson.Definitions.WeightedSubcoherenceBlockData
public import CFSG.FeitThompson.Representations.EqualDegreeRowsCoherentAmbientMap
public import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
public import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Functor.Functorial
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.RegularLocalRing.Defs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open CategoryTheory

theorem FDRep.hom_apply_rho {G : Type*} [Group G] {V W : FDRep ℂ G} (f : V ⟶ W) (g : G)
    (w : V.V) : f.hom.hom.hom (V.ρ g w) = W.ρ g (f.hom.hom.hom w) :=
  congrArg (fun m : V.V ⟶ W.V => m.hom.hom w) (f.comm g)

theorem simple_of_isIrreducible {G : Type*} [Group G] (V : FDRep ℂ G)
    (h : Representation.IsIrreducible V.ρ) : Simple V := by
  have hnt : Nontrivial V.V := Representation.nontrivial_of_isIrreducible V.ρ h
  constructor
  intro Y f hmono
  have hinj : Function.Injective f.hom.hom.hom :=
    (Rep.mono_iff_injective _).1 (Functor.map_mono (forget₂ (FDRep ℂ G) (Rep ℂ G)) f)
  set S : Subrepresentation V.ρ :=
    { toSubmodule := LinearMap.range f.hom.hom.hom
      apply_mem_toSubmodule := by
        rintro g v ⟨w, rfl⟩
        exact ⟨Y.ρ g w, FDRep.hom_apply_rho f g w⟩ } with hS
  have hzero_iff : f = 0 ↔ ∀ w, f.hom.hom.hom w = 0 :=
    ⟨fun hf w => by rw [hf]; rfl, fun hf => by ext w; exact hf w⟩
  have hcases := h.eq_bot_or_eq_top S
  constructor
  ·
    intro hiso hf0
    obtain ⟨a, b, hab⟩ := hnt
    obtain ⟨g, -, hg2⟩ := hiso.out
    have h1 : (𝟙 V : V ⟶ V) = 0 := by rw [← hg2, hf0]; simp
    refine hab ?_
    have ha : a = (0 : V ⟶ V).hom.hom.hom a :=
      congrArg (fun m : V ⟶ V => m.hom.hom.hom a) h1
    have hb : b = (0 : V ⟶ V).hom.hom.hom b :=
      congrArg (fun m : V ⟶ V => m.hom.hom.hom b) h1
    rw [ha, hb]; rfl
  · intro hf0
    rcases hcases with hb | ht
    ·
      exact absurd (hzero_iff.2 fun w => by
        have hmem : f.hom.hom.hom w ∈ S := ⟨w, rfl⟩
        rw [hb] at hmem
        exact (hmem : f.hom.hom.hom w ∈ (⊥ : Subrepresentation V.ρ).toSubmodule)) hf0
    ·
      have hsurj : Function.Surjective f.hom.hom.hom := by
        intro v
        have hmem : v ∈ (⊤ : Subrepresentation V.ρ) := trivial
        rw [← ht] at hmem
        exact hmem
      set e : Y.V.obj ≃ₗ[ℂ] V.V.obj :=
        LinearEquiv.ofBijective f.hom.hom.hom ⟨hinj, hsurj⟩ with he
      have hinv : IsIso f.hom.hom := by
        refine ⟨ModuleCat.ofHom e.symm.toLinearMap, ?_, ?_⟩
        · ext w; exact e.symm_apply_apply w
        · ext v; exact e.apply_symm_apply v
      have hiso2 : IsIso f.hom := (ObjectProperty.isIso_hom_iff f.hom).mp hinv
      exact Action.isIso_of_hom_isIso f

theorem Irr_subset_virtualCharSpan (G : Type*) [Group G] :
    Irr G ⊆ (virtualCharSpan G : Set (G → ℂ)) := by
  rintro χ hχ
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hχ
  have : Simple V := simple_of_isIrreducible V hV
  exact character_mem_virtualCharSpan V

theorem span_Irr_le_virtualCharSpan (G : Type*) [Group G] :
    Submodule.span ℤ (Irr G) ≤ virtualCharSpan G :=
  Submodule.span_le.2 (Irr_subset_virtualCharSpan G)

theorem mem_virtualCharSpan_of_mem_span_Irr {G : Type*} [Group G] {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) : f ∈ virtualCharSpan G :=
  span_Irr_le_virtualCharSpan G hf

namespace IsPrimeCyclicTIHyp

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

section Sign

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem star_primeTIirr_principal_left_eq_smul (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    star (h.primeTIirr σ (principalIrr ↥W₁) j)
      = (h.primeTISign σ j * h.primeTISign σ (starIrr j)) •
        h.primeTIirr σ (principalIrr ↥W₁) (starIrr j) := by
  have hstar : (classFun.starₗ ↥(W₁ ⊔ W₂)) (h.isCyclicTIPair.basisProdIrr
      (principalIrr ↥W₁, j)) = h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, starIrr j) := by
    refine h.isCyclicTIPair.starₗ_basisProdIrr ?_ (coe_starIrr j)
    rw [coe_principalIrr]
    simp
  have key : star ((σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, j)) : L → ℂ))
      = ((σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, starIrr j))) : L → ℂ) := by
    rw [← classFun.coe_starₗ, ← hσ.map_starₗ h.isCyclicTIPair, hstar]
  have hsq : h.primeTISign σ (starIrr j) * h.primeTISign σ (starIrr j) = 1 :=
    h.primeTISign_mul_self _
  have hbk : ((σ (h.isCyclicTIPair.basisProdIrr (principalIrr ↥W₁, starIrr j))) : L → ℂ)
      = h.primeTISign σ (starIrr j) • h.primeTIirr σ (principalIrr ↥W₁) (starIrr j) := by
    rw [h.primeTIirr_principal_left, smul_smul, hsq, one_smul]
  have hsr : star (h.primeTISign σ j) = h.primeTISign σ j := h.conj_primeTISign j
  rw [h.primeTIirr_principal_left, star_smul, hsr, key, hbk, smul_smul]

theorem primeTISign_starIrr_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTISign σ (starIrr j) = h.primeTISign σ j := by
  obtain ⟨d, hd, hdeg⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr
    (h.primeTIirr_mem_Irr hσ (principalIrr ↥W₁) j)
  obtain ⟨e, he, hedeg⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr
    (h.primeTIirr_mem_Irr hσ (principalIrr ↥W₁) (starIrr j))
  have h2 := congrFun (h.star_primeTIirr_principal_left_eq_smul hσ j) 1
  rw [Pi.star_apply, Pi.smul_apply, hdeg, hedeg, smul_eq_mul, star_natCast] at h2
  rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j with hj | hj <;>
    rcases h.primeTISign_eq_one_or_eq_neg_one (σ := σ) (starIrr j) with hk | hk <;>
      rw [hj, hk] at h2 ⊢ <;> try rfl
  · exfalso
    have hc : (d : ℂ) = -(e : ℂ) := by linear_combination h2
    have hde : (d : ℝ) = -(e : ℝ) := by exact_mod_cast hc
    have h1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h3 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
    linarith
  · exfalso
    have hc : (d : ℂ) = -(e : ℂ) := by linear_combination h2
    have hde : (d : ℝ) = -(e : ℝ) := by exact_mod_cast hc
    have h1 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have h3 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
    linarith

theorem primeTIirr_one_starIrr_eq (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIirr σ i j 1 = h.primeTIirr σ i (starIrr j) 1 := by
  have h2 := congrFun (h.star_primeTIirr_principal_left_eq_smul hσ j) 1
  rw [h.primeTISign_starIrr_eq hσ j, h.primeTISign_mul_self, one_smul] at h2
  rw [h.primeTIirr_one i j, h.primeTIirr_one i (starIrr j), ← h2, Pi.star_apply,
    RCLike.star_def, conj_apply_one_of_mem_Irr (h.primeTIirr_mem_Irr hσ _ j)]

end Sign

section Rows

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]

theorem primeTIrow_starIrr_eq_star (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) :
    h.primeTIrow σ (starIrr j) = star (h.primeTIrow σ j) :=
  (star_primeTIrow h hσ j (h.primeTISign_starIrr_eq hσ j).symm).symm

end Rows

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson
