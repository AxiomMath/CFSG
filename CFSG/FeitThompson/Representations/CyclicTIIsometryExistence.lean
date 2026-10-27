module

import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
import CFSG.FeitThompson.Representations.CyclicTIDifferencesOrthonormalSignedArray
import CFSG.FeitThompson.Representations.SaturatedSignedArraySingleCharacter
public import CFSG.FeitThompson.Representations.CyclicTIIsometryUnique

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

section Aux

variable {α : Type*} [Fintype α] {ι : Type*} [Fintype ι]

theorem cfInner_sum_smul_sum_smul {u : ι → α → ℂ} (hu1 : ∀ p, cfInner (u p) (u p) = 1)
    (hu0 : ∀ p q, p ≠ q → cfInner (u p) (u q) = 0) (c d : ι → ℂ) :
    cfInner (∑ p, c p • u p) (∑ p, d p • u p) = ∑ p, c p * conj (d p) := by
  have hstep : ∀ p, cfInner (u p) (∑ q, d q • u q) = conj (d p) := by
    intro p
    rw [cfInner_sum_smul_right, Finset.sum_eq_single p]
    · rw [hu1 p, mul_one]
    · intro q _ hqp
      rw [hu0 p q (Ne.symm hqp), mul_zero]
    · intro hp
      exact absurd (Finset.mem_univ p) hp
  rw [cfInner_sum_smul_left]
  exact Finset.sum_congr rfl fun p _ => by rw [hstep p]

theorem repr_eq_cfInner_of_orthonormal {X : Type*} [Group X] [Fintype X]
    (b : Module.Basis ι ℂ (classFun X))
    (hb1 : ∀ p, cfInner ((b p : classFun X) : X → ℂ) ((b p : classFun X) : X → ℂ) = 1)
    (hb0 : ∀ p q, p ≠ q →
      cfInner ((b p : classFun X) : X → ℂ) ((b q : classFun X) : X → ℂ) = 0)
    (f : classFun X) (p : ι) :
    b.repr f p = cfInner (f : X → ℂ) ((b p : classFun X) : X → ℂ) := by
  have hexp : (f : X → ℂ) = ∑ q, (b.repr f q) • ((b q : classFun X) : X → ℂ) := by
    conv_lhs => rw [← b.sum_repr f]
    push_cast
    rfl
  rw [hexp, cfInner_sum_smul_left, Finset.sum_eq_single p]
  · rw [hb1 p, mul_one]
  · intro q _ hqp
    rw [hb0 q p hqp, mul_zero]
  · intro hp
    exact absurd (Finset.mem_univ p) hp

end Aux

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]

theorem IsCyclicTIPair.exists_isCyclicTIIsometry (h : IsCyclicTIPair W W1 W2) :
    ∃ σ : classFun ↥W →ₗ[ℂ] classFun G, IsCyclicTIIsometry W W1 W2 σ := by
  classical
  obtain ⟨η, hη00, hηZ, hηorth, -, hηind⟩ := h.exists_prodCharEta
  have := h.finite_left
  have := h.finite_right
  have : Finite (Irr ↥W1) := finite_coe_Irr
  have : Finite (Irr ↥W2) := finite_coe_Irr
  have : Fintype (Irr ↥W1 × Irr ↥W2) := Fintype.ofFinite _
  have hηcf : ∀ i j, η i j ∈ classFun G := fun i j =>
    mem_classFun_of_mem_span_Irr (mem_span_Irr_of_mem_virtualChars (hηZ i j))
  set ηCF : Irr ↥W1 → Irr ↥W2 → classFun G := fun i j => ⟨η i j, hηcf i j⟩ with hηCF
  have hηCFcoe : ∀ i j, ((ηCF i j : classFun G) : G → ℂ) = η i j := fun _ _ => rfl
  set σ := h.basisProdIrr.constr ℂ fun p : Irr ↥W1 × Irr ↥W2 => ηCF p.1 p.2 with hσdef
  have hσb : ∀ p : Irr ↥W1 × Irr ↥W2, σ (h.basisProdIrr p) = ηCF p.1 p.2 := fun p =>
    h.basisProdIrr.constr_basis ℂ _ p
  have hw1 : ∀ p : Irr ↥W1 × Irr ↥W2,
      cfInner ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ)
        ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ) = 1 := by
    intro p; rw [h.cfInner_basisProdIrr p p, if_pos rfl]
  have hw0 : ∀ p q : Irr ↥W1 × Irr ↥W2, p ≠ q →
      cfInner ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ)
        ((h.basisProdIrr q : classFun ↥W) : ↥W → ℂ) = 0 := by
    intro p q hpq; rw [h.cfInner_basisProdIrr p q, if_neg hpq]
  have hη1 : ∀ p : Irr ↥W1 × Irr ↥W2, cfInner (η p.1 p.2) (η p.1 p.2) = 1 := by
    intro p; rw [hηorth, if_pos ⟨rfl, rfl⟩]
  have hη0 : ∀ p q : Irr ↥W1 × Irr ↥W2, p ≠ q → cfInner (η p.1 p.2) (η q.1 q.2) = 0 := by
    intro p q hpq
    rw [hηorth, if_neg]
    exact fun hc => hpq (Prod.ext hc.1 hc.2)
  have hexpf : ∀ f : classFun ↥W, (f : ↥W → ℂ) =
      ∑ p : Irr ↥W1 × Irr ↥W2, (h.basisProdIrr.repr f p) •
        ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ) := by
    intro f
    conv_lhs => rw [← h.basisProdIrr.sum_repr f]
    push_cast
    rfl
  have hcoe : ∀ f : classFun ↥W, ((σ f : classFun G) : G → ℂ) =
      ∑ p : Irr ↥W1 × Irr ↥W2, (h.basisProdIrr.repr f p) • η p.1 p.2 := by
    intro f
    conv_lhs => rw [← h.basisProdIrr.sum_repr f, map_sum]
    push_cast
    exact Finset.sum_congr rfl fun p _ => by
      rw [map_smul, hσb p, Submodule.coe_smul, hηCFcoe]
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  ·
    intro f g
    rw [hcoe, hcoe, cfInner_sum_smul_sum_smul hη1 hη0]
    conv_rhs => rw [hexpf f, hexpf g]
    rw [cfInner_sum_smul_sum_smul hw1 hw0]
  ·
    intro f hf
    have hint : ∀ p : Irr ↥W1 × Irr ↥W2, ∃ n : ℤ, h.basisProdIrr.repr f p = (n : ℂ) := by
      intro p
      have hIrr : ((h.basisProdIrr p : classFun ↥W) : ↥W → ℂ) ∈ Irr ↥W := by
        rw [h.coe_basisProdIrr_apply p]
        exact h.prodChar_mem_Irr p.1.2 p.2.2
      obtain ⟨n, hn⟩ := (mem_span_Irr_iff_forall_exists_int_cfInner f.2).1
        (mem_span_Irr_of_mem_virtualChars hf) _ hIrr
      exact ⟨n, by rw [repr_eq_cfInner_of_orthonormal _ hw1 hw0, hn]⟩
    choose n hn using hint
    rw [hcoe]
    refine Submodule.sum_mem _ fun p _ => ?_
    rw [hn p, Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (hηZ p.1 p.2)
  ·
    refine Subtype.ext ?_
    rw [← h.basisProdIrr_principal, hσb, hηCFcoe, coe_principalClassFun, hη00]
  ·
    intro f hf0
    set D := cyclicTIDiff W W1 W2
    obtain ⟨fd, hfd⟩ : ∃ fd : dadeDomain W D, (fd : ↥W → ℂ) = (f : ↥W → ℂ) :=
      ⟨⟨(f : ↥W → ℂ), mem_dadeDomain.2 ⟨f.2, hf0⟩⟩, rfl⟩
    have hfdeq : Submodule.inclusion (dadeDomain_le_classFun W D) fd = f :=
      Subtype.ext (by rw [Submodule.coe_inclusion, hfd])
    have hkey :
        (classFun G).subtype.comp
            (σ.comp (Submodule.inclusion (dadeDomain_le_classFun W D))) =
          (InducedCharacterConstruction.indClassFunₗ W).comp (dadeDomain W D).subtype := by
      refine h.basisProdCharAlpha.ext fun p => ?_
      have hincl : Submodule.inclusion (dadeDomain_le_classFun W D)
          (h.basisProdCharAlpha p) = h.prodCharAlphaCF p.1.1 p.2.1 :=
        Subtype.ext (by
          rw [Submodule.coe_inclusion, h.coe_basisProdCharAlpha_apply p, h.coe_prodCharAlphaCF])
      simp only [LinearMap.comp_apply, Submodule.coe_subtype, hincl,
        InducedCharacterConstruction.indClassFunₗ_apply]
      rw [h.coe_basisProdCharAlpha_apply p,
        NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq,
        hηind p.1.1 p.1.2 p.2.1 p.2.2, h.prodCharAlphaCF_eq, map_add, map_sub, map_sub,
        hσb, hσb, hσb, hσb]
      push_cast [hηCFcoe, hη00]
      ring
    have hres := congrArg (fun T : dadeDomain W D →ₗ[ℂ] (G → ℂ) => T fd) hkey
    simp only [LinearMap.comp_apply, Submodule.coe_subtype,
      InducedCharacterConstruction.indClassFunₗ_apply, hfdeq] at hres
    rw [hres, NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq, hfd]

theorem IsCyclicTIPair.exists_isCyclicTIIsometry' (h : IsCyclicTIPair W W1 W2) :
    ∃ σ : classFun ↥W →ₗ[ℂ] classFun G,
      (∀ f g : classFun ↥W,
        cfInner (σ f : G → ℂ) (σ g : G → ℂ) = cfInner (f : ↥W → ℂ) (g : ↥W → ℂ)) ∧
      (∀ f : classFun ↥W, (f : ↥W → ℂ) ∈ virtualChars ↥W → (σ f : G → ℂ) ∈ virtualChars G) ∧
      ((σ (principalClassFun ↥W) : classFun G) : G → ℂ) = 1 ∧
      (∀ f : classFun ↥W, (∀ x : ↥W, (x : G) ∉ cyclicTIDiff W W1 W2 → (f : ↥W → ℂ) x = 0) →
        (σ f : G → ℂ) = indClassFun W (f : ↥W → ℂ)) := by
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  refine ⟨σ, hσ.inner_eq, hσ.map_virtualChars, ?_, hσ.eq_indClassFun⟩
  rw [hσ.map_principalClassFun, coe_principalClassFun]

end CFSG.FeitThompson
