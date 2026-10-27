module

public import CFSG.FeitThompson.Representations.ClassFunctionInnerProductNorms
import CFSG.FeitThompson.Representations.ComplexCompleteReducibility
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Representation

noncomputable section

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def restrictIntertwiningMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (μ : Subrepresentation ρ) :
    μ.toRepresentation.IntertwiningMap σ where
  toLinearMap := f.toLinearMap ∘ₗ μ.toSubmodule.subtype
  isIntertwining' g := by
    ext x
    exact f.isIntertwining ρ σ g (x : V)

@[simp]
theorem restrictIntertwiningMap_apply {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (f : ρ.IntertwiningMap σ) (μ : Subrepresentation ρ) (x : μ.toSubmodule) :
    restrictIntertwiningMap f μ x = f (x : V) := (rfl)

theorem toSubmodule_bot (ρ : Representation ℂ G V) :
    (⊥ : Subrepresentation ρ).toSubmodule = ⊥ :=
  Submodule.toSubMulAction_inj.mp rfl

theorem exists_isCompl_equiv_of_isIrreducible [Finite G] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) :
    ∃ σ τ : Subrepresentation (leftRegular ℂ G),
      IsCompl σ τ ∧ Nonempty (σ.toRepresentation.Equiv ρ) := by
  have := hρ
  have hV : Nontrivial V :=
    (Submodule.nontrivial_iff ℂ).mp (nontrivial_of_ne _ _
      (Subrepresentation.toSubmodule_injective.ne (bot_ne_top (α := Subrepresentation ρ))))
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  set f : (leftRegular ℂ G).IntertwiningMap ρ := ρ.leftRegularMapEquiv.symm v with hf
  have hf1 : f (MonoidAlgebra.single 1 1) = v := by
    rw [hf, Representation.leftRegularMapEquiv_symm_single]; simp
  have hf0 : f ≠ 0 := fun h => hv (by rw [h] at hf1; exact hf1.symm)
  have hsurj : Function.Surjective f := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf0
  have hss : (leftRegular ℂ G).IsSemisimpleRepresentation :=
    isSemisimpleRepresentation_complex (leftRegular ℂ G)
  obtain ⟨σ, hcompl⟩ := exists_isCompl (Representation.IntertwiningMap.ker _ _ f)
  refine ⟨σ, Representation.IntertwiningMap.ker _ _ f, hcompl.symm, ⟨?_⟩⟩
  refine (restrictIntertwiningMap f σ).ofBijective ⟨?_, ?_⟩
  ·
    intro x y hxy
    have hker : (x : MonoidAlgebra ℂ G) - y ∈
        (Representation.IntertwiningMap.ker _ _ f).toSubmodule := by
      rw [Representation.IntertwiningMap.ker_toSubmodule, LinearMap.mem_ker]
      simpa using sub_eq_zero.2 (by simpa using hxy)
    have hmem : (x : MonoidAlgebra ℂ G) - y ∈
        (σ ⊓ Representation.IntertwiningMap.ker _ _ f).toSubmodule := by
      rw [Subrepresentation.toSubmodule_inf]; exact ⟨sub_mem x.2 y.2, hker⟩
    rw [hcompl.symm.inf_eq_bot, toSubmodule_bot, Submodule.mem_bot] at hmem
    exact Subtype.ext (sub_eq_zero.1 hmem)
  ·
    intro w
    obtain ⟨x, rfl⟩ := hsurj w
    have hx : x ∈ (σ ⊔ Representation.IntertwiningMap.ker _ _ f).toSubmodule := by
      rw [hcompl.symm.sup_eq_top]; trivial
    rw [Subrepresentation.toSubmodule_sup, Submodule.mem_sup] at hx
    obtain ⟨s, hs, t, ht, rfl⟩ := hx
    refine ⟨⟨s, hs⟩, ?_⟩
    have ht0 : f t = 0 := by
      rw [Representation.IntertwiningMap.ker_toSubmodule, LinearMap.mem_ker] at ht
      simpa using ht
    simp [ht0]

theorem finiteDimensional_of_isIrreducible [Finite G] (ρ : Representation ℂ G V)
    (hρ : ρ.IsIrreducible) : FiniteDimensional ℂ V := by
  obtain ⟨σ, -, -, ⟨e⟩⟩ := exists_isCompl_equiv_of_isIrreducible ρ hρ
  have : FiniteDimensional ℂ (MonoidAlgebra ℂ G) := inferInstance
  have : FiniteDimensional ℂ σ.toSubmodule := inferInstance
  exact e.toLinearEquiv.finiteDimensional

def charBilinForm (G : Type*) [Group G] [Fintype G] : LinearMap.BilinForm ℂ (G → ℂ) :=
  LinearMap.mk₂ ℂ (fun f h => ∑ g : G, f g * h g⁻¹)
    (fun f₁ f₂ h => by simp [add_mul, Finset.sum_add_distrib])
    (fun c f h => by simp [Finset.mul_sum, mul_assoc])
    (fun f h₁ h₂ => by simp [mul_add, Finset.sum_add_distrib])
    (fun c f h => by simp [Finset.mul_sum]; ring_nf; simp [mul_comm])

theorem charBilinForm_apply [Fintype G] (f h : G → ℂ) :
    charBilinForm G f h = ∑ g : G, f g * h g⁻¹ := (rfl)

theorem fdRepCharacter_eq (X : FDRep ℂ G) : FDRep.character X = Representation.character X.ρ :=
  (rfl)

theorem charBilinForm_eq_zero_of_ne [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ irrChar ℂ G) (hψ : ψ ∈ irrChar ℂ G) (hne : χ ≠ ψ) :
    charBilinForm G χ ψ = 0 := by
  obtain ⟨X, hX, rfl⟩ := mem_irrChar.1 hχ
  obtain ⟨Y, hY, rfl⟩ := mem_irrChar.1 hψ
  rw [fdRepCharacter_eq] at hne ⊢
  rw [fdRepCharacter_eq] at hne ⊢
  have := hX
  have := hY
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hc
  have key := Representation.char_orthonormal (k := ℂ) X.ρ Y.ρ
  rw [if_neg (fun ⟨e⟩ => hne (Representation.char_iso e).symm)] at key
  rw [charBilinForm_apply]
  rcases mul_eq_zero.1 key with h | h
  · exact absurd h (inv_ne_zero hc)
  · exact h

theorem charBilinForm_self_ne_zero [Fintype G] {χ : G → ℂ} (hχ : χ ∈ irrChar ℂ G) :
    charBilinForm G χ χ ≠ 0 := by
  obtain ⟨X, hX, rfl⟩ := mem_irrChar.1 hχ
  rw [fdRepCharacter_eq]
  have := hX
  have hc : (Nat.card G : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_ne_zero]
  have : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hc
  have key := Representation.char_orthonormal (k := ℂ) X.ρ X.ρ
  rw [if_pos ⟨Representation.Equiv.refl _⟩] at key
  rw [charBilinForm_apply]
  intro h
  rw [h, mul_zero] at key
  exact one_ne_zero key.symm

theorem linearIndependent_irrChar [Finite G] :
    LinearIndependent ℂ (fun χ : irrChar ℂ G => (χ : G → ℂ)) := by
  have : Fintype G := Fintype.ofFinite G
  exact LinearMap.BilinForm.linearIndependent_of_iIsOrtho (B := charBilinForm G)
    (fun χ ψ hne => charBilinForm_eq_zero_of_ne χ.2 ψ.2 fun h => hne (Subtype.ext h))
    (fun χ => charBilinForm_self_ne_zero χ.2)

theorem finite_irrChar [Finite G] : (irrChar ℂ G).Finite := by
  have : Fintype G := Fintype.ofFinite G
  exact linearIndependent_irrChar.setFinite

theorem Irr_eq_irrChar (G : Type*) [Group G] : Irr G = irrChar ℂ G :=
  Set.ext fun _ => mem_Irr.trans mem_irrChar.symm

theorem finite_Irr [Finite G] : (Irr G).Finite := by
  rw [Irr_eq_irrChar]
  exact finite_irrChar

end

end CFSG.FeitThompson
