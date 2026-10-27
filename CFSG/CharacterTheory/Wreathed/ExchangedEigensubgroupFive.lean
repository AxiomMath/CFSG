module

public import CFSG.CharacterTheory.Wreathed.ExchangedEigensubgroupFiveSupport

public section

namespace CFSG.Wreathed.ExchangedEigensubgroupFive

open CFSG.Semidihedral CFSG.Semidihedral.ExchangedEigensubgroups

universe u v w

variable {R : Type u} [CommGroup R]

theorem exchanged_eigensubgroup_projective_injection_forces_defining_square_order_including_five
    [Finite R] [Nontrivial R] {F : Type v} [Field F]
    {J : Type w} [Group J] [Finite J] [Group.IsPerfect J]
    {p ell f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hell : ell.Prime) (hellodd : Odd ell)
    (hf : 1 ≤ f) (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (β : J →* Matrix.SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F)
    (ρ : J →* MulAut R) (hinv : ∀ r : R, ρ t r = r⁻¹) (hR : IsPGroup ell R)
    (α : MulAut R) (hα : α ^ 2 = 1) (d : J)
    (hexchange : ρ d * α * (ρ d)⁻¹ = ρ t * α)
    (ι : positiveGroup α →* OddProjectiveCoverKernel.S F) (hι : Function.Injective ι) :
    ell = p ∧
      (positiveGroup α).IsComplement' (positiveGroup (ρ t * α)) ∧
      CFSG.IsElementaryAbelian p (positiveGroup α) ∧
      CFSG.IsElementaryAbelian p (positiveGroup (ρ t * α)) ∧
      (∃ e : positiveGroup α × positiveGroup (ρ t * α) ≃* R,
        ∀ r, e r = (r.1 : R) * r.2) ∧
      ∃ hwhole : CFSG.IsElementaryAbelian p R,
        letI : Fact p.Prime := ⟨hp⟩
        letI : CFSG.IsElementaryAbelian p R := hwhole
        Nat.card (positiveGroup α) = p ^ f ∧
          Nat.card (positiveGroup (ρ t * α)) = p ^ f ∧
          Nat.card R = (p ^ f) ^ 2 ∧
          (∃ P : Sylow p (OddProjectiveCoverKernel.S F), (P : Subgroup _) = ι.range) ∧
          Module.finrank (ZMod p) (Additive R) = 2 * f ∧
          Representation.IsIrreducible
            (ElementaryActionTransport.primeFieldRepresentation (p := p) ρ) ∧
          ρ.ker = β.ker ∧
          (∀ A : Subgroup R, (∀ j : J, ∀ r : R, r ∈ A → ρ j r ∈ A) → A = ⊥ ∨ A = ⊤) ∧
          ∃ σ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut R,
            Function.Injective σ ∧ σ.comp β = ρ ∧
            (∀ (j : J) (r : R), σ (β j) r = ρ j r) ∧
            Function.Injective (ElementaryActionTransport.primeFieldAction (p := p) σ) ∧
            (ElementaryActionTransport.primeFieldAction (p := p) σ).comp β =
              ElementaryActionTransport.primeFieldAction (p := p) ρ := by
  have hchar : ell = p := by
    rcases hq.lt_or_eq with hq' | hq'
    · exact eigengroups_characteristic_eq hp hpodd hell hellodd hf hF hq'
        β hβ hcentral hodd t ht htorder htβ ρ hinv hR α hα d hexchange ι hι
    · exact eigengroups_characteristic_eq_five hp hpodd hell hellodd hf hF hq'.symm
        ρ t hinv hR α hα d hexchange ι hι
  have hRdef : IsPGroup p R := hchar ▸ hR
  have hoddR := odd_card_of_odd_prime_group hell hellodd hR
  rw [← negativeGroup_eq_twisted_fixed ρ t hinv α]
  obtain ⟨hplus, hminus, hwhole, hdim, hpluscard, hminuscard, hwholecard,
      hSylow, hirr, hker, hinvariant⟩ :=
    eigengroups_defining_full_dimension_and_kernel hp hpodd hf hF hq
      β hβ hcentral hodd t ht htorder htβ ρ hinv hRdef α hα d hexchange ι hι
  refine ⟨hchar, eigengroups_isComplement hoddR α hα, hplus, hminus,
    ⟨eigenProductEquiv hoddR α hα, eigenProductEquiv_apply hoddR α hα⟩, hwhole, ?_⟩
  let : Fact p.Prime := ⟨hp⟩
  let : CFSG.IsElementaryAbelian p R := hwhole
  have hsquare : Nat.card R = (p ^ f) ^ 2 := by
    rw [hwholecard, ← pow_mul, Nat.mul_comm f 2]
  let σ := ElementaryActionTransport.descendedOriginalAction β hβ ρ hker.ge
  have hσ : Function.Injective σ :=
    ElementaryActionTransport.descendedOriginalAction_injective β hβ ρ hker.ge hker
  have hσcomp : σ.comp β = ρ :=
    ElementaryActionTransport.descendedOriginalAction_comp β hβ ρ hker.ge
  refine ⟨hpluscard, hminuscard, hsquare, hSylow, hdim, hirr, hker, hinvariant,
    σ, hσ, hσcomp, ElementaryActionTransport.descendedOriginalAction_apply_element
      β hβ ρ hker.ge, ?_, ?_⟩
  · exact (ElementaryActionTransport.autToGL_injective (p := p)).comp hσ
  · apply MonoidHom.ext
    intro j
    change ElementaryActionTransport.autToGL (p := p) (σ (β j)) =
      ElementaryActionTransport.autToGL (p := p) (ρ j)
    exact congrArg (ElementaryActionTransport.autToGL (p := p))
      (DFunLike.congr_fun hσcomp j)

end CFSG.Wreathed.ExchangedEigensubgroupFive
