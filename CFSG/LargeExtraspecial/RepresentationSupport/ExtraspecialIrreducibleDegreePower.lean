module

public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialIrreducibleMatrixBasis
public import CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot

public section

namespace CFSG.LargeExtraspecial

namespace RepresentationSupport

namespace ExtraspecialIrreducibleDegreePower

theorem exists_degree {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {q : ℕ} (hq : q.Prime)
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup q E)
    (σ : Representation F E W) (hfaith : Function.Injective σ) (hσ : σ.IsIrreducible) :
    ∃ d : ℕ, 0 < d ∧ Module.finrank F W = q ^ d ∧ Nat.card E = q ^ (1 + 2 * d) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨χ, hχ, hscalar⟩ := CFSG.LinearAlgebra.CoprimeActions.IrreducibleCentralCharacter.exists_character σ hfaith hσ
  let r : E ⧸ Subgroup.center E → E := fun a => Quotient.out a
  have hr : ∀ a, (QuotientGroup.mk (r a) : E ⧸ Subgroup.center E) = a := fun a => Quotient.out_eq' a
  obtain ⟨b, -⟩ := ExtraspecialIrreducibleMatrixBasis.exists_basis hq hE σ hσ χ hχ hscalar r hr
  have h1 : Module.finrank F (Module.End F W) = Nat.card (E ⧸ Subgroup.center E) := by
    rw [Module.finrank_eq_nat_card_basis b]
  have h5 : Module.finrank F (Module.End F W) = Module.finrank F W * Module.finrank F W :=
    Module.finrank_linearMap F F W W
  have hQp : IsPGroup q (E ⧸ Subgroup.center E) := hE.1.to_quotient _
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q) (G := E ⧸ Subgroup.center E)).1 hQp
  have hN : (Module.finrank F W) ^ 2 = q ^ m := by
    rw [sq, ← h5, h1, hm]
  obtain ⟨d, hd, hNd⟩ := CFSG.GroupTheory.CoprimeActionSupport.PrimePowerSquareRoot.exists_exponent hq hN
  have h2 : Nat.card E = Nat.card (E ⧸ Subgroup.center E) * Nat.card (Subgroup.center E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card (Subgroup.center E) = q := hE.2.2.2
  refine ⟨d, ?_, hNd, ?_⟩
  · rcases Nat.eq_zero_or_pos d with rfl | hpos
    · exfalso
      simp only [mul_zero] at hd
      subst hd
      have hone : Nat.card (E ⧸ Subgroup.center E) = 1 := by rw [hm]; simp
      have htop : Subgroup.center E = ⊤ := by
        have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center E)
        rw [hone, one_mul] at this
        exact (Subgroup.card_eq_iff_eq_top _).1 this.symm
      have hcomm : commutator E = ⊥ := (commutator_eq_bot_iff_center_eq_top E).2 htop
      rw [hE.2.1, htop] at hcomm
      have hc1 : Nat.card (Subgroup.center E) = 1 := by
        rw [htop, hcomm]; simp
      rw [h3] at hc1
      exact hq.one_lt.ne' hc1
    · exact hpos
  · rw [h2, h3, hm, hd, pow_add, pow_one]
    ring

end ExtraspecialIrreducibleDegreePower

end RepresentationSupport

end CFSG.LargeExtraspecial
