module

public import CFSG.FeitThompson.Representations.ExtraspecialWeightCosetBasis
public import CFSG.FeitThompson.Representations.ExtraspecialAbelianNormalSqrtIndex
public import Mathlib.GroupTheory.SemidirectProduct
import CFSG.FeitThompson.Representations.DirectSumOfSubrepresentations
import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField
import CFSG.FeitThompson.Representations.ExtraspecialCentralCharacterUniqueness
import CFSG.FeitThompson.Foundations.CoprimeActionFittingFaithful

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Representation SemidirectProduct

universe u v w

variable {p : ℕ} {P : Type u} [Group P] {H : Type u} [Group H] {φ : H →* MulAut P}
  {k : Type v} [Field k] {V : Type w} [AddCommGroup V] [Module k V]

theorem natCard_ne_zero_of_isExtraspecial (hP : IsExtraspecial p P) (hp : (p : k) ≠ 0) :
    (Nat.card P : k) ≠ 0 := by
  obtain ⟨m, hm⟩ := hP.exists_card_eq_pow
  rw [hm]; push_cast; exact pow_ne_zero _ hp

noncomputable def quotientRangeInlMulEquiv (φ : H →* MulAut P)
    [(SemidirectProduct.inl (φ := φ)).range.Normal] :
    (P ⋊[φ] H) ⧸ (SemidirectProduct.inl (φ := φ)).range ≃* H :=
  (QuotientGroup.quotientMulEquivOfEq SemidirectProduct.range_inl_eq_ker_rightHom).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ rightHom_surjective)

@[simp]
theorem quotientRangeInlMulEquiv_mk [(SemidirectProduct.inl (φ := φ)).range.Normal]
    (x : P ⋊[φ] H) : quotientRangeInlMulEquiv φ (QuotientGroup.mk x) = rightHom x := (rfl)

theorem isCyclic_quotient_range_inl (φ : H →* MulAut P) [IsCyclic H]
    [(SemidirectProduct.inl (φ := φ)).range.Normal] :
    IsCyclic ((P ⋊[φ] H) ⧸ (SemidirectProduct.inl (φ := φ)).range) :=
  isCyclic_of_surjective (quotientRangeInlMulEquiv φ).symm
    (quotientRangeInlMulEquiv φ).symm.surjective

theorem isIrreducible_comp_inl (hP : IsExtraspecial p P) [Finite H] [IsCyclic H] [IsAlgClosed k]
    (hp : (p : k) ≠ 0) {ρ : Representation k (P ⋊[φ] H) V} (hirr : ρ.IsIrreducible)
    (zeta : ↥(Subgroup.center P) →* kˣ) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V),
      ρ (SemidirectProduct.inl (z : P)) w = (zeta z : k) • w) :
    Representation.IsIrreducible (ρ.comp (SemidirectProduct.inl : P →* P ⋊[φ] H)) := by
  classical
  have hnormal : (SemidirectProduct.inl (φ := φ)).range.Normal := range_inl_normal
  have hcyc : IsCyclic ((P ⋊[φ] H) ⧸ (SemidirectProduct.inl (φ := φ)).range) :=
    isCyclic_quotient_range_inl φ
  have := hirr
  have hPfin := hP.finite
  have hfd : FiniteDimensional k V :=
    ExtraspecialWeight.finiteDimensional_of_isIrreducible hirr
  have hnt : Nontrivial V := nontrivial_of_isIrreducible ρ
  set ρP : Representation k P V := ρ.comp (SemidirectProduct.inl : P →* P ⋊[φ] H) with hρP
  obtain ⟨n, σ, hbij, hσirr⟩ :=
    exists_bijective_coeLinearMap_isIrreducible (natCard_ne_zero_of_isExtraspecial hP hp) ρP
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      subst h
      have hsup : (⨆ i : Fin 0, (σ i).toSubmodule) = ⊤ :=
        DirectSum.IsInternal.submodule_iSup_eq_top (A := fun i : Fin 0 => (σ i).toSubmodule) hbij
      rw [iSup_of_empty] at hsup
      exact bot_ne_top hsup
    · exact h
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  have hzσ : ∀ (i : Fin n) (z : ↥(Subgroup.center P)) (x : ((σ i).toSubmodule : Type w)),
      (σ i).toRepresentation (z : P) x = (zeta z : k) • x := fun i z x =>
    Subtype.ext (hz z (x : V))
  obtain ⟨N, B, -, -, -, hZB, -, hPB, hBZ, hCB⟩ := hP.exists_abelian_normal_polarization
  have hEquiv : ∀ i : Fin n, Nonempty ((σ i).toRepresentation.Equiv (σ i₀).toRepresentation) :=
    fun i => ExtraspecialWeight.nonempty_equiv_of_centerChar hP hZB hCB hPB hBZ hp
      (hσirr i) (hσirr i₀) zeta hzeta (hzσ i) (hzσ i₀)
  exact isIrreducible_comp_of_homogeneous_of_isCyclic_quotient
    (SemidirectProduct.inl : P →* P ⋊[φ] H) SemidirectProduct.inl_injective hirr (hσirr i₀)
    ((equivOfIsInternal σ hbij).symm.trans (directSumEquivCongr fun i => (hEquiv i).some))

theorem exists_finrank_eq_pow (hP : IsExtraspecial p P) [IsAlgClosed k] (hp : (p : k) ≠ 0)
    {ρ : Representation k (P ⋊[φ] H) V}
    (hirrP : Representation.IsIrreducible (ρ.comp (SemidirectProduct.inl : P →* P ⋊[φ] H)))
    (zeta : ↥(Subgroup.center P) →* kˣ) (hzeta : zeta ≠ 1)
    (hz : ∀ (z : ↥(Subgroup.center P)) (w : V),
      ρ (SemidirectProduct.inl (z : P)) w = (zeta z : k) • w) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card P = p ^ (2 * n + 1) ∧ Module.finrank k V = p ^ n := by
  obtain ⟨n, B, hn1, -, -, hZB, hcard, hPB, -, hCB⟩ := hP.exists_abelian_normal_polarization
  refine ⟨n, hn1, hcard, ?_⟩
  exact ExtraspecialWeight.finrank_eq_pow hP hZB hCB hPB hp hirrP zeta hzeta hz

end

end CFSG.FeitThompson
