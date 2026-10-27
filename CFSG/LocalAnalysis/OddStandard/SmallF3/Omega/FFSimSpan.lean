module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Sim
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_span_nonsingular (hQ : Q.Nondegenerate) :
    Submodule.span (ZMod 3) {u : V | Q u ≠ 0} = ⊤ := by
  haveI : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  obtain ⟨b, -, haniso⟩ := hQ.exists_orthogonal_basis
  rw [eq_top_iff, ← b.span_eq]
  apply Submodule.span_mono
  rintro u ⟨i, rfl⟩
  exact haniso i

theorem ff_eq_smul_of_eigen (hQ : Q.Nondegenerate) {γ : V ≃ₗ[ZMod 3] V} {c : ZMod 3}
    (hc : ∀ u : V, Q u ≠ 0 → γ u = c • u) (v : V) : γ v = c • v := by
  have hmap : (γ : V →ₗ[ZMod 3] V) = c • (LinearMap.id : V →ₗ[ZMod 3] V) := by
    apply LinearMap.ext_on (ff_span_nonsingular hQ)
    intro u hu
    simpa using hc u hu
  simpa using congrArg (fun f : V →ₗ[ZMod 3] V => f v) hmap

theorem ff_mk_eq_one_of_smul (h0 : 0 < Module.finrank (ZMod 3) V) (γ : simGroup Q)
    {c : ZMod 3} (hc : ∀ v : V, (γ : V ≃ₗ[ZMod 3] V) v = c • v) :
    (QuotientGroup.mk γ : ProjSim Q) = 1 := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos h0
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hc0 : c ≠ 0 := by
    intro hc_eq
    apply hv0
    apply (γ : V ≃ₗ[ZMod 3] V).injective
    rw [map_zero, hc v0, hc_eq, zero_smul]
  have hcpm : c = 1 ∨ c = -1 := by
    rcases aux_unit_eq_one_or_neg_one (Units.mk0 c hc0) with h | h
    · left
      simpa using congrArg Units.val h
    · right
      simpa using congrArg Units.val h
  rw [QuotientGroup.eq_one_iff, mem_piSim_iff]
  rcases hcpm with hc1 | hcm1
  · left
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [hc v, hc1, one_smul]
    simp
  · right
    apply Subtype.ext
    rw [coe_orthToSim]
    apply LinearEquiv.ext
    intro v
    rw [hc v, hcm1, neg_one_smul]
    exact (coe_piOrth_apply v).symm

end CFSG.OddStandard.SmallF3.Omega
