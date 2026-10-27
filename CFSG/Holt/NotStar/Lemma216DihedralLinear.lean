module

public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Holt.NotStar.CasesSupport

public section

namespace CFSG.Holt

open MulAction CFSG.Open
open scoped Pointwise

namespace NotStar216

open NotStarCases

section OutAbelian

variable {G : Type} [Group G]

omit [Group G] in
@[expose] def OutAbelian (X : Type*) [Group X] : Prop :=
  ∀ φ ψ : MulAut X, ∃ g : X, ∀ x : X, (φ * ψ * φ⁻¹ * ψ⁻¹) x = g * x * g⁻¹

theorem OutAbelian.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (hY : OutAbelian Y)
    (e : X ≃* Y) : OutAbelian X := by
  intro φ ψ
  obtain ⟨g, hg⟩ := hY (e.symm.trans (φ.trans e)) (e.symm.trans (ψ.trans e))
  refine ⟨e.symm g, fun x => e.injective ?_⟩
  have h := hg (e x)
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h
  simp only [MulAut.mul_apply, MulAut.inv_apply, map_mul, MulEquiv.apply_symm_apply]
  convert h using 2 <;> simp [MulEquiv.symm_trans_apply]

theorem outAbelian_psl2 (F : Type) [Field F] [Finite F] :
    OutAbelian (CFSG.GorensteinWalter.PSL2 F) := by
  intro φ ψ
  open CFSG.ComponentClassification.OuterAutomorphisms in
  have h := CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm F
    (QuotientGroup.mk φ) (QuotientGroup.mk ψ)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  have hn := (inner_normal (CFSG.GorensteinWalter.PSL2 F)).conj_mem _ h (φ * ψ)
  have h' : φ * ψ * φ⁻¹ * ψ⁻¹ ∈ inner (CFSG.GorensteinWalter.PSL2 F) := by
    have := inv_mem hn
    simpa [mul_assoc] using this
  obtain ⟨g, hg⟩ := h'
  exact ⟨g, fun x => by rw [← hg]; rfl⟩

end OutAbelian

end NotStar216

end CFSG.Holt
