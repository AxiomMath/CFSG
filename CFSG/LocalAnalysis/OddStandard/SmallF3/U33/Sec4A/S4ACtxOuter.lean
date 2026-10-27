module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxSteps

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

section Outer

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

theorem ctx_outer_of (h : Ctx0 t L S x₁ x₂ lam rho)
    (ht : CtxTauFacts t L S x₁ x₂ lam rho tau) : CtxOuterFact t L tau := by
  intro γ hγ hγL hγ2
  have hτH : tau ∈ invCent t := h.le_invCent ht.tau_mem
  let a : ↥(invCent t) := ⟨tau, hτH⟩
  let b : ↥(invCent t) := ⟨γ, hγ⟩
  have ha2 : ctxConjHom h.hyp a * ctxConjHom h.hyp a = 1 := by
    rw [← map_mul, ctxConjHom_eq_one_iff]
    have hmem : tau * tau ∈ twoCore t := by
      rw [← pow_two]
      exact ht.tau_sq_mem
    exact hmem
  have ha' : ∀ k : ↥L, ctxConjHom h.hyp a ≠ MulAut.conj k := fun k hk =>
    ht.tau_not_mem ((ctxConjHom_inner_iff h.hyp a).mp ⟨k, hk⟩)
  have hb2 : ctxConjHom h.hyp b * ctxConjHom h.hyp b = 1 := by
    rw [← map_mul, ctxConjHom_eq_one_iff]
    have hmem : γ * γ ∈ twoCore t := by
      rw [← pow_two]
      exact hγ2
    exact hmem
  have hb' : ∀ k : ↥L, ctxConjHom h.hyp b ≠ MulAut.conj k := fun k hk =>
    hγL ((ctxConjHom_inner_iff h.hyp b).mp ⟨k, hk⟩)
  obtain ⟨k, hk⟩ := outer_invol_conj_of_psu33 (K := ↥L) h.hyp.lieModel ha2 ha' hb2 hb'
  have hkH : (k : G) ∈ invCent t := L_le_invCent h.hyp k.2
  have hkτ : (k : G) * tau * (k : G)⁻¹ ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).mul_mem hkH hτH) ((invCent t).inv_mem hkH)
  let c : ↥(invCent t) := ⟨(k : G) * tau * (k : G)⁻¹, hkτ⟩
  have hbc : ctxConjHom h.hyp b = ctxConjHom h.hyp c := by
    have hc : c = (⟨(k : G), hkH⟩ : ↥(invCent t)) * a * (⟨(k : G), hkH⟩ : ↥(invCent t))⁻¹ :=
      Subtype.ext rfl
    rw [hk, hc, map_mul, map_mul, map_inv, ctxConjHom_coe h.hyp k]
  have hq := (ctxConjHom_eq_iff h.hyp b c).mp hbc
  obtain ⟨q, hqP, hγeq⟩ : ∃ q ∈ twoCore t, γ = ((k : G) * tau * (k : G)⁻¹) * q⁻¹ :=
    ⟨γ⁻¹ * ((k : G) * tau * (k : G)⁻¹), hq, by group⟩
  have hcomm : q⁻¹ * (k : G) = (k : G) * q⁻¹ :=
    twoCore_commute h.hyp _ ((twoCore t).inv_mem hqP) _ k.2
  have hkq : (k : G)⁻¹ * q⁻¹ * (k : G) = q⁻¹ := by
    calc (k : G)⁻¹ * q⁻¹ * (k : G) = (k : G)⁻¹ * (q⁻¹ * (k : G)) := by group
      _ = (k : G)⁻¹ * ((k : G) * q⁻¹) := by rw [hcomm]
      _ = q⁻¹ := by group
  refine ⟨(k : G)⁻¹, (invCent t).inv_mem hkH, tau * q⁻¹ * tau⁻¹,
    twoCore_conj_mem t hτH ((twoCore t).inv_mem hqP), ?_⟩
  calc (k : G)⁻¹ * γ * ((k : G)⁻¹)⁻¹
      = (k : G)⁻¹ * (((k : G) * tau * (k : G)⁻¹) * q⁻¹) * (k : G) := by
        rw [← hγeq]
        group
    _ = tau * ((k : G)⁻¹ * q⁻¹ * (k : G)) := by group
    _ = tau * q⁻¹ := by rw [hkq]
    _ = (tau * q⁻¹ * tau⁻¹) * tau := by group

end Outer

end S4A

theorem ctxOuter_holds : CtxOuterStmt :=
  fun h _ _ ht => S4A.ctx_outer_of h ht

end CFSG.OddStandard.SmallF3.HarrisU33
