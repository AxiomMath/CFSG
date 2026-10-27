module

public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinFrame
public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem
public import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth CFSG.LieType.Universal.Spin
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Restrict

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def hypPairToRestrict (P : HypPair Q) {S : Submodule F V} (he : P.e ∈ S)
    (hf : P.f ∈ S) : HypPair (Q.restrict S) where
  e := ⟨P.e, he⟩
  f := ⟨P.f, hf⟩
  Q_e := P.Q_e
  Q_f := P.Q_f
  polar_ef := by
    rw [polar_restrict]
    exact P.polar_ef

@[expose] def _root_.CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame.toRestrict
    (fr : OFrame Q) {S : Submodule F V} (h1 : fr.e₁ ∈ S)
    (h2 : fr.f₁ ∈ S) (h3 : fr.e₂ ∈ S) (h4 : fr.f₂ ∈ S) : OFrame (Q.restrict S) where
  P := hypPairToRestrict fr.P h1 h2
  P' := hypPairToRestrict fr.P' h3 h4
  orth :=
    { ee := by
        show polar (Q.restrict S) ⟨fr.e₁, h1⟩ ⟨fr.e₂, h3⟩ = 0
        rw [polar_restrict]
        exact fr.polar_e₁_e₂
      ef := by
        show polar (Q.restrict S) ⟨fr.e₁, h1⟩ ⟨fr.f₂, h4⟩ = 0
        rw [polar_restrict]
        exact fr.polar_e₁_f₂
      fe := by
        show polar (Q.restrict S) ⟨fr.f₁, h2⟩ ⟨fr.e₂, h3⟩ = 0
        rw [polar_restrict]
        exact fr.polar_f₁_e₂
      ff := by
        show polar (Q.restrict S) ⟨fr.f₁, h2⟩ ⟨fr.f₂, h4⟩ = 0
        rw [polar_restrict]
        exact fr.polar_f₁_f₂ }

end Restrict

section Compat

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  {S : Submodule F V} (fr : OFrame Q) {h1 : fr.e₁ ∈ S} {h2 : fr.f₁ ∈ S} {h3 : fr.e₂ ∈ S}
  {h4 : fr.f₂ ∈ S}

theorem coords_toRestrict (v : S) :
    (fr.toRestrict h1 h2 h3 h4).coords v = fr.coords (v : V) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Frame.coords_apply, Frame.toRestrict, hypPairToRestrict, polar_restrict]

theorem incl_toRestrict (X : Matrix (Fin 2) (Fin 2) F) :
    (((fr.toRestrict h1 h2 h3 h4).incl X : S) : V) = fr.incl X := by
  simp [Frame.incl_apply, Frame.toRestrict, hypPairToRestrict]

theorem La_toRestrict (A : SL(2, F)) (v : S) :
    (((fr.toRestrict h1 h2 h3 h4).La A v : S) : V) = fr.La A (v : V) := by
  rw [Frame.La_apply, Frame.La_apply, coords_toRestrict, Submodule.coe_add, incl_toRestrict]

end Compat

section Conj

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem OFrame.vectors_mem {fr : OFrame Q} {S : Submodule F V} (h : fr.span ≤ S) :
    fr.e₁ ∈ S ∧ fr.f₁ ∈ S ∧ fr.e₂ ∈ S ∧ fr.f₂ ∈ S := by
  refine ⟨h ⟨!![1, 0; 0, 0], ?_⟩, h ⟨!![0, 0; 0, 1], ?_⟩, h ⟨!![0, -1; 0, 0], ?_⟩,
    h ⟨!![0, 0; 1, 0], ?_⟩⟩
  · simp [Frame.incl_apply]
  · simp [Frame.incl_apply]
  · simp [Frame.incl_apply]
  · simp [Frame.incl_apply]

theorem exists_elemOn_conj [Finite F] [FiniteDimensional F V] (hodd : Odd (Nat.card F))
    {S : Submodule F V} (hS : PolarNondegOn Q S) (h6 : 6 ≤ Module.finrank F S)
    {fr fr' : OFrame Q} (hfr : fr.span ≤ S) (hfr' : fr'.span ≤ S) :
    ∃ h ∈ elemOn Q S, ∀ A : SL(2, F), fr'.La A = h * fr.La A * h⁻¹ := by
  have hQ₁ : (polarBilin (Q.restrict S)).Nondegenerate := nondegenerate_polarBilin_restrict hS
  obtain ⟨h1, h2, h3, h4⟩ := OFrame.vectors_mem hfr
  obtain ⟨h1', h2', h3', h4'⟩ := OFrame.vectors_mem hfr'
  have hodd2 : (2 : F) ≠ 0 :=
    CFSG.ClassicalInvolution.Models.OrthogonalPairs.IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero hodd2
  have : Nontrivial S := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  have hperp : 2 ≤ Module.finrank F (fr.toRestrict h1 h2 h3 h4).perp := by
    have := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four
      (fr.toRestrict h1 h2 h3 h4)
    omega
  obtain ⟨x₁, hx₁⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_spin_conj hodd hQ₁
    (fr.toRestrict h1 h2 h3 h4) (fr'.toRestrict h1' h2' h3' h4') hperp
  have hE : spinAction (Q.restrict S) x₁ ∈ elementaryGroup (Q.restrict S) :=
    range_spinAction_le_elementaryGroup hQ₁ (fr.toRestrict h1 h2 h3 h4).orth ⟨x₁, rfl⟩
  rw [← range_resHom] at hE
  obtain ⟨h, hh⟩ := hE
  refine ⟨h.1, h.2, fun A => ?_⟩
  have hinvS : ∀ z, (∀ x ∈ S, polar Q z x = 0) → h.1⁻¹ z = z := fun z hz => by
    have := (support_of_mem_elemOn (inv_mem h.2)).2 z hz
    exact this
  have hz0 : ∀ (fr₀ : OFrame Q), fr₀.span ≤ S → ∀ z, (∀ x ∈ S, polar Q z x = 0) →
      fr₀.coords z = 0 := by
    intro fr₀ hfr₀ z hz
    obtain ⟨a1, a2, a3, a4⟩ := OFrame.vectors_mem hfr₀
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Frame.coords_apply, hz _ a1, hz _ a2, hz _ a3, hz _ a4]
  refine eq_of_agree_on hQ₁ (fun r hr => ?_) (fun z hz => ?_) (fun z hz => ?_)
  ·
    have hA := hx₁ A
    have e1 := congrArg (fun L : S ≃ₗ[F] S => ((L ⟨r, hr⟩ : S) : V)) hA
    simp only [LinearEquiv.mul_apply] at e1
    rw [La_toRestrict, ← hh, coe_resHom, La_toRestrict] at e1
    have e2 : ((((resHom Q S) h)⁻¹ ⟨r, hr⟩ : S) : V) = (h.1)⁻¹ r := by
      rw [← map_inv, coe_resHom]
      rfl
    rw [e2] at e1
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact e1
  · exact Frame.La_apply_of_coords_eq_zero fr' A (hz0 fr' hfr' z hz)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinvS z hz,
      Frame.La_apply_of_coords_eq_zero fr A (hz0 fr hfr z hz)]
    exact (support_of_mem_elemOn h.2).2 z hz

end Conj

end CFSG.ClassicalInvolution.RouteD.TwinY
