module

public import CFSG.ClassicalInvolution.RouteD.TWT9Class
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.RouteD.TWU

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (mem_negSpace_iff' eq_self_of_perp_plane)
open CFSG.ClassicalInvolution.RouteD.TWT9 (leaf_planes_td4 adapted_frame_td4)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝔔" => quadMinus 4 (GaloisField p f) (Prod.fst (minusCoeffs p f))
  (Prod.snd (minusCoeffs p f))

local notation "𝔽" => GaloisField p f

local notation "𝕍" => Vm 4 (GaloisField p f)



theorem class_spin_td4c (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {g₀ : 𝕍 ≃ₗ[𝔽] 𝕍} (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hg2 : g₀ * g₀ = 1)
    {RM RJ : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕) (FM : OFrame 𝔔)
    (hFM : RM.map (spinAction 𝔔) = FM.La.range)
    (hfixM : ∀ l ∈ RM.map (spinAction 𝔔), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction 𝔔), g₀ * l * g₀ ∈ RJ.map (spinAction 𝔔))
    {x₀ : spinGroup 𝔔} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction 𝔔 x₀ v) = (spinAction 𝔔 x₀).symm (g₀ v))
    (hdim : Module.finrank 𝔽 (negSpace g₀) = 2) :
    ∃ (x' : spinGroup 𝔔),
      RJ = ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = y := by
  classical
  have h2 : (2 : 𝔽) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card 𝔽) := by
    obtain ⟨-, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hs₁ : IsFundamental 𝔔 (RM.map (spinAction 𝔔)) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hs₁ hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  have hε1 : εM = 1 := by
    rcases hεM with h | h
    · exact h
    · exfalso
      have hle : FM.span ≤ negSpace g₀ := fun x hx =>
        mem_negSpace_iff'.mpr (by rw [hgM' x hx, h]; simp)
      have h4 := Submodule.finrank_mono hle
      rw [FM.finrank_span, hdim] at h4
      omega
  obtain ⟨FJ, π', ρ', hFJ, hπρ', hsup', hgπ', hgρ'⟩ := leaf_planes_td4 hp2 hq cq hgO hg2 hRJ
    hnormJ hx₀J hx₀1 hx₀p hx₀inv hεM
  rw [hε1] at hgπ'
  have hπle : hypPlane π' ≤ negSpace g₀ := fun x hx =>
    mem_negSpace_iff'.mpr (by simpa using hgπ' x hx)
  have hneg : negSpace g₀ = hypPlane π' :=
    (Submodule.eq_of_le_of_finrank_eq hπle (by rw [finrank_hypPlane, hdim])).symm
  have hperp : ∀ y, y ∈ π'.perp → g₀ y = εM • y := fun y hy => by
    rw [hε1, one_smul]
    exact eq_self_of_perp_plane h2 hgO hg2 π' hneg hy
  obtain ⟨x', hx'RJ, hx'⟩ := adapted_frame_td4 hp2 hq cq hRJ hFJ hπρ' hsup' hperp
  exact ⟨x', hx'RJ, fun y h₁ h₂ => by simpa [hε1] using hx' y h₁ h₂⟩

end Spin

end CFSG.ClassicalInvolution.RouteD.TWU
