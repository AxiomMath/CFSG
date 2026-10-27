module

public import CFSG.ClassicalInvolution.RouteD.TWT9Frame
public import CFSG.ClassicalInvolution.RouteD.TWT9Cls
public import CFSG.ClassicalInvolution.RouteD.TWT8V
public import CFSG.ClassicalInvolution.RouteD.TWEB6Sign
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

namespace CFSG.ClassicalInvolution.RouteD.TWT9

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TWE.B6
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ClassicalInvolution.RouteD.TWE.B4 (mem_negSpace_iff' mem_posSpace_iff')
open CFSG.ClassicalInvolution.RouteD.TWT8 (BridgeOmega)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

set_option linter.unusedSectionVars false

section Spin

open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)

variable {p f : ℕ} [Fact p.Prime]

local notation "𝔔" => quadMinus 4 (GaloisField p f) (Prod.fst (minusCoeffs p f))
  (Prod.snd (minusCoeffs p f))

local notation "𝔽" => GaloisField p f

local notation "𝕍" => Vm 4 (GaloisField p f)

theorem isometry_fixes_of_commute (hodd : Odd (Nat.card 𝔽)) {h : 𝕍 ≃ₗ[𝔽] 𝕍}
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hh2 : h * h = 1)
    (hhdim : Module.finrank 𝔽 (negSpace h) = 2) {L : Subgroup (𝕍 ≃ₗ[𝔽] 𝕍)}
    {s : 𝕍 ≃ₗ[𝔽] 𝕍} (hL : IsFundamental 𝔔 L s) (hc : ∀ l ∈ L, h * l = l * h) :
    ∀ x ∈ negSpace s, h x = x := by
  have h2 : (2 : 𝔽) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨ε', hε', he⟩ := sign_of_commute h2 hL hhO hh2 hc
  rcases hε' with rfl | rfl
  · intro x hx
    simpa using he x hx
  · exfalso
    have hle : negSpace s ≤ negSpace h := fun x hx =>
      mem_negSpace_iff'.mpr (by rw [he x hx]; simp)
    have h4 := Submodule.finrank_mono hle
    rw [finrank_negSpace hodd hL, hhdim] at h4
    omega

theorem class_spin_td4a (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {𝓕 : Set (Subgroup (spinGroup 𝔔))}
    (cq : CentralQuot (spinAction 𝔔) 𝓕 (fundSet 𝔔) (scalars 𝔽 𝕍))
    {g₀ h : 𝕍 ≃ₗ[𝔽] 𝕍} (hgO : g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hg2 : g₀ * g₀ = 1)
    (hhO : h ∈ TauCeti.QuadraticMap.orthogonalGroup 𝔔) (hh2 : h * h = 1)
    {RM RJ RN : Subgroup (spinGroup 𝔔)} (hRJ : RJ ∈ 𝓕) (hRN : RN ∈ 𝓕)
    (FM : OFrame 𝔔) (hFM : RM.map (spinAction 𝔔) = FM.La.range)
    (hfixM : ∀ l ∈ RM.map (spinAction 𝔔), g₀ * l = l * g₀)
    (hfixN : ∀ l ∈ RN.map (spinAction 𝔔), g₀ * l = l * g₀)
    (hnormJ : ∀ l ∈ RJ.map (spinAction 𝔔), g₀ * l * g₀ ∈ RJ.map (spinAction 𝔔))
    {x₀ : spinGroup 𝔔} (hx₀J : x₀ ∈ RJ) (hx₀1 : x₀ ≠ 1) (hx₀p : x₀ ^ p = 1)
    (hx₀inv : ∀ v, g₀ (spinAction 𝔔 x₀ v) = (spinAction 𝔔 x₀).symm (g₀ v))
    (hhneg : negSpace h ≤ FM.span) (hhdim : Module.finrank 𝔽 (negSpace h) = 2)
    (hJh : ∀ l ∈ RJ.map (spinAction 𝔔), h * l = l * h)
    (hNh : ∀ l ∈ RN.map (spinAction 𝔔), h * l = l * h)
    (haniso : ∀ y ∈ FM.span, h y = y → y ≠ 0 → 𝔔 y ≠ 0) :
    ∃ (x' : spinGroup 𝔔) (ε : 𝔽), (ε = 1 ∨ ε = -1) ∧
      RJ = ((rootSL2 (minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom) ∧
      ∀ y, polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            true)) y = 0 →
        polar 𝔔 (spinAction 𝔔 x'
          ((minusFrame 4 (minusCoeffs p f).1 (minusCoeffs p f).2).toHypFrame.vec ⟨0, by omega⟩
            false)) y = 0 →
        g₀ y = ε • y := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have h2 : (2 : 𝔽) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hodd : Odd (Nat.card 𝔽) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have : Invertible (2 : 𝔽) := invertibleOfNonzero h2
  have hdim8 : Module.finrank 𝔽 𝕍 = 8 := by
    rw [finrank_minus p f 4 (by omega)]
  have hiMf : IsFundamental 𝔔 (RM.map (spinAction 𝔔)) (FM.La (-1)) := by
    rw [hFM]
    exact IsFundamental.of_frame FM
  obtain ⟨εM, hεM, hgM⟩ := sign_of_commute h2 hiMf hgO hg2 hfixM
  have hgM' : ∀ x ∈ FM.span, g₀ x = εM • x := fun x hx =>
    hgM x (by rw [negSpace_La_neg_one h2]; exact hx)
  obtain ⟨FJ, π', ρ', hFJ, hπρ', hsup', hgπ', hgρ'⟩ := leaf_planes_td4 hp2 hq cq hgO hg2 hRJ
    hnormJ hx₀J hx₀1 hx₀p hx₀inv hεM
  have hiJf : IsFundamental 𝔔 (RJ.map (spinAction 𝔔)) (FJ.La (-1)) := by
    rw [hFJ]
    exact IsFundamental.of_frame FJ
  have hJspan : ∀ x ∈ FJ.span, h x = x := fun x hx =>
    isometry_fixes_of_commute hodd hhO hh2 hhdim hiJf hJh x
      (by rw [negSpace_La_neg_one h2]; exact hx)
  have hρ'h : ∀ x ∈ hypPlane ρ', h x = x := fun x hx =>
    hJspan x (by rw [← hsup']; exact Submodule.mem_sup_right hx)
  obtain ⟨s, hs⟩ := cq.map_mem _ hRN
  obtain ⟨εN, hεN, hgN⟩ := sign_of_commute h2 hs hgO hg2 hfixN
  have hperp := eq_smul_of_perp_td4a h2 hdim8 hgO hg2 hh2 FM.finrank_span hεM hgM' hhneg hhdim
    π' ρ' hgπ' hgρ' hρ'h (finrank_negSpace hodd hs) hεN hgN
    (isometry_fixes_of_commute hodd hhO hh2 hhdim hs hNh) haniso
  obtain ⟨x', hx'RJ, hx'⟩ := adapted_frame_td4 hp2 hq cq hRJ hFJ hπρ' hsup' hperp
  exact ⟨x', εM, hεM, hx'RJ, hx'⟩

end Spin

end CFSG.ClassicalInvolution.RouteD.TWT9
