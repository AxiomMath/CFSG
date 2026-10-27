module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6cOrbit
public import CFSG.CGT.PushingUpLit.BHS6.Conj
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.CGT.PushingUpLit.BHS6.SixThree
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreElevenB
public import CFSG.Quasithin.Background.B1MoreNineG

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}


local notation "Ω[" R "]" => CoreAssembly.conjClass (tightCore R)

@[expose] def V3AE6cPair (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y) (K₄ W : Subgroup Y) (a₁ a₂ a₃ a₄ y : Y),
    AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W → AE6Frame K K' K₃ K₄ W t u₁ u₂ a₁ a₂ a₃ a₄ y →
      ∀ j ∈ K, j * a₁ * j⁻¹ = a₁ * t →
        ∀ e ∈ ae6E Ω[R] (u₁ * u₂), ∀ e' ∈ ae6E Ω[R] (u₁ * u₂), Commute e (j * e' * j⁻¹)

section Main

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y} {a₁ a₂ a₃ a₄ y : Y}

theorem cent_normalizes_E (H : AE6Hyp n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {c : Y}
    (hc : c * (u₁ * u₂) * c⁻¹ = u₁ * u₂) : conjSub c (ae6E Ω[R] (u₁ * u₂)) = ae6E Ω[R] (u₁ * u₂) := by
  have hcC : c ∈ Subgroup.centralizer ({u₁ * u₂} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc c * (u₁ * u₂) = c * (u₁ * u₂) * c⁻¹ * c := by group
      _ = (u₁ * u₂) * c := by rw [hc]
  have h1 : conjSub c (rLayer Ω[R] (u₁ * u₂)) = rLayer Ω[R] (u₁ * u₂) :=
    T8.rLayer_conjSub_eq (hypOf H).conjInvariant hcC
  have h2 : pCoreOf 2 (conjSub c (rLayer Ω[R] (u₁ * u₂))) =
      conjSub c (pCoreOf 2 (rLayer Ω[R] (u₁ * u₂))) :=
    CFSG.CGT.PushingUpLit.BHS6.pCoreOf_conjSub c (rLayer Ω[R] (u₁ * u₂))
  unfold ae6E
  rw [← h2, h1]

theorem v3AE6EComm_of_pair (hE : V3AE6E n) (hP : V3AE6cPair n) : V3AE6EComm n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr m hm e he e' he'
  have hu : a₁ * a₂ = u₁ * u₂ := fr.hu
  have hEab := (hE Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr).1
  have hEcomm : ∀ x ∈ ae6E Ω[R] (u₁ * u₂), ∀ z ∈ ae6E Ω[R] (u₁ * u₂), x * z = z * x := by
    intro x hx z hz
    have hxx := hEab.2 x hx
    have hzz := hEab.2 z hz
    have hxz := hEab.2 (x * z) ((ae6E Ω[R] (u₁ * u₂)).mul_mem hx hz)
    calc x * z = (x * (x * z * (x * z)) * z) := by rw [hxz]; group
      _ = (x * x) * z * x * (z * z) := by group
      _ = z * x := by rw [hxx, hzz]; group
  have hEn : ∀ c : Y, c * (u₁ * u₂) * c⁻¹ = u₁ * u₂ → ∀ x ∈ ae6E Ω[R] (u₁ * u₂),
      c * x * c⁻¹ ∈ ae6E Ω[R] (u₁ * u₂) := by
    intro c hc x hx
    have := conj_mem_conjSub (n := c) hx
    rwa [cent_normalizes_E H hc] at this
  have hEn' : ∀ c : Y, c * (u₁ * u₂) * c⁻¹ = u₁ * u₂ → ∀ x ∈ ae6E Ω[R] (u₁ * u₂),
      c⁻¹ * x * c ∈ ae6E Ω[R] (u₁ * u₂) := by
    intro c hc x hx
    have hc' : c⁻¹ * (u₁ * u₂) * c⁻¹⁻¹ = u₁ * u₂ := by
      rw [inv_inv]
      calc c⁻¹ * (u₁ * u₂) * c = c⁻¹ * (c * (u₁ * u₂) * c⁻¹) * c := by rw [hc]
        _ = u₁ * u₂ := by group
    have := hEn c⁻¹ hc' x hx
    rwa [inv_inv] at this
  obtain ⟨j, hjK, hja⟩ := exists_inverting H (memKOf H) fr.h₁.1 (frameCalc_of H fr).s₁
  rcases orbit_two_trans H fr hjK hja m hm with h1 | ⟨g, hgM, hg1, hg2⟩
  · rw [hu] at h1
    exact hEcomm e he _ (hEn m h1 e' he')
  · rw [hu] at hg1 hg2
    have hj' : j * (u₁ * u₂) * j⁻¹ = j * (a₁ * a₂) * j⁻¹ := by rw [hu]
    set c := (g * j)⁻¹ * m with hcdef
    have hc : c * (u₁ * u₂) * c⁻¹ = u₁ * u₂ := by
      have : m * (u₁ * u₂) * m⁻¹ = g * (j * (u₁ * u₂) * j⁻¹) * g⁻¹ := by rw [← hu] at hg2 ⊢; exact hg2.symm
      calc c * (u₁ * u₂) * c⁻¹ = (g * j)⁻¹ * (m * (u₁ * u₂) * m⁻¹) * (g * j) := by rw [hcdef]; group
        _ = (g * j)⁻¹ * (g * (j * (u₁ * u₂) * j⁻¹) * g⁻¹) * (g * j) := by rw [this]
        _ = u₁ * u₂ := by group
    have hm' : m = g * j * c := by rw [hcdef]; group
    have hge : g⁻¹ * (u₁ * u₂) * g = u₁ * u₂ := by
      calc g⁻¹ * (u₁ * u₂) * g = g⁻¹ * (g * (u₁ * u₂) * g⁻¹) * g := by rw [hg1]
        _ = u₁ * u₂ := by group
    have he₀ : g⁻¹ * e * g ∈ ae6E Ω[R] (u₁ * u₂) := hEn' g hg1 e he
    have he'' : c * e' * c⁻¹ ∈ ae6E Ω[R] (u₁ * u₂) := hEn c hc e' he'
    have hpair := hP Y R S t K K' K₃ u₁ u₂ u₃ K₄ W a₁ a₂ a₃ a₄ y H fr j hjK hja _ he₀ _ he''
    have e1 : e = g * (g⁻¹ * e * g) * g⁻¹ := by group
    have e2 : m * e' * m⁻¹ = g * (j * (c * e' * c⁻¹) * j⁻¹) * g⁻¹ := by rw [hm']; group
    rw [e2]
    show e * (g * (j * (c * e' * c⁻¹) * j⁻¹) * g⁻¹) = g * (j * (c * e' * c⁻¹) * j⁻¹) * g⁻¹ * e
    have hp : (g⁻¹ * e * g) * (j * (c * e' * c⁻¹) * j⁻¹) = (j * (c * e' * c⁻¹) * j⁻¹) * (g⁻¹ * e * g) :=
      hpair.eq
    calc e * (g * (j * (c * e' * c⁻¹) * j⁻¹) * g⁻¹)
        = g * ((g⁻¹ * e * g) * (j * (c * e' * c⁻¹) * j⁻¹)) * g⁻¹ := by group
      _ = g * ((j * (c * e' * c⁻¹) * j⁻¹) * (g⁻¹ * e * g)) * g⁻¹ := by rw [hp]
      _ = g * (j * (c * e' * c⁻¹) * j⁻¹) * g⁻¹ * e := by group

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
