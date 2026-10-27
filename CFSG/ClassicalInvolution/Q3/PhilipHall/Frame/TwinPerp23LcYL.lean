module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcLDef
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcFacts
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolG3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Sec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Balance
open scoped commutatorElement


section YL

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem lcL_normal (hΩ : HypOmegaGen (Om R)) (hc2 : IsPGroup 2 (Subgroup.zpowers u)) :
    ∀ c ∈ Subgroup.centralizer ({u} : Set Y), ∀ l ∈ lcL R u, c * l * c⁻¹ ∈ lcL R u := by
  rintro c hc _ ⟨y, hy, rfl⟩
  refine ⟨⟨c, hc⟩ * y * ⟨c, hc⟩⁻¹, ?_, rfl⟩
  have h := conj_mem_conjSub (n := (⟨c, hc⟩ : ↥(Subgroup.centralizer ({u} : Set Y)))) hy
  rwa [conjSub_coreHull hΩ hc2] at h

theorem lcL_luGroup (hP : TL4.TightBelowRPlus 3 n) (hc : P23Cfg n Y R S t K' W u e g)
    (hnoU : SecNoExit R u) (hYo : YOrth R u)
    (hOu : oddCoreIn (Subgroup.centralizer ({u} : Set Y)) = ⊥) :
    Lc.LuGroup ↥(lcL R u) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hS := p23_q8Section hc.std.perp hd.hu2
  have hlt := secQ_card_lt hc.std.perp hd.hu1
  obtain ⟨-, hl, -⟩ := lifts_of_noExit hP hlt hS hnoU
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam (TwinDisc.secFam (Om R) u)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgen : omegaGen (liftFam (TwinDisc.secFam (Om R) u)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hS.gen]
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨L, u', hL⟩ := hl J hJ
    exact hL.le_sat.trans (le_omegaGen (satU_mem_liftFam hJ hL))
  obtain ⟨tag, k, e', ⟨M⟩, hE4⟩ := e4_data_of_yOrth hΛ hgen hYo
  have hO1 : classicalInvolutionOddCore ↥(coreHull (Om R) u) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := oddCore_coreHull_le hΩ hc2' hx
    have h2 : oddCoreOf (Subgroup.centralizer ({u} : Set Y)) = ⊥ := hOu
    rw [h2, Subgroup.mem_bot] at h1
    have h3 : ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = 1 := h1
    have h4 : x = 1 := Subtype.ext (Subtype.ext h3)
    exact h4 ▸ Subgroup.one_mem _
  let e : SecQ R u ≃* ↥(lcL R u) :=
    ((QuotientGroup.quotientMulEquivOfEq hO1).trans QuotientGroup.quotientBot).trans
      (Subgroup.equivMapOfInjective _ (Subgroup.centralizer ({u} : Set Y)).subtype
        (Subgroup.subtype_injective _))
  have key : ∀ {K : Type} [Group K] (ψ : K →* SecQ R u), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center K →
      ∃ φ : K →* ↥(lcL R u), Function.Surjective φ ∧ φ.ker ≤ Subgroup.center K := by
    intro K _ ψ hs hk
    refine ⟨e.toMonoidHom.comp ψ, e.surjective.comp hs, fun x hx => hk ?_⟩
    have : e (ψ x) = 1 := hx
    exact (MonoidHom.mem_ker).mpr (e.map_eq_one_iff.mp this)
  have hexp := M.exp_eq_f
  rcases hE4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, h⟩
  · obtain rfl : e' = 1 := hexp (by decide)
    exact Or.inr (key M.ψ M.surj M.ker_le_center)
  · obtain rfl : e' = 1 := hexp (by decide)
    exact Or.inl (key M.ψ M.surj M.ker_le_center)
  · exact absurd h (by decide)

end YL

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
