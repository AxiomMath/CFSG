module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3PfDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.InductionBridge.FStarNormal

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.ClassicalInvolution.Balance.Bootstrap (trivialOnQuot)

section Sec

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem members_sylow_q8 (h : PerpHypS n Y R S t) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  have hC := CoreData.of_S h.core
  rintro _ ⟨g', rfl⟩
  apply forall_sylow_iso_of_exists
  obtain ⟨P, hP', ⟨e⟩⟩ := hC.datum.exists_sylow_q8 hC.q8
  exact ⟨conjSub g' P, hP'.conj g', ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g').toMonoidHom
    (MulAut.conj g').injective).symm.trans e⟩⟩

theorem layer_q8Section (h : PerpHypS n Y R S t) {c : Y} (hc : c * c = 1) :
    Q8Section (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c))
      (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c) := by
  have hC := CoreData.of_S h.core
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc
  exact q8Section_secFam hC.hyp hc2
    (TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup))
    (members_sylow_q8 h) hC.aEmpty_all

theorem card_layer_lt (h : PerpHypS n Y R S t) {c : Y} (hc1 : c ≠ 1) :
    Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c)) < n := by
  have hC := CoreData.of_S h.core
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple hC.simple hC.nonab
  have hne : Subgroup.centralizer ({c} : Set Y) ≠ ⊤ := by
    intro htop
    apply hc1
    have : c ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => by
      have : g ∈ Subgroup.centralizer ({c} : Set Y) := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    rw [hZ] at this
    exact Subgroup.mem_bot.mp this
  have h1 : Nat.card ↥(Subgroup.centralizer ({c} : Set Y)) < n := by
    rw [← hC.card]
    exact lt_of_le_of_ne (Subgroup.card_le_card_group _) fun heq =>
      hne ((Subgroup.card_eq_iff_eq_top _).mp heq)
  have h2 := Subgroup.card_le_card_group (coreHull (CoreAssembly.conjClass (tightCore R)) c)
  have h3 : Nat.card (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
      classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c)) ≤
      Nat.card ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  omega

theorem layer_lieDecomp (hcit : CIT3Below n) (hP : TL4.TightBelowRPlus 3 n)
    (h : PerpHypS n Y R S t) {c : Y} (hc : c * c = 1) (hc1 : c ≠ 1)
    (hne : (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c).Nonempty)
    (hno : NoExit (↥(coreHull (CoreAssembly.conjClass (tightCore R)) c) ⧸
        classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) c))
      (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c)) :
    (∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c, IsPGroup 2 J) ∧
      HasLifts (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c) ∧
      ExactSylow (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c) ∧
      Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) c))) :=
  lieDecomp_of_noExit hcit hP (card_layer_lt h hc1) (layer_q8Section h hc) hne hno

end Sec

section Named

@[expose] def V3LayerGen (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y)
    (K K' K₃ : Subgroup Y) (u₁ u₂ u₃ : Y), V3Std n Y R S t K K' K₃ u₁ u₂ u₃ →
      ∀ K₄ : Subgroup Y,
        FourthTwin (CoreAssembly.conjClass (tightCore R)) K K' K₃ t u₁ u₂ u₃ K₄ →
          NoExit (↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) ⧸
              classicalInvolutionOddCore ↥(coreHull (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)))
            (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            (∀ J ∈ TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂), IsPGroup 2 J) →
            HasLifts (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            ExactSylow (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)) →
            Nonempty (OmegaLieU 3 1 (liftFam (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R))
              (u₁ * u₂)))) →
              ∀ R₃ R₄ : Subgroup Y, IsSylow2In R₃ K₃ → IsSylow2In R₄ K₄ →
                R₃ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
                R₄ ≤ Subgroup.centralizer ({u₁ * u₂} : Set Y) →
                  (⨆ x : ↥(rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)), conjSub (x : Y) R₃) = rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂) ∧
                    R₄ ∈ twinSet {L | ∃ x : ↥(rLayer (CoreAssembly.conjClass (tightCore R)) (u₁ * u₂)), conjSub (x : Y) R₃ = L} R₃

end Named

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
