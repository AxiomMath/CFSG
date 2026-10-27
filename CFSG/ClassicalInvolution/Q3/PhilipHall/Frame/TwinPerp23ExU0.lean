module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf17Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGenSec
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
open scoped commutatorElement



section U0

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem layer_exit_frame (hT : Thm4RTwinBelow 3 n) (h : PerpHypS n Y R S t) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) {J₁ J₂ : Subgroup Y}
    (hJ₁ : J₁ ∈ Om R) (hJ₂ : J₂ ∈ Om R) (hne : J₂ ≠ J₁) {w : Y}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ T₂ : Subgroup Y}
    (hT₁ : IsSylow2In T₁ J₁) (hT₂ : IsSylow2In T₂ J₂)
    (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set Y)) (hT₂c : T₂ ≤ Subgroup.centralizer ({c} : Set Y))
    (hcomm : Commutes T₁ T₂)
    (hperp₁ : ∀ J₀ ∈ Om R, J₀ ∈ KPerp (Om R) J₁ → J₀ = J₁ ∨ J₀ = J₂)
    (hperp₂ : ∀ J₀ ∈ Om R, J₀ ∈ KPerp (Om R) J₂ → J₀ = J₂ ∨ J₀ = J₁) :
    TwinDisc.secImg (Om R) c J₂ ∈ omegaNbr (TwinDisc.secFam (Om R) c) (TwinDisc.secImg (Om R) c J₁) ∧
      ((∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
          ∃ x : SecQ R c, conjSub x K = L) ∨
        ∀ M ∈ TwinDisc.secFam (Om R) c,
          M = TwinDisc.secImg (Om R) c J₁ ∨ M = TwinDisc.secImg (Om R) c J₂) := by
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hKtq : J₁ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨T₁, hT₁, hT₁c⟩⟩
  have hK'tq : J₂ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨T₂, hT₂, hT₂c⟩⟩
  have hS := p23_q8Section h hc2
  have hlt := secQ_card_lt h hc1
  have h8 : 8 ≤ Nat.card T₂ :=
    Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ₂ hT₂)
  have hT₂w : T₂ ≤ Subgroup.centralizer ({w} : Set Y) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hw₂.commute_of_mem (hT₂.1 hx)).symm
  have hT₂J : T₂ ≤ Subgroup.normalizer (J₁ : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ₁ hJ₂ hne.symm hw₁ hT₂.1 hT₂.2.1 (by omega) hT₂w
  have hedge := omegaNbr_secImg hΩ hc2' hKtq hK'tq hT₁ hT₂ hT₁c hT₂c hcomm hT₂J
  refine ⟨hedge, ?_⟩
  by_cases hnot : ∀ M ∈ TwinDisc.secFam (Om R) c,
      M = TwinDisc.secImg (Om R) c J₁ ∨ M = TwinDisc.secImg (Om R) c J₂
  · exact Or.inr hnot
  · left
    refine transitive_of_twin_nbr_of_not_two hT hlt hS (secImg_mem_secFam hKtq)
      (secImg_mem_secFam hK'tq) ?_ ?_ hnot
    · intro M hM hMn
      obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
      exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hKtq hJ₀
        (fun J₀' hJ₀' hp => hperp₁ J₀' hJ₀'.1 hp) hMn
    · intro M hM hMn
      obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
      exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hK'tq hJ₀
        (fun J₀' hJ₀' hp => hperp₂ J₀' hJ₀'.1 hp) hMn

end U0

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
