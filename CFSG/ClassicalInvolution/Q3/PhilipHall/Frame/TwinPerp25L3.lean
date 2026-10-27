module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGenSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSecNoExit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Defs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap


section Trans

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem layer_twins_tq (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (hacA : a ∈ cA S R R') :
    K ∈ tqMembers3 Ω a ∧ K' ∈ tqMembers3 Ω a ∧ IsUniqueInvolution K z ∧ IsUniqueInvolution K' z ∧
      (∀ J₀ ∈ tqMembers3 Ω a, J₀ ∈ KPerp Ω K → J₀ = K ∨ J₀ = K') ∧
      (∀ J₀ ∈ tqMembers3 Ω a, J₀ ∈ KPerp Ω K' → J₀ = K' ∨ J₀ = K) := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hKΩ : K ∈ Ω := hyp.std.1.stand.mem
  have hK'tw : K' ∈ twinSet Ω K := hyp.std.1.hK'
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hz : IsUniqueInvolution K z := hyp.std.1.hz
  have hz' : IsUniqueInvolution K' z := by
    obtain ⟨-, z', hz'K, hz'J⟩ := hK'tw
    rwa [hz.eq hz'K]
  have hRK : IsSylow2In R K :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hKΩ hyp.hR.1 hyp.hR.2.1
  have hR'K' : IsSylow2In R' K' :=
    Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hyp.hR'.1 hyp.hR'.2.1
  have hcomm : ∀ x ∈ R ⊔ R', x * a = a * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp hacA.2 x hx
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Subgroup.mem_sup_left hx))
  have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x (Subgroup.mem_sup_right hx))
  have h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) := hyp.std.1.quot2
  have hKtq : K ∈ tqMembers3 Ω a :=
    ⟨hKΩ, TwinADescent3.mem_tq_of_sylCent hΩ h2 hKΩ ⟨R, hRK, hRc⟩⟩
  have hK'tq : K' ∈ tqMembers3 Ω a :=
    ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R', hR'K', hR'c⟩⟩
  have hperp : KPerp Ω K = {K, K'} := hyp.std.2
  refine ⟨hKtq, hK'tq, hz, hz', ?_, ?_⟩
  · intro J₀ _ hJ₀
    rw [hperp] at hJ₀
    exact hJ₀
  · intro J₀ _ hJ₀
    rcases hJ₀ with h | h
    · exact Or.inl h
    · have h1 : J₀ ∈ KPerp Ω K := Q3T7M.omegaNbr_subset_kPerp_of_twin hΩ hKΩ hz' hz h
      rw [hperp] at h1
      rcases h1 with h1 | h1
      · exact Or.inr h1
      · exact Or.inl h1

theorem layer_transitive (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1)
    (ha1 : a ≠ 1) (hacA : a ∈ cA S R R') (hT : TwinThmE.T4Supply) (hno : SecNoExitAt Ω a) :
    ∀ M ∈ TwinDisc.secFam Ω a, ∀ N ∈ TwinDisc.secFam Ω a,
      ∃ x : ↥(coreHull Ω a) ⧸ classicalInvolutionOddCore ↥(coreHull Ω a), conjSub x M = N := by
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers a) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one ha2
  obtain ⟨hKtq, hK'tq, hz, hz', hperp₁, hperp₂⟩ := layer_twins_tq hyp hacA
  have hS := layer_q8Section hyp ha2
  have hcenter : a ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => ha1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  have h4 := hT (Nat.card G) hih.1 hih.2
  obtain ⟨htC₁, htY₁, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2 hKtq hz
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2 hK'tq hz'
  refine TwinLayerGen.transitive_of_twin_nbr h4 hlt hS hno (secImg_mem_secFam hKtq)
    (secImg_mem_secFam hK'tq) hz₁ hz₂ ?_ ?_
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hKtq hJ₀ hperp₁ hMn
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2 hK'tq hJ₀ hperp₂ hMn

end Trans

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
