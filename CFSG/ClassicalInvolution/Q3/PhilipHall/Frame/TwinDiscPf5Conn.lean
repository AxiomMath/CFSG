module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc



section Gen

theorem q8_conjClass {G : Type} [Group G] [Finite G] {K₀ : Subgroup G}
    (h : ∃ P : Subgroup G, IsSylow2In P K₀ ∧ Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ M ∈ CoreAssembly.conjClass K₀, ∀ P : Subgroup G, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨g, rfl⟩
  apply forall_sylow_iso_of_exists
  obtain ⟨P, hP, ⟨e⟩⟩ := h
  exact ⟨conjSub g P, hP.conj g, ⟨(Subgroup.equivMapOfInjective P (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).symm.trans e⟩⟩

theorem card_secQuot_lt {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}
    (hc : c ∉ Subgroup.center G) :
    Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < Nat.card G := by
  have hC : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
    intro htop
    apply hc
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({c} : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_singleton_iff.mp this)
  have h1 : Nat.card ↥(Subgroup.centralizer ({c} : Set G)) < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      fun h => hC (Subgroup.eq_top_of_card_eq _ h)
  have h2 : Nat.card ↥(coreHull Ω c) ≤ Nat.card ↥(Subgroup.centralizer ({c} : Set G)) :=
    Subgroup.card_le_card_group _
  have h3 : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≤
      Nat.card ↥(coreHull Ω c) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  omega

end Gen

section Setup

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t₀ : Y}
  {K K' : Subgroup Y} {z u : Y} {J : Subgroup Y} {t : Y} {W : Subgroup Y}

theorem setup_members (s : Setting n R S t₀ K K' z u J t W) :
    (∀ M ∈ CoreAssembly.conjClass (tightCore R),
      IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) ∧
    (∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ P : Subgroup Y, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup 2)) ∧
    (∀ M ∈ CoreAssembly.conjClass (tightCore R), AEmpty (CoreAssembly.conjClass (tightCore R)) M) := by
  refine ⟨?_, ?_, ?_⟩
  · exact TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) s.core.datum.twoGroup)
  · exact q8_conjClass (s.core.datum.exists_sylow_q8 s.core.q8)
  · rintro _ ⟨g, rfl⟩
    exact aEmpty_conj s.core.hyp.conjInvariant s.core.aEmpty g

theorem not_mem_center_of_ne_one (s : Setting n R S t₀ K K' z u J t W) {c : Y} (hc : c ≠ 1) :
    c ∉ Subgroup.center Y := by
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple s.core.simple s.core.nonab
  rw [hZ]
  exact fun h => hc (Subgroup.mem_bot.mp h)

end Setup


section Main

variable {n : ℕ}

theorem discSecConnU_of (hT4 : Thm4RTwinBelow 3 n) : DiscSecConnU n := by
  intro Y _ _ R S t₀ K K' z u J t W s hα hY M hM N hN
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hf := s.data.frame
  have hΩ : HypOmegaGen Ω := s.core.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hf.hu2
  obtain ⟨h2, hq, hA⟩ := setup_members s
  have hMtq : M ∈ tqMembers3 Ω u := ⟨hM.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hM.1 hM.2⟩
  have hNtq : N ∈ tqMembers3 Ω u := ⟨hN.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hN.1 hN.2⟩
  have hlt : Nat.card (↥(coreHull Ω u) ⧸ classicalInvolutionOddCore ↥(coreHull Ω u)) < n :=
    s.core.card ▸ card_secQuot_lt (not_mem_center_of_ne_one s hf.hu1)
  rcases dichotomy_secFam hT4 hlt hΩ hc2 h2 hq hA hMtq with hconn | horb
  · exact secPath_of_connected hΩ hc2 hMtq le_sup_left hconn N hNtq
  · exact secPath_of_transitive hΩ hc2 hMtq
      ((coreHull_map_le_rLayer hΩ hc2).trans le_sup_right) horb N hNtq

end Main

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
