module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X5
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X10
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf19AE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf10Map
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25L3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X9

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped MatrixGroups


section Fix

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem secImg_q8 (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hno : SecNoExitAt Ω b) {J : Subgroup G} (hJ : J ∈ tqMembers3 Ω b) :
    IsPGroup 2 (TwinDisc.secImg Ω b J) ∧ Nat.card ↥(TwinDisc.secImg Ω b J) = 8 ∧
      ∀ q ∈ TwinDisc.secImg Ω b J, q ^ 4 = 1 := by
  classical
  have hS := layer_q8Section hyp hb2
  have hcenter : b ∉ Subgroup.center G := by
    have hZ := CoreLike.center_eq_bot (G := G)
    rw [hZ]
    exact fun h => hb1 (Subgroup.mem_bot.mp h)
  have hlt := card_secQuot_lt (Ω := Ω) hcenter
  have hih : TwinThmE.EIH (Nat.card G) := hyp.std.1.ih
  obtain ⟨h2', -, -⟩ := lifts_of_noExit hih.2 hlt hS hno
  have hmem := TwinDisc.secImg_mem_secFam hJ
  have hp2 : IsPGroup 2 (TwinDisc.secImg Ω b J) := h2' _ hmem
  obtain ⟨e⟩ := hS.q8 _ hmem (TwinDisc.secImg Ω b J)
    ⟨le_rfl, hp2, fun V hV _ hPV => le_antisymm hV hPV⟩
  refine ⟨hp2, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  · intro q hq
    have h4 : ∀ g : QuaternionGroup 2, g ^ 4 = 1 := by decide
    have : (⟨q, hq⟩ : ↥(TwinDisc.secImg Ω b J)) ^ 4 = 1 := by
      apply e.injective
      rw [map_pow, h4, map_one]
    simpa using congrArg Subtype.val this

theorem secAct_fix_lifts (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) {b : G} (hb2 : b * b = 1) (hb1 : b ≠ 1)
    (hbA : b ∈ cA S R R') (hno : SecNoExitAt Ω b) {A A' : Subgroup (SecQ Ω b)}
    (hAK : TwinDisc.secImg Ω b K ≤ A) (hAK' : TwinDisc.secImg Ω b K' ≤ A')
    (hAmem : A ∈ liftFam (TwinDisc.secFam Ω b)) (hA'mem : A' ∈ liftFam (TwinDisc.secFam Ω b))
    (eA : A ≃* SL(2, ZMod 3)) (eA' : A' ≃* SL(2, ZMod 3))
    {x : G} (hxA : x ∈ cA S R R') (hxb : x ∈ Subgroup.centralizer ({b} : Set G)) :
    (∀ a ∈ A, TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2) ⟨x, hxb⟩ a = a) ∧
      ∀ a ∈ A', TwinDisc.secAct hyp.std.1.stand.hyp (isPGroup_zpowers_of_sq_eq_one hb2) ⟨x, hxb⟩ a = a := by
  classical
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  obtain ⟨hKtq, hK'tq, -, -, -, -⟩ := layer_twins_tq hyp hbA
  set β : MulAut (SecQ Ω b) := TwinDisc.secAct hΩ hc2 ⟨x, hxb⟩ with hβ
  obtain ⟨hp2, hc8, h4⟩ := secImg_q8 hyp hb2 hb1 hno hKtq
  obtain ⟨hp2', hc8', h4'⟩ := secImg_q8 hyp hb2 hb1 hno hK'tq
  have hfixK : ∀ q ∈ TwinDisc.secImg Ω b K, β q = q :=
    TwinDisc.secAct_fix_secImg hΩ hc2 hp2 hxb (mem_trivialOnQuot_of_mem_A hyp hxA).1
  have hfixK' : ∀ q ∈ TwinDisc.secImg Ω b K', β q = q :=
    TwinDisc.secAct_fix_secImg hΩ hc2 hp2' hxb (mem_trivialOnQuot_of_mem_A hyp hxA).2
  have hσ : ∀ L ∈ TwinDisc.secFam Ω b, L.map β.toMonoidHom ∈ TwinDisc.secFam Ω b := by
    intro L hL
    obtain ⟨J₁, hJ₁, rfl⟩ := TwinDisc.exists_of_mem_secFam hL
    rw [hβ, TwinDisc.secAct_map_secImg hΩ hc2 ⟨x, hxb⟩]
    exact TwinDisc.secImg_mem_secFam (conjSub_mem_tqMembers3 hΩ.conjInvariant hxb hJ₁)
  have hΩΦ : HypOmegaGen (TwinDisc.secFam Ω b) := TwinDisc.hypOmegaGen_secFam hΩ hc2
  have key : ∀ {B : Subgroup (SecQ Ω b)} {J : Subgroup G}, J ∈ tqMembers3 Ω b →
      (∀ q ∈ TwinDisc.secImg Ω b J, β q = q) → TwinDisc.secImg Ω b J ≤ B →
      B ∈ liftFam (TwinDisc.secFam Ω b) → ∀ a ∈ B, β a ∈ B := by
    intro B J hJ hfix hJB hB a ha
    have hBmap : B.map β.toMonoidHom ∈ liftFam (TwinDisc.secFam Ω b) :=
      TwinExitPf10.liftFam_map β hσ hB
    have hJΦ := TwinDisc.secImg_mem_secFam hJ
    have hJle : TwinDisc.secImg Ω b J ≤ B.map β.toMonoidHom := by
      intro q hq
      exact ⟨q, hJB hq, hfix q hq⟩
    have hBeq := liftFam_eq_of_le hΩΦ hBmap hB hJΦ hJle hJB
    have : β a ∈ B.map β.toMonoidHom := ⟨a, ha, rfl⟩
    rwa [hBeq] at this
  refine ⟨?_, ?_⟩
  · exact fix_of_fix_sylow eA (mem_of_pow_four_eq_one eA hAK h4 hc8) β
      (key hKtq hfixK hAK hAmem) hfixK
  · exact fix_of_fix_sylow eA' (mem_of_pow_four_eq_one eA' hAK' h4' hc8') β
      (key hK'tq hfixK' hAK' hA'mem) hfixK'

end Fix

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
