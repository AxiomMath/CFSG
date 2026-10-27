module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf6Lift
public import CFSG.ClassicalInvolution.Q3.Q3T7W21Z02
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieNR
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Uniform

open CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap

namespace TwinDisc


section Sq

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secAct_sq_dichotomy {n : ℕ} (hcit : CIT3Below n) (hih : IH8T 3 1 n) (hP : TL4.TightBelowRPlus 3 n)
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hlt : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < n)
    (hdisc : ¬ T3.DStarConnected (secFam Ω c))
    (hno : NoExit (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) (secFam Ω c))
    {J J' T T' : Subgroup G} {t x : G} (hJ : J ∈ tqMembers3 Ω c) (hJ' : J' ∈ tqMembers3 Ω c)
    (ht : IsUniqueInvolution J t) (ht' : IsUniqueInvolution J' t)
    (hT : IsSylow2In T J) (hT' : IsSylow2In T' J')
    (hTc : T ≤ Subgroup.centralizer ({c} : Set G)) (hT'c : T' ≤ Subgroup.centralizer ({c} : Set G))
    (hcomm : Commutes T T') (hT'J : T' ≤ Subgroup.normalizer (J : Set G))
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxJ : x ∈ trivialOnQuot J)
    (hxJ' : x ∈ trivialOnQuot J') (hx4 : x * x * (x * x) = 1) :
    ∃ (htC : t ∈ Subgroup.centralizer ({c} : Set G))
      (htY : (⟨t, htC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈ coreHull Ω c),
      secAct hΩ hc2 ⟨x, hxc⟩ * secAct hΩ hc2 ⟨x, hxc⟩ = 1 ∨
        secAct hΩ hc2 ⟨x, hxc⟩ * secAct hΩ hc2 ⟨x, hxc⟩ =
          MulAut.conj (QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω c)) :
            ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) := by
  have hS := q8Section_secFam hΩ hc2 h2 hq hA
  obtain ⟨h2', hl, hex⟩ := lifts_of_noExit hP hlt hS hno
  obtain ⟨htC, htY, htbar⟩ := isUniqueInvolution_secImg hΩ hc2 hJ ht
  obtain ⟨htC', htY', htbar'⟩ := isUniqueInvolution_secImg hΩ hc2 hJ' ht'
  refine ⟨htC, htY, ?_⟩
  set tb : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c) :=
    QuotientGroup.mk (⟨⟨t, htC⟩, htY⟩ : ↥(coreHull Ω c)) with htb
  have hJΦ : secImg Ω c J ∈ secFam Ω c := secImg_mem_secFam hJ
  have hJ'Φ : secImg Ω c J' ∈ secFam Ω c := secImg_mem_secFam hJ'
  obtain ⟨L, u₀, hL⟩ := hl _ hJΦ
  obtain ⟨L', u₀', hL'⟩ := hl _ hJ'Φ
  have hu₀ : u₀ = tb := hL.inv.eq htbar
  have hu₀' : u₀' = tb := hL'.inv.eq htbar'
  subst hu₀ hu₀'
  have hO : Balance.oddCoreIn (Subgroup.centralizer ({tb} : Set _)) = ⊥ :=
    (hno _ hJΦ tb hL.inv).1
  have hO' : Balance.oddCoreIn (Subgroup.centralizer ({tb} : Set _)) = ⊥ :=
    (hno _ hJ'Φ tb hL'.inv).1
  have hAmem := satU_mem_liftFam hJΦ hL
  have hBmem := satU_mem_liftFam hJ'Φ hL'
  have hxA : IsUniqueInvolution (satU (.sl2 3 1) L tb) tb :=
    isUniqueInvolution_liftFam_of_le hAmem hL.inv hL.le_sat
  have hxB : IsUniqueInvolution (satU (.sl2 3 1) L' tb) tb :=
    isUniqueInvolution_liftFam_of_le hBmem hL'.inv hL'.le_sat
  have hBnbr : satU (.sl2 3 1) L' tb ∈ omegaNbr (liftFam (secFam Ω c)) (satU (.sl2 3 1) L tb) :=
    (hex.mem_omegaNbr_liftFam_iff hS.hyp h2' hl hAmem hJΦ hL.le_sat hBmem hJ'Φ hL'.le_sat).mpr
      (omegaNbr_secImg hΩ hc2 hJ hJ' hT hT' hTc hT'c hcomm hT'J)
  have hne : (secFam Ω c).Nonempty := ⟨_, hJΦ⟩
  have hΛ : HypOmegaModU (.sl2 3 1) (liftFam (secFam Ω c)) :=
    hypOmegaModU_liftFam hS.hyp.conjInvariant
  have hgenΛ : omegaGen (liftFam (secFam Ω c)) = ⊤ :=
    (inClass3_liftFam hS.hyp.conjInvariant hne hl hS.gen).generated
  have hAΛ := ExactSylow.aEmpty_liftFam hS.hyp h2' hl hex hS.aEmpty
  have hdiscΛ : ¬ T3.DStarConnected (liftFam (secFam Ω c)) := fun hc =>
    hdisc (dstarConnected_of_liftFam hS.hyp h2' hl hex hc)
  set α := secAct hΩ hc2 ⟨x, hxc⟩ with hα
  have hα4 : α * α * (α * α) = 1 := by
    rw [hα]
    simp only [← map_mul]
    have : (⟨x, hxc⟩ * ⟨x, hxc⟩ * (⟨x, hxc⟩ * ⟨x, hxc⟩) :
        ↥(Subgroup.centralizer ({c} : Set G))) = 1 := Subtype.ext hx4
    rw [this, map_one]
  have hfixJ := secAct_fix_secImg hΩ hc2 (h2' _ hJΦ) hxc hxJ
  have hfixJ' := secAct_fix_secImg hΩ hc2 (h2' _ hJ'Φ) hxc hxJ'
  have hfixL := lift_fix_of_fix hS.hyp hJΦ (h2' _ hJΦ) hL hO α hfixJ
  have hfixL' := lift_fix_of_fix hS.hyp hJ'Φ (h2' _ hJ'Φ) hL' hO' α hfixJ'
  rw [satU_eq_of_oddCoreIn_eq_bot (L := L) hO] at hxA hBnbr hAmem
  rw [satU_eq_of_oddCoreIn_eq_bot (L := L') hO'] at hxB hBnbr hBmem
  exact Q3T8.Asc77.sq_dichotomy_of_twin_pair
    ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit)
    hih hlt hΛ hS.oddFree hgenΛ hAΛ hdiscΛ hAmem hBnbr hxA hxB
    α hα4 (fun a ha => by rw [hfixL a ha, mul_inv_cancel]; exact Subgroup.one_mem _)
    (fun b hb => by rw [hfixL' b hb, mul_inv_cancel]; exact Subgroup.one_mem _)

end Sq

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
