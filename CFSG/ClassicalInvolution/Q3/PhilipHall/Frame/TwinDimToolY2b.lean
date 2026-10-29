module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY2a
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolE2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDimToolY1a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement


section Y2b

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem no_member_commutes_q8 (hc : P23Cfg n Y R S t K' W u e g) {v' : Y}
    (hzv : t = v' ∨ t = u * v') (vH : ↥(coreHull (Om R) u))
    (hvH : ((vH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = v') :
    ∀ J ∈ tqMembers3 (Om R) u, ∃ m ∈ secImg (Om R) u J,
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) vH * m ≠
        m * QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull (Om R) u)) vH := by
  intro J hJ
  by_contra hcon
  push Not at hcon
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have htuC : t ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_ut hc).symm
  set N := classicalInvolutionOddCore ↥(coreHull (Om R) u) with hN
  obtain ⟨T₀, hT₀, hT₀c⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2' hJ.2
  set NG : Subgroup Y := N.map (TwinThmE.secEmb (Om R) u) with hNG
  have hNodd : Odd (Nat.card NG) := by
    rw [hNG, Subgroup.card_map_of_injective (TwinThmE.secEmb_injective)]
    exact CFSG.ComponentClassification.OddCore.odd_card _
  have hrH : ∀ r ∈ T₀, ∃ rH : ↥(coreHull (Om R) u),
      ((rH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) = r ∧
        QuotientGroup.mk' N rH ∈ secImg (Om R) u J := fun r hr =>
    exists_hull_elt hJ (le_tightCore_of_isPGroup (le_inf hT₀.1 hT₀c) hT₀.2.1 hr)
  have hnorm : ∀ x : ↥(coreHull (Om R) u),
      ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) ∈ Subgroup.normalizer (NG : Set Y) := by
    intro x
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨x * m * x⁻¹, (inferInstance : N.Normal).conj_mem m hm x, rfl⟩
    · rintro ⟨m, hm, hmy⟩
      have hy : y = ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)⁻¹ *
          (TwinThmE.secEmb (Om R) u m) * ((x : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) := by
        rw [hmy]; group
      rw [hy]
      exact ⟨x⁻¹ * m * x, by
        have := (inferInstance : N.Normal).conj_mem m hm x⁻¹
        simpa using this, rfl⟩
  have hcN : t ∈ Subgroup.normalizer (NG : Set Y) := by
    have key : ∀ y ∈ NG, t * y * t⁻¹ ∈ NG := by
      rintro _ ⟨m, hm, rfl⟩
      have h1 := TwinDisc.coe_secAct_mk hΩ hc2' ⟨t, htuC⟩ m
      have h2 : QuotientGroup.mk (C25Y.conjOnSub (coreHull (Om R) u)
          (conjSub_coreHull hΩ hc2' (⟨t, htuC⟩ : ↥(Subgroup.centralizer ({u} : Set Y)))) m) =
          (1 : ↥(coreHull (Om R) u) ⧸ N) := by
        rw [← TwinDisc.secAct_mk hΩ hc2' ⟨t, htuC⟩ m, (QuotientGroup.eq_one_iff m).mpr hm, map_one]
      refine ⟨C25Y.conjOnSub (coreHull (Om R) u)
        (conjSub_coreHull hΩ hc2' (⟨t, htuC⟩ : ↥(Subgroup.centralizer ({u} : Set Y)))) m,
        (QuotientGroup.eq_one_iff _).mp h2, ?_⟩
      show ((C25Y.conjOnSub (coreHull (Om R) u)
        (conjSub_coreHull hΩ hc2' (⟨t, htuC⟩ : ↥(Subgroup.centralizer ({u} : Set Y)))) m :
          ↥(coreHull (Om R) u)) : ↥(Subgroup.centralizer ({u} : Set Y))).1 = _
      rw [h1]
      rfl
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key y hy, fun hy => ?_⟩
    have := key _ hy
    have ht2 : t * t = 1 := hz.sq
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [hti] at this
    have e : t * (t * y * t) * t = y := by
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [ht2]; group
    rwa [e] at this
  have hcR : ∀ r ∈ T₀, ⁅t, r⁆ ∈ NG := by
    intro r hr
    obtain ⟨rH, hrHv, hrHm⟩ := hrH r hr
    have hcomm : vH * rH * vH⁻¹ * rH⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      have h1 : QuotientGroup.mk' N vH * QuotientGroup.mk' N rH =
          QuotientGroup.mk' N rH * QuotientGroup.mk' N vH := hcon _ hrHm
      show QuotientGroup.mk' N (vH * rH * vH⁻¹ * rH⁻¹) = 1
      simp only [map_mul, map_inv]
      rw [h1]
      group
    refine ⟨_, hcomm, ?_⟩
    have hvC : v' * u = u * v' := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (vH : ↥(Subgroup.centralizer ({u} : Set Y))).2
      rwa [hvH] at this
    have hrC : r * u = u * r := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (rH : ↥(Subgroup.centralizer ({u} : Set Y))).2
      rwa [hrHv] at this
    show ((vH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) * ((rH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y) *
      ((vH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)⁻¹ * ((rH : ↥(Subgroup.centralizer ({u} : Set Y))) : Y)⁻¹ = ⁅t, r⁆
    rw [hvH, hrHv, commutatorElement_def]
    rcases hzv with h | h
    · rw [h]
    · have hvC' : Commute u v' := (hvC : Commute v' u).symm
      have hrC' : Commute u r := (hrC : Commute r u).symm
      have hcu : Commute u (v' * r * v'⁻¹) :=
        Commute.mul_right (Commute.mul_right hvC' hrC') hvC'.inv_right
      rw [h]
      calc v' * r * v'⁻¹ * r⁻¹ = u * (v' * r * v'⁻¹) * u⁻¹ * r⁻¹ := by
            rw [hcu.eq]; group
        _ = u * v' * r * (u * v')⁻¹ * r⁻¹ := by group
  have hRN : T₀ ≤ Subgroup.normalizer (NG : Set Y) := fun r hr => by
    obtain ⟨rH, hrHv, -⟩ := hrH r hr
    exact hrHv ▸ hnorm rH
  obtain ⟨m, hmN, hmR⟩ := Asc77.T7L.exists_conj_centralizes hz.sq hNodd hT₀.2.1 hRN hcN hcR
  obtain ⟨mH, hmHm, rfl⟩ := Subgroup.mem_map.mp hmN
  have hmC : TwinThmE.secEmb (Om R) u mH ∈ Subgroup.centralizer ({u} : Set Y) :=
    (mH : ↥(Subgroup.centralizer ({u} : Set Y))).2
  have hJn : conjSub (TwinThmE.secEmb (Om R) u mH) J ∈ tqMembers3 (Om R) u :=
    conjSub_mem_tqMembers3 hΩ.conjInvariant hmC hJ
  have hS := hT₀.conj (TwinThmE.secEmb (Om R) u mH)
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  obtain ⟨hKt, hK't⟩ := not_mem_tq_u hc
  by_cases hne : conjSub (TwinThmE.secEmb (Om R) u mH) J = tightCore R
  · exact hKt (hne ▸ hJn)
  · have hnbr := Q3T8.Asc77.mem_omegaNbr_of_sylow_le_centralizer hΩ hK hJn.1 hne hz hS
      (mem_RSet_of_isSylow2In hJn.1 hS) hmR
    have hp : conjSub (TwinThmE.secEmb (Om R) u mH) J ∈ KPerp (Om R) (tightCore R) := Or.inr hnbr
    rw [hperp] at hp
    rcases hp with h | h
    · exact hne h
    · exact hK't (h ▸ hJn)

end Y2b

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
