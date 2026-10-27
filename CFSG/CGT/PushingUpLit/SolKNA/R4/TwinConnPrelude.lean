module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnHyp51
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinConnFinalFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf4Edge

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSep
open CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
open scoped commutatorElement

section SepHyp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem sepHyp_of_thm4RTwin_R {r n : ℕ} (h4 : Thm4RTwinBelow r n) (hn : Nat.card G ≤ n)
    (hΩ : HypOmegaGen Ω) (h2 : ∀ J ∈ Ω, IsPGroup 2 J)
    (hq8 : ∀ J ∈ Ω, Nonempty (↥J ≃* QuaternionGroup (2 ^ (r - 2)))) (hA : ∀ J ∈ Ω, AEmpty Ω J)
    (hZ : Subgroup.center G = ⊥)
    (hθ : ∀ K ∈ Ω, ∀ z : G, IsUniqueInvolution K z →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set G)) = ⊥) :
    TC.SepHyp Ω := by
  intro K J J' hKJ hKJ' hnot
  have hK : K ∈ Ω := hKJ.1
  have hJΩ : J ∈ Ω := hKJ.2.1
  have hJ'Ω : J' ∈ Ω := hKJ'.2.1
  obtain ⟨⟨z, hz⟩, -⟩ := hΩ.omega1 K hK
  set H := nbrGen (nbrAdj Ω) K with hHdef
  have hJH : J ≤ H := le_nbrGen hKJ
  have hJ'H : J' ≤ H := le_nbrGen hKJ'
  have hOH := oddCore_nbrGen_eq_bot hΩ h2 hK hz (hθ K hK z hz)
  have hHn : Nat.card H < n := lt_of_lt_of_le (card_nbrGen_lt hΩ h2 hK hz hZ) hn
  have hΩH : HypOmegaGen (restrictFamily Ω H) := hypOmegaGen_restrict hΩ H
  have h2H : ∀ M ∈ restrictFamily Ω H, IsPGroup 2 ↥M := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    exact (h2 L hL).of_equiv (Subgroup.subgroupOfEquivOfLe hLH).symm
  have htwo : ∀ M ∈ restrictFamily Ω H, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    fun M hM => (h2H M hM).to_quotient _
  have hquat : ∀ M ∈ restrictFamily Ω H, ∀ P : Subgroup ↥H, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨L, hL, hLH, rfl⟩ P hP
    have hPeq : P = L.subgroupOf H :=
      (hP.2.2 _ le_rfl (h2H _ ⟨L, hL, hLH, rfl⟩) hP.1).symm
    subst hPeq
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLH).trans (hq8 L hL).some⟩
  have hAH : ∀ M ∈ restrictFamily Ω H, AEmpty (restrictFamily Ω H) M := by
    rintro _ ⟨L, hL, hLH, rfl⟩
    exact aEmpty_restrictFamily hΩ h2 subset_rfl hLH (hA L hL)
  have hc := h4 ↥H hHn (restrictFamily Ω H) hΩH htwo hquat hAH hOH (J.subgroupOf H)
    ⟨J, hJΩ, hJH, rfl⟩ (J'.subgroupOf H) ⟨J', hJ'Ω, hJ'H, rfl⟩ (fun hex => by
      obtain ⟨g, hgH, hg⟩ := TL4.exists_conjSub_of_restrict hJH hJ'H hex
      exact hnot ⟨g, hgH, hg⟩)
  have hcomm : Commutes J J' := TL4.commutes_of_restrict hJH hJ'H hc
  have hne : J' ≠ J := fun h => hnot (by rw [h]; exact mem_orbOf_self K J)
  exact nbrAdj_of_commutes hΩ h2 hJΩ hJ'Ω hne hcomm


end SepHyp

section Prelude


variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y} {r n : ℕ}

theorem quiet_edge_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n Y R S t) (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥)
    {M N : Subgroup Y} (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hN : N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) {zM zN : Y}
    (hzM : IsUniqueInvolution M zM) (hzN : IsUniqueInvolution N zN) (hne : zM ≠ zN)
    (hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y)) : Quiet zN zM hcomm := by
  have hΩ := h.hyp
  obtain ⟨K', hK', hne'⟩ := h.twin
  obtain ⟨M'', hM'', hM''ne⟩ := TwinFrame.exists_twin_of_trans hΩ (TwinFrame.trans_conjClass _)
    (CoreAssembly.mem_conjClass_self _) hK' hne' hM
  have hzM'' : IsUniqueInvolution M'' zM := isUniqueInvolution_of_mem_twinSet hzM hM''
  have hNM'' : N ≠ M'' := by
    intro e
    rw [e] at hzN
    exact hne (hzM''.eq hzN)
  have hJ'' : N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M'' :=
    TwinExitPf4.omegaNbr_of_twin hΩ hM''.1 hzM hzM'' hN hNM''
  exact quiet_nbr_R h4 hT h hRc hZ hM hzM hM'' hM''ne hN hJ'' hzN (Ne.symm hne)
    (Subgroup.mem_centralizer_singleton_iff.mp hcomm) (c := zN) (Or.inl rfl) hcomm

theorem autOddFreeOn_of_edges_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n Y R S t) (hRc : tightCore R = R) (hZ : Subgroup.center Y = ⊥) :
    ∀ M ∈ CoreAssembly.conjClass (tightCore R),
      ∀ N ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M,
      ∀ zM zN : Y, IsUniqueInvolution M zM → IsUniqueInvolution N zN → zM ≠ zN →
        ∀ hcomm : zM ∈ Subgroup.centralizer ({zN} : Set Y),
        ∀ L : Subgroup (OddQuot zN), CFSG.IsComponent L →
          oddQuotMk zN ⟨zM, hcomm⟩ ∈ Subgroup.normalizer (L : Set (OddQuot zN)) →
          (∃ y ∈ L, oddQuotMk zN ⟨zM, hcomm⟩ * y ≠ y * oddQuotMk zN ⟨zM, hcomm⟩) →
          Q3NM.AutOddFreeOn ↥L (TL4.IsInducedAut L (oddQuotMk zN ⟨zM, hcomm⟩)) := by
  rintro M hM N hN zM zN hzM hzN hne hcomm L hL - ⟨y, hy, hne'⟩
  exact absurd (quiet_edge_R h4 hT h hRc hZ hM hN hzM hzN hne hcomm L hL y hy) hne'

theorem hyp51_allR (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n Y R S t) (hZ : Subgroup.center Y = ⊥)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M) :
    ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore R)), Hyp51 B := by
  obtain ⟨S₀, h₀⟩ := h.core
  have hid := TwinEdge.tightCore_idem R
  have key : ∀ B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore (tightCore R))),
      Hyp51 B := by
    intro B hB
    exact hyp51_of_mem_frameSet_R h4 hT h₀ hid hZ (by rw [hid]; exact hsolv) hB
  rwa [hid] at key

theorem twinConn_preludeR (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n Y R S t)
    (hconn : Disconnected.DConnected (CoreAssembly.conjClass (tightCore R))) :
    TwinConnPreR r R := by
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hZ : Subgroup.center Y = ⊥ :=
    PhilipHall.InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hΩ := h.hyp
  have htr : ∀ M ∈ Ω, ∀ N ∈ Ω, ∃ g : Y, conjSub g M = N := TwinFrame.trans_conjClass _
  have hgen : (⨆ J ∈ Ω, J) = ⊤ := iSup_conjClass_eq_top h.gen
  have hz₀ : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  have hsolv : ∀ M ∈ Ω, Group.IsSolvable ↥M := by
    rintro _ ⟨g, rfl⟩
    have hR := Q8Datum.isSolvable h.datum
    have hK : Group.IsSolvable ↥(tightCore R) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (tightCore_le R))
        (Subgroup.inclusion_injective _)
    exact isSolvable_conjSub_of hK g
  have hO : componentClassificationOddCore Y = ⊥ := h.oddFree
  obtain ⟨K', hK', hne'⟩ := h.twin
  obtain ⟨S₀, h₀⟩ := h.core
  have hid := TwinEdge.tightCore_idem R
  have hhyp := hyp51_allR h4 hT h hZ hsolv
  have hα : ∀ M ∈ Ω, ∀ N ∈ omegaNbr Ω M, ∀ zM zN : Y, IsUniqueInvolution M zM →
      IsUniqueInvolution N zN → zM ≠ zN → alphaOf (Subgroup.closure ({zM, zN} : Set Y)) = ⊥ :=
    fun M hM N hN zM zN hzM hzN hne =>
      TwinFrame.alpha_edge_hyp51 hO hΩ htr hconn hgen hZ hhyp (CoreAssembly.mem_conjClass_self _)
        hK' hne' hM hN hzM hzN hne
  have hsec := autOddFreeOn_of_edges_R h4 hT h₀ hid hZ
  rw [hid] at hsec
  have hθ₀ : oddCoreImg (Subgroup.centralizer ({t} : Set Y)) = ⊥ :=
    oddCent_eq_bot_of_alpha hΩ hO hz₀ hconn hα hsec
  have hθ : ∀ K ∈ Ω, ∀ z : Y, IsUniqueInvolution K z →
      oddCoreImg (Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
    rintro _ ⟨g, rfl⟩ z hz
    have hzg : z = g * t * g⁻¹ := (hz₀.conj g).eq hz |>.symm
    subst hzg
    have hcard := TwinOdd.card_oddCent_conj g t
    rw [hθ₀, Subgroup.card_bot] at hcard
    exact Subgroup.eq_bot_of_card_eq _ hcard
  have hθ' : ∀ K ∈ Ω, ∀ z : Y, IsUniqueInvolution K z →
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
    intro K hK z hz
    have h1 : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set Y)) = ⊥ := hθ K hK z hz
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  have h2q : IsPGroup 2 (↥(tightCore R) ⧸ classicalInvolutionOddCore ↥(tightCore R)) :=
    TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup
  have h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J := isPGroup_conjClass_of_oddCent hΩ hz₀ hθ₀ h2q
  have hK₀q : Nonempty (↥(tightCore R) ≃* QuaternionGroup (2 ^ (r - 2))) := by
    have hP := h.datum.sylow_core
    have hK2 := h2 _ (CoreAssembly.mem_conjClass_self _)
    have hPeq : tightCore R = (S : Subgroup R).map R.subtype := hP.2.2 _ le_rfl hK2 hP.1
    rw [hPeq]
    exact ⟨(Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
      h.quat.some⟩
  have hq8 : ∀ J ∈ Ω, Nonempty (↥J ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨e⟩ := hK₀q
    exact ⟨(Subgroup.equivMapOfInjective (tightCore R) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm.trans e⟩
  have hA : ∀ J ∈ Ω, AEmpty Ω J :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) h.aEmpty
  have hsep : TC.SepHyp Ω :=
    sepHyp_of_thm4RTwin_R h4 (le_of_eq h.card) hΩ h2 hq8 hA hZ hθ'
  exact ⟨hθ', fun J hJ => ⟨h2 J hJ, hq8 J hJ⟩, ⟨hΩ, h2, hsep, h.gen, hconn⟩⟩

end Prelude

end CFSG.CGT.PushingUpLit.SolKNA.R4
