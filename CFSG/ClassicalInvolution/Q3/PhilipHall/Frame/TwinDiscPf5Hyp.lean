module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Dich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3Odd
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinADescent3Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecDatum

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Gen

theorem isPGroup_two_quotient_map {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (hN : Odd (Nat.card N)) {K : Subgroup H}
    (h : IsPGroup 2 (↥K ⧸ classicalInvolutionOddCore ↥K)) :
    IsPGroup 2 (↥(K.map (QuotientGroup.mk' N)) ⧸
      classicalInvolutionOddCore ↥(K.map (QuotientGroup.mk' N))) := by
  have hO := oddCoreOf_map_mk_of_odd (odd_natCard_inf hN K)
  intro y
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨x, hxK, hx⟩ := y0.2
  obtain ⟨m, hm⟩ := h (QuotientGroup.mk (⟨x, hxK⟩ : ↥K))
  refine ⟨m, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hm
  have h1 : x ^ 2 ^ m ∈ oddCoreOf K := ⟨_, hm, rfl⟩
  have h2 : QuotientGroup.mk' N (x ^ 2 ^ m) ∈ oddCoreOf (K.map (QuotientGroup.mk' N)) := by
    rw [hO]
    exact Subgroup.mem_map_of_mem _ h1
  obtain ⟨w, hw, hwe⟩ := h2
  have : w = y0 ^ 2 ^ m := by
    apply Subtype.ext
    have h3 : (w : H ⧸ N) = QuotientGroup.mk' N (x ^ 2 ^ m) := hwe
    rw [h3, Subgroup.coe_pow, ← hx, map_pow]
  rw [← this]
  exact hw

theorem forall_sylow_iso_of_exists {H : Type} [Group H] [Finite H] {J : Subgroup H} {A : Type}
    [Group A] (h : ∃ P : Subgroup H, IsSylow2In P J ∧ Nonempty (↥P ≃* A)) :
    ∀ P' : Subgroup H, IsSylow2In P' J → Nonempty (↥P' ≃* A) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := h
  intro P' hP'
  obtain ⟨x, -, hx⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP' hP
  exact ⟨(Subgroup.equivMapOfInjective P' (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective).trans ((MulEquiv.subgroupCongr hx).trans e)⟩

end Gen

section Hyp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hypOmegaGen_secFam (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    HypOmegaGen (secFam Ω c) :=
  TwinEdge.hypOmegaGen_quotFamily_odd
    (hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω c))
    (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c))

theorem secFam_twoGroup
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    ∀ J ∈ secFam Ω c, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
  intro J hJ
  obtain ⟨M, hM, rfl⟩ := exists_of_mem_secFam hJ
  have h1 : IsPGroup 2 (↥(TwinADescent.coreAt c M) ⧸
      classicalInvolutionOddCore ↥(TwinADescent.coreAt c M)) :=
    TwinEdge.isPGroup_two_quotient_of_le (TwinADescent.coreAt_le_left c M) (h2 M hM.1)
  have h2C := isPGroup_two_quotient_subgroupOf (TwinADescent.coreAt c M)
    (Subgroup.centralizer ({c} : Set G)) h1
  have h2X := isPGroup_two_quotient_subgroupOf
    ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) (coreHull Ω c) h2C
  exact isPGroup_two_quotient_map (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c))
    h2X

theorem hullFam_q8 (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ L ∈ hullFam Ω c, ∃ P : Subgroup ↥(coreHull Ω c), IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨_, ⟨_, ⟨M, hM, rfl⟩, -, rfl⟩, -, rfl⟩
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hM.2
  have hPs : IsSylow2In P (TwinADescent.coreAt c M) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hM.2).mpr ⟨hP, hPc⟩
  obtain ⟨e⟩ := hq M hM.1 P hP
  have hs1 : IsSylow2In (P.subgroupOf (Subgroup.centralizer ({c} : Set G)))
      ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    hPs.subgroupOf (TwinADescent.coreAt_le_centralizer c M)
  have hs2 := hs1.subgroupOf (le_coreHull hM)
  refine ⟨_, hs2, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (hs1.1.trans (le_coreHull hM))).trans
    ((Subgroup.subgroupOfEquivOfLe hPc).trans e)

theorem secFam_q8 (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ J ∈ secFam Ω c, ∀ P : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2) := by
  intro J hJ
  apply forall_sylow_iso_of_exists
  exact TwinThmE.q8_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c))
    (hullFam_q8 hc2 hq) J hJ

theorem secFam_aEmpty (hΩ : HypOmegaGen Ω) (hA : ∀ M ∈ Ω, AEmpty Ω M)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) : ∀ M ∈ secFam Ω c, AEmpty (secFam Ω c) M :=
  TwinADescent3.aEmpty_quot_coreFamily hΩ hA hc2 (coreHull Ω c)

theorem oddCore_quot_eq_bot :
    classicalInvolutionOddCore (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) = ⊥ :=
  CFSG.ComponentClassification.OddCore.quotient_corefree ↥(coreHull Ω c)

end Hyp

section Dich

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem dichotomy_secFam {n : ℕ} (h4 : Thm4RTwinBelow 3 n)
    (hlt : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < n)
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c) :
    (∀ M ∈ secFam Ω c, M ∈ dstarComp (secFam Ω c) (secImg Ω c B)) ∨
      (∀ M ∈ secFam Ω c, ∃ y, conjSub y (secImg Ω c B) = M) :=
  dichotomy_of_thm4RTwin h4 hlt (hypOmegaGen_secFam hΩ hc2) (secFam_twoGroup h2)
    (secFam_q8 hc2 hq) (secFam_aEmpty hΩ hA hc2) oddCore_quot_eq_bot (secImg_mem_secFam hB)

end Dich

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
