module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

section Fam

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

variable (Ω c) in
@[expose] def famX (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    Set (Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)) :=
  quotFamily (restrictFamily (cFam Ω c) X) (classicalInvolutionOddCore ↥X)

variable (c) in
@[expose] noncomputable def imgX (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G)))
    (J : Subgroup G) : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X) :=
  (((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf X).map
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥X))

theorem imgX_mem_famX {X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))} {J : Subgroup G}
    (hJ : J ∈ tqMembers3 Ω c)
    (hX : (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ X) :
    imgX c X J ∈ famX Ω c X :=
  ⟨_, ⟨_, ⟨_, ⟨J, hJ, rfl⟩, TwinADescent.coreAt_le_centralizer c J, rfl⟩, hX, rfl⟩, rfl⟩

theorem exists_of_mem_famX {X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))}
    {M : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X)} (hM : M ∈ famX Ω c X) :
    ∃ J ∈ tqMembers3 Ω c,
      (TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G)) ≤ X ∧
        M = imgX c X J := by
  obtain ⟨_, ⟨_, ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩, hX, rfl⟩, rfl⟩ := hM
  exact ⟨J, hJ, hX, rfl⟩

theorem famX_hyp (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) : HypOmegaGen (famX Ω c X) :=
  TwinEdge.hypOmegaGen_quotFamily_odd
    (hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X)
    (CFSG.ComponentClassification.OddCore.odd_card ↥X)

theorem famX_twoGroup (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ J ∈ famX Ω c X, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J) := by
  intro J hJ
  obtain ⟨M, hM, hMX, rfl⟩ := exists_of_mem_famX hJ
  have h1 : IsPGroup 2 (↥(TwinADescent.coreAt c M) ⧸
      classicalInvolutionOddCore ↥(TwinADescent.coreAt c M)) :=
    TwinEdge.isPGroup_two_quotient_of_le (TwinADescent.coreAt_le_left c M) (h2 M hM.1)
  have h2C := isPGroup_two_quotient_subgroupOf (TwinADescent.coreAt c M)
    (Subgroup.centralizer ({c} : Set G)) h1
  have h2X := isPGroup_two_quotient_subgroupOf
    ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) X h2C
  exact isPGroup_two_quotient_map (CFSG.ComponentClassification.OddCore.odd_card ↥X) h2X

theorem restrictCFam_q8 (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ L ∈ restrictFamily (cFam Ω c) X, ∃ P : Subgroup ↥X, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup 2) := by
  rintro _ ⟨_, ⟨_, ⟨M, hM, rfl⟩, -, rfl⟩, hMX, rfl⟩
  obtain ⟨P, hP, hPc⟩ := TwinADescent.exists_sylow_centralizer_of_tq hc2 hM.2
  have hPs : IsSylow2In P (TwinADescent.coreAt c M) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hM.2).mpr ⟨hP, hPc⟩
  obtain ⟨e⟩ := hq M hM.1 P hP
  have hs1 : IsSylow2In (P.subgroupOf (Subgroup.centralizer ({c} : Set G)))
      ((TwinADescent.coreAt c M).subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    hPs.subgroupOf (TwinADescent.coreAt_le_centralizer c M)
  have hs2 := hs1.subgroupOf hMX
  refine ⟨_, hs2, ⟨?_⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe (hs1.1.trans hMX)).trans
    ((Subgroup.subgroupOfEquivOfLe hPc).trans e)

theorem famX_q8 (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G))) :
    ∀ J ∈ famX Ω c X, ∀ P : Subgroup (↥X ⧸ classicalInvolutionOddCore ↥X),
      IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup 2) := by
  intro J hJ
  apply forall_sylow_iso_of_exists
  exact TwinThmE.q8_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥X)
    (restrictCFam_q8 hc2 hq X) J hJ

theorem thm4_famX {n : ℕ} (h4 : Thm4RTwinBelow 3 n) (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) (X : Subgroup ↥(Subgroup.centralizer ({c} : Set G)))
    (hlt : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) < n) :
    ∀ J ∈ famX Ω c X, ∀ L ∈ famX Ω c X,
      (¬ ∃ g : ↥X ⧸ classicalInvolutionOddCore ↥X, conjSub g J = L) → Commutes J L :=
  h4 _ hlt (famX Ω c X) (famX_hyp hΩ hc2 X) (famX_twoGroup h2 X) (famX_q8 hc2 hq X)
    (TwinADescent3.aEmpty_quot_coreFamily hΩ hA hc2 X)
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥X)

end Fam

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf2
