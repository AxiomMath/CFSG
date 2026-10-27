module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


section Hyp

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem hullFam_quat {k : ℕ} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup k)) :
    ∀ L ∈ hullFam Ω c, ∃ P : Subgroup ↥(coreHull Ω c), IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup k) := by
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

theorem secFam_quat {k : ℕ} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup k)) :
    ∀ J ∈ TwinDisc.secFam Ω c, ∀ P : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)),
      IsSylow2In P J → Nonempty (↥P ≃* QuaternionGroup k) := by
  intro J hJ
  apply forall_sylow_iso_of_exists
  exact quatSylow_quot_odd (CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c))
    (hullFam_quat hc2 hq) J hJ

end Hyp

section Dich

variable {X : Type} [Group X] [Finite X] {Δ : Set (Subgroup X)}

theorem dichotomy_of_thm4RTwinR {r n : ℕ} (h4 : Thm4RTwinBelow r n) (hlt : Nat.card X < n)
    (hΔ : HypOmegaGen Δ) (h2 : ∀ J ∈ Δ, IsPGroup 2 (↥J ⧸ classicalInvolutionOddCore ↥J))
    (hq : ∀ J ∈ Δ, ∀ P : Subgroup X, IsSylow2In P J →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ L ∈ Δ, AEmpty Δ L) (hO : classicalInvolutionOddCore X = ⊥) {L : Subgroup X}
    (hL : L ∈ Δ) :
    (∀ M ∈ Δ, M ∈ dstarComp Δ L) ∨ (∀ M ∈ Δ, ∃ y : X, conjSub y L = M) := by
  have h4' := h4 X hlt Δ hΔ h2 hq hA hO
  by_cases hall : ∀ M ∈ Δ, ∃ y : X, conjSub y L = M
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨M₀, hM₀, hM₀c⟩ := hall
  have hLM₀ : M₀ ≠ L := fun h => hM₀c 1 (by rw [conjSub_one, h])
  have hc0 : Commutes L M₀ := h4' L hL M₀ hM₀ (fun ⟨g, hg⟩ => hM₀c g hg)
  have hadj0 : dstarAdj Δ L M₀ := dstarAdj_of_commutes_gen hΔ hM₀ hLM₀ hc0.symm
  intro M hM
  by_cases hMc : ∃ y : X, conjSub y L = M
  · obtain ⟨y, rfl⟩ := hMc
    have hnot : ¬ ∃ g : X, conjSub g (conjSub y L) = M₀ := by
      rintro ⟨g, hg⟩
      exact hM₀c (g * y) (by rw [conjSub_mul]; exact hg)
    have hc1 : Commutes (conjSub y L) M₀ := h4' _ hM M₀ hM₀ hnot
    have hne : M₀ ≠ conjSub y L := fun h => hnot ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single hadj0)
      (dstarAdj_of_commutes_gen hΔ hM hne.symm hc1)
  · have hc : Commutes L M := h4' L hL M hM (fun ⟨g, hg⟩ => hMc ⟨g, hg⟩)
    have hne : M ≠ L := fun h => hMc ⟨1, by rw [conjSub_one, h]⟩
    exact Relation.ReflTransGen.single (dstarAdj_of_commutes_gen hΔ hM hne hc.symm)

end Dich

section SecDich

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem dichotomy_secFamR {r n : ℕ} (h4 : Thm4RTwinBelow r n)
    (hlt : Nat.card (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) < n)
    (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h2 : ∀ M ∈ Ω, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M))
    (hq : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M →
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))))
    (hA : ∀ M ∈ Ω, AEmpty Ω M) {B : Subgroup G} (hB : B ∈ tqMembers3 Ω c) :
    (∀ M ∈ TwinDisc.secFam Ω c, M ∈ dstarComp (TwinDisc.secFam Ω c) (secImg Ω c B)) ∨
      (∀ M ∈ TwinDisc.secFam Ω c, ∃ y, conjSub y (secImg Ω c B) = M) :=
  dichotomy_of_thm4RTwinR h4 hlt (hypOmegaGen_secFam hΩ hc2) (secFam_twoGroup h2)
    (secFam_quat hc2 hq) (secFam_aEmpty hΩ hA hc2) oddCore_quot_eq_bot (secImg_mem_secFam hB)

end SecDich

end CFSG.CGT.PushingUpLit.SolKNA.R4
