module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUGen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.ExitU
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open scoped commutatorElement

section Residual

section Abstract

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem twin_only_two_group (h4 : Thm4RTwinBelow 3 n) (hlt : Nat.card X < n) (hS : Q8Section X Φ)
    {A A' : Subgroup X} (hA : A ∈ Φ) (hA' : A' ∈ Φ) (h2A : IsPGroup 2 A) (h2A' : IsPGroup 2 A')
    (hnb : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A') (hnb' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A)
    (hnot : ¬ ∃ g : X, conjSub g A = A') : ∃ k : ℕ, Nat.card X = 2 ^ k := by
  have h4' := h4 X hlt Φ hS.hyp hS.two hS.q8 hS.aEmpty hS.oddFree
  have hcA : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A = M) → M = A' := by
    intro M hM hn
    have hMA : M ≠ A := fun h => hn ⟨1, by rw [conjSub_one, h]⟩
    exact hnb M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A hA M hM hn))
  have hcA' : ∀ M ∈ Φ, (¬ ∃ g : X, conjSub g A' = M) → M = A := by
    intro M hM hn
    have hMA : M ≠ A' := fun h => hn ⟨1, by rw [conjSub_one, h]⟩
    exact hnb' M hM (MuTab.mem_omegaNbr_of_commutes hM hMA (h4' A' hA' M hM hn))
  have hall : ∀ M ∈ Φ, M = A ∨ M = A' := by
    intro M hM
    by_cases hM1 : ∃ g : X, conjSub g A = M
    · left
      obtain ⟨g, hg⟩ := hM1
      refine hcA' M hM ?_
      rintro ⟨g', hg'⟩
      exact hnot ⟨g'⁻¹ * g, by rw [conjSub_mul, hg, ← hg', conjSub_inv_conjSub]⟩
    · right
      exact hcA M hM hM1
  have hAn : A.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc : conjSub g A ∈ Φ := hS.hyp.conjInvariant g A hA
    rcases hall _ hc with h | h
    · rw [← h]; exact conj_mem_conjSub ha
    · exact absurd ⟨g, h⟩ hnot
  have hA'n : A'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hc : conjSub g A' ∈ Φ := hS.hyp.conjInvariant g A' hA'
    rcases hall _ hc with h | h
    · exact absurd ⟨g⁻¹, by rw [← h, conjSub_inv_conjSub]⟩ hnot
    · rw [← h]; exact conj_mem_conjSub ha
  have hsup : IsPGroup 2 ↥(A ⊔ A') := IsPGroup.to_sup_of_normal_right h2A h2A'
  have htop : A ⊔ A' = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    exact iSup₂_le fun M hM => by
      rcases hall M hM with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
  rw [htop] at hsup
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hsup)
  exact ⟨k, by rw [← hk]; exact (Subgroup.card_top (G := X)).symm⟩

end Abstract

section V3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem secImg_isPGroup' {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G} {J : Subgroup G}
    (hJ2 : IsPGroup 2 J) : IsPGroup 2 (secImg Ω c J) := by
  have h1 : IsPGroup 2 (TwinADescent.coreAt c J) := hJ2.to_le (TwinADescent.coreAt_le_left c J)
  have h2 : IsPGroup 2 ↥((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    h1.comap_subtype
  have h3 : IsPGroup 2 ↥(((TwinADescent.coreAt c J).subgroupOf (Subgroup.centralizer ({c} : Set G))).subgroupOf
      (coreHull Ω c)) := h2.comap_subtype
  exact h3.of_surjective ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).subgroupMap _)
    ((QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c))).subgroupMap_surjective _)

end V3

end Residual

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
