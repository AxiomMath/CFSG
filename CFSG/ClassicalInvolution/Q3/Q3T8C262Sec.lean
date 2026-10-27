module

public import CFSG.ClassicalInvolution.Q3.Q3T8C262Type
public import CFSG.ClassicalInvolution.Q3.Q3T7M00
public import CFSG.ClassicalInvolution.Uniform.UExact

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Sect

open CFSG.Open (classicalInvolutionOddCore)
open scoped commutatorElement
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Asc77
  CFSG.Assembly.LowTwoRank

section Exact


variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)}

theorem exactMembers_of_card_eq (hΦ : HypOmegaModU (.sl2 3 1) Φ)
    (hc : ∀ L ∈ Φ, Nat.card L = 24) : ExactMembers Φ := by
  intro L hL
  obtain ⟨z, hz⟩ := hΦ.classical L hL
  exact hz.oddCore_eq_bot_of_natCard_eq (by norm_num : (3 : ℕ) ^ 1 = 3) (hc L hL)

theorem hypOmega_of_modU_exact (h : HypOmegaModU (.sl2 3 1) Φ) (hex : ExactMembers Φ) :
    Q3T8.Asc77.HypOmega Φ where
  conjInvariant := h.conjInvariant
  classical := h.classical
  exact := hex
  omega4 K hK J hJ hKJ := by
    refine ⟨(h.omega4 K hK J hJ hKJ).1, fun he => ?_⟩
    have hle := (h.omega4 K hK J hJ hKJ).2 he
    have hK1 : oddCoreOf K = ⊥ := oddCoreOf_eq_bot_of_exact hex hK
    have hJ1 : oddCoreOf J = ⊥ := oddCoreOf_eq_bot_of_exact hex hJ
    have hcomm : ⁅K, J⁆ = ⊥ := by
      rw [eq_bot_iff]
      refine le_trans hle ?_
      rw [hK1]
      exact inf_le_left
    intro a ha b hb
    have : ⁅a, b⁆ ∈ ⁅K, J⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  omega5 := h.omega5

end Exact

section Section


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hypOmega_section_omegaNbrGen {K : Subgroup G} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hn : CITBelowT (.sl2 3 1) (Nat.card G))
    (hX : omegaNbrGen Ω K ≠ ⊤) (hne : (restrictFamily Ω (omegaNbrGen Ω K)).Nonempty) :
    Q3T8.Asc77.HypOmega (oddQuotientFamily (restrictFamily Ω (omegaNbrGen Ω K))) := by
  set X : Subgroup G := omegaNbrGen Ω K with hXdef
  have hGen := s26_genSection_omegaNbrGen (K := K) hΩ hA
  have hcardX : Nat.card ↥X < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group X)
      (fun h => hX (Subgroup.eq_top_of_card_eq X h))
  have hL : layerHull Ω X = X := s26_layerHull_omegaNbrGen Ω K
  have hcls : InClassU (.sl2 3 1) (restrictFamily Ω X) :=
    Q3T8.Asc77.inClassU_restrict_hull hΩ hL hne
  obtain ⟨ι, -, ⟨D₀⟩⟩ := (hn ↥X hcardX _ hcls).toLieSystemU
  exact hypOmega_of_modU_exact hGen.modU (exactMembers_of_card_eq hGen.modU
    (D₀.card_eq (by norm_num)))

theorem hypOmega_section_of_hull {Λ : Subgroup G} (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hA : ∀ L ∈ Ω, AEmpty Ω L) (hn : CITBelowT (.sl2 3 1) (Nat.card G))
    (hΛ : Λ ≠ ⊤) (hL : layerHull Ω Λ = Λ) (hne : (restrictFamily Ω Λ).Nonempty) :
    Q3T8.Asc77.HypOmega (oddQuotientFamily (restrictFamily Ω Λ)) := by
  have hGen : GenSection (oddQuotientFamily (restrictFamily Ω Λ)) := by
    have := genSection_layerHull hΩ hA Λ
    rwa [hL] at this
  have hcard : Nat.card ↥Λ < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group Λ)
      (fun h => hΛ (Subgroup.eq_top_of_card_eq Λ h))
  have hcls : InClassU (.sl2 3 1) (restrictFamily Ω Λ) :=
    Q3T8.Asc77.inClassU_restrict_hull hΩ hL hne
  obtain ⟨ι, -, ⟨D₀⟩⟩ := (hn ↥Λ hcard _ hcls).toLieSystemU
  exact hypOmega_of_modU_exact hGen.modU (exactMembers_of_card_eq hGen.modU
    (D₀.card_eq (by norm_num)))

end Section

end CFSG.ClassicalInvolution.Q3.Q3T8.Sect
