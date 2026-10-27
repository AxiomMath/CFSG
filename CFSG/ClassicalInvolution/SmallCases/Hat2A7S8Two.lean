module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8Graph
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected

section Two

theorem sylow16_of_witness' {G : Type} [Group G] [Finite G] {J R : Subgroup G}
    (hw : A7Witness J) (hR : IsSylow2In R J) : 16 ≤ Nat.card R := by
  obtain ⟨π, zE, hcov, -⟩ := Hat2A7.exists_cover_of_witness hw
  rw [Uniform.natCard_isSylow2In_eq hR]
  have h5040 : Nat.card (↥J ⧸ classicalInvolutionOddCore ↥J) = 5040 := hcov.card_E
  rw [h5040]
  have h4 : (Nat.factorization 5040) 2 = 4 := by decide +kernel
  rw [h4]
  norm_num


theorem a7C27_2_proved :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
      (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8A7 Ω K J S R T W z t →
        ¬ DConnected Ω → dComp Ω K = dstarComp Ω K := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hΩ : AschTight.HypOmegaGen Ω := hs.stand.hyp
  have hw : ∀ L ∈ Ω, A7Witness L := fun L hL =>
    (hs.stand.classical L hL).choose_spec.witness
  have h16 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → 16 ≤ Nat.card P :=
    fun M hM P hP => sylow16_of_witness' (hw M hM) hP
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  exact Hat2A7S8.dComp_eq_dstarComp hΩ hw h16 hnt hs.stand.mem

end Two

end CFSG.ClassicalInvolution.Hat2A7S
