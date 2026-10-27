module

public import CFSG.ClassicalInvolution.Asc77.AscT8ZC2
import CFSG.ClassicalInvolution.Asc77.AscT8ZC2Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab T8YY
open scoped commutatorElement

namespace T8ZZ

variable {p f : ℕ} [Fact p.Prime]


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem ncard_commonNbr_le [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) {M : Subgroup G}
    (hM : M ∈ omegaNbr Ω K) : (omegaNbr Ω K ∩ omegaNbr Ω M).ncard ≤ 2 := by
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨s, hs'⟩ := hΩ.exists_uniqueInvolution hp hq hM.1
  have hnc : ¬ DbarConnected Ω W := T8X.not_dbarConnected_of_ne hs hne
  have hframe := exists_fuzzyFrame hs hμ hnc
  obtain ⟨S', R', T', W', hstd⟩ :=
    c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hs.hz M hM s hs'
  have hμ' := muIsoWylD4_transfer hp hq hΩ hs.hW.1 hstd.hW.1 hμ
  have hnc' : ¬ DbarConnected Ω W' := T8X.not_dbarConnected_of_ne hstd hne
  obtain ⟨F'⟩ := exists_frameData hstd hμ' hnc'
  have hα' : alphaOf (Subgroup.closure ({s, z} : Set G)) = ⊥ := by
    rw [(T8U.alphaOf_eq_of_omegaNbr_frame hs.stand hs.noTwins hframe hs.hz hs' hs.ht hM
      hs.hJ).symm]
    exact hα
  have hsub : omegaNbr Ω K ∩ omegaNbr Ω M ⊆ {(F'.ρ 2).K, (F'.ρ 3).K} := by
    rintro L ⟨hLK, hLM⟩
    obtain ⟨j, hj0, hjL⟩ := commonNbr_mem_frame hstd (huni M hM s hs') hα' F' hLK hLM
    have hj1 : j ≠ 1 := by
      rintro rfl
      exact hLM.2.1 (by rw [hjL, F'.h1])
    fin_cases j
    · exact absurd rfl hj0
    · exact absurd rfl hj1
    · exact Or.inl hjL
    · exact Or.inr hjL
  refine (Set.ncard_le_ncard hsub (Set.toFinite _)).trans ?_
  refine (Set.ncard_insert_le _ _).trans ?_
  rw [Set.ncard_singleton]

theorem commonNbr_frame_eq [IsSimpleGroup G] (hs : Std8 p f Ω K J S R T W z t)
    (hdisc : ¬ DConnected Ω) (hμ : MuIsoWylD4 Ω W) (hne : dComp Ω K ≠ dstarComp Ω K)
    (huni : ∀ M ∈ omegaNbr Ω K, ∀ s : G, IsUniqueInvolution M s →
      ¬ DConnected (T8.layerFamQ Ω (z * s)))
    (hα : alphaOf (Subgroup.closure ({t, z} : Set G)) = ⊥) (F : FrameData Ω W K J z t)
    {j : Fin 4} (hj : j ≠ 0) {L : Subgroup G} (hLK : L ∈ omegaNbr Ω K)
    (hLj : L ∈ omegaNbr Ω (F.ρ j).K) : ∃ i : Fin 4, i ≠ 0 ∧ i ≠ j ∧ L = (F.ρ i).K := by
  exact commonNbr_frame_eq_of F hj hLK hLj
    (fun hM => ncard_commonNbr_le hs hdisc hμ hne huni hα hM)

end T8ZZ

end CFSG.ClassicalInvolution.Asc77
