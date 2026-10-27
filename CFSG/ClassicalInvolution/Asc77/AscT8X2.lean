module

public import CFSG.ClassicalInvolution.Asc77.AscT8Y3
public import CFSG.ClassicalInvolution.Asc77.AscMuTabNonab
public import CFSG.ClassicalInvolution.Asc77.AscMuTabWyl
import CFSG.ClassicalInvolution.Asc77.AscT8X2Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.MuTab

namespace T8X


variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem not_dbarConnected_of_ne (hs : Std8 p f Ω K J S R T W z t)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  thompsonGraphAll G Ω (T8.partIHyp_of_std8 hs) hs.stand.mem hne hs.hW.1

theorem not_muIsoS3_or_S4 {W : Subgroup G} (h : MuIsoWylD4 Ω W) :
    ¬ MuIsoS3 Ω W ∧ ¬ MuIsoS4 Ω W := by
  obtain ⟨e⟩ := h
  constructor
  · rintro ⟨e3⟩
    exact MuTab.not_wyl_equiv_perm3 ⟨e.symm.trans e3⟩
  · rintro ⟨e4⟩
    exact MuTab.not_wyl_equiv_perm4 ⟨e.symm.trans e4⟩

omit [Finite G] in
theorem exists_four {α : Type*} {C : Set α} (hC : C.ncard = 4) {a b : α}
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ c d : α, C = {a, b, c, d} ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b :=
  CFSG.ClassicalInvolution.Asc77.T8X.exists_four_gen hC ha hb hab

theorem ncard_cent_eq_four (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 := by
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hnot := not_muIsoS3_or_S4 hμ
  have key := muIso_of_cent hP hW hnc ρ
  rcases thompsonClique G Ω hP W hW hnc (muTabElt ρ) (muTabElt_mem ρ) with h | h | ⟨h, -⟩
  · exact absurd (key.1 h) hnot.1
  · exact absurd (key.2.1 h) hnot.2
  · exact h

theorem exists_frame (hs : Std8 p f Ω K J S R T W z t) (hμ : MuIsoWylD4 Ω W)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ ρ : Fin 4 → Rep Ω W, (ρ 0).K = K ∧ (ρ 1).K = J ∧ (∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K) ∧
      (∀ i j, i ≠ j → (ρ j).K ∈ omegaNbr Ω (ρ i).K) ∧
      ∀ σ : Rep Ω W, (σ.K = K ∨ σ.K ∈ omegaNbr Ω K) → ∃ i, σ.K = (ρ i).K := by
  classical
  have hp : p ≠ 2 := hs.stand.odd
  have hq : 5 ≤ p ^ f := hs.stand.five
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hP := T8.partIHyp_of_std8 hs
  have hW : W ∈ WSet Ω := hs.hW.1
  have hTT := isTT_muDelta hp hq hΩ hW (thompsonCube G Ω hP W hW)
  have hSt := isStar_muDelta hp hq hΩ hW (thompsonStar G Ω hP W hW)
  set ρ0 := T8.stdRepK hs
  set ρ1 := T8.stdRepJ hs
  have hK0 : ρ0.K = K := T8.stdRepK_K hs
  have hK1 : ρ1.K = J := T8.stdRepJ_K hs
  have hne01 : ρ0.K ≠ ρ1.K := by rw [hK0, hK1]; exact hs.hJ.2.1.symm
  have hd01 : muTabElt ρ0 ≠ muTabElt ρ1 := fun h =>
    hne01 ((muTabElt_eq_iff hP hW ρ0 ρ1).mp h)
  set C := Star3T.cent (muDelta Ω W) (muTabElt ρ0) with hCdef
  have hC4 : C.ncard = 4 := ncard_cent_eq_four hs hμ hnc ρ0
  have h0C : muTabElt ρ0 ∈ C := Star3T.self_mem_cent (muTabElt_mem ρ0)
  have h1C : muTabElt ρ1 ∈ C := ⟨muTabElt_mem ρ1,
    ((muTab_commute_iff hP hW ρ0 ρ1 hne01).mpr (by rw [hK0, hK1]; exact hs.hJ)).symm⟩
  obtain ⟨c, d, hCe, hcd, hca, hcb, hda, hdb⟩ := exists_four hC4 h0C h1C hd01
  have hcC : c ∈ C := by rw [hCe]; simp
  have hdC : d ∈ C := by rw [hCe]; simp
  obtain ⟨ρ2, hρ2⟩ := MuTab.exists_rep_of_mem_muDelta hcC.1
  obtain ⟨ρ3, hρ3⟩ := MuTab.exists_rep_of_mem_muDelta hdC.1
  let ρ : Fin 4 → Rep Ω W := ![ρ0, ρ1, ρ2, ρ3]
  let dd : Fin 4 → ↥(muGroup Ω W) := ![muTabElt ρ0, muTabElt ρ1, c, d]
  have hdd : ∀ i, muTabElt (ρ i) = dd i := by
    intro i; fin_cases i
    · rfl
    · rfl
    · exact hρ2.symm
    · exact hρ3.symm
  have hddC : ∀ i, dd i ∈ C := by
    intro i; fin_cases i
    · exact h0C
    · exact h1C
    · exact hcC
    · exact hdC
  have hddinj : ∀ i j, i ≠ j → dd i ≠ dd j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | skip
    all_goals first
      | exact hd01 | exact fun h => hd01 h.symm
      | exact fun h => hca h.symm | exact hca | exact fun h => hcb h.symm | exact hcb
      | exact fun h => hda h.symm | exact hda | exact fun h => hdb h.symm | exact hdb
      | exact hcd | exact fun h => hcd h.symm
  have hKne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := by
    intro i j hij h
    exact hddinj i j hij (by rw [← hdd i, ← hdd j]; exact (muTabElt_eq_iff hP hW _ _).mpr h)
  obtain ⟨a₁, ha₁, hn₁⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ0)
  have hcommdd : ∀ i j, dd i * dd j = dd j * dd i := fun i j =>
    hTT.isClique_cent hSt (muTabElt_mem ρ0) ha₁ hn₁ (hddC i) (hddC j)
  refine ⟨ρ, hK0, hK1, hKne, ?_, ?_⟩
  · intro i j hij
    exact (muTab_commute_iff hP hW (ρ i) (ρ j) (hKne i j hij)).mp
      (by rw [hdd i, hdd j]; exact hcommdd i j)
  · intro σ hσ
    have hσC : muTabElt σ ∈ C := by
      refine ⟨muTabElt_mem σ, ?_⟩
      rcases hσ with h | h
      · have : muTabElt σ = muTabElt ρ0 := (muTabElt_eq_iff hP hW σ ρ0).mpr (by rw [h, hK0])
        rw [this]
      · by_cases hσK : ρ0.K = σ.K
        · have : muTabElt σ = muTabElt ρ0 := (muTabElt_eq_iff hP hW σ ρ0).mpr hσK.symm
          rw [this]
        · exact ((muTab_commute_iff hP hW ρ0 σ hσK).mpr (by rw [hK0]; exact h)).symm
    rw [hCe] at hσC
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hσC
    rcases hσC with h | h | h | h
    · exact ⟨0, (muTabElt_eq_iff hP hW σ ρ0).mp h⟩
    · exact ⟨1, (muTabElt_eq_iff hP hW σ ρ1).mp h⟩
    · exact ⟨2, (muTabElt_eq_iff hP hW σ ρ2).mp (h.trans hρ2)⟩
    · exact ⟨3, (muTabElt_eq_iff hP hW σ ρ3).mp (h.trans hρ3)⟩

end T8X

end CFSG.ClassicalInvolution.Asc77
