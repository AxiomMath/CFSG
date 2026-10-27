module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape

public section

namespace CFSG.ClassicalInvolution.RouteD.TWY

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_layerOne (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hcard : D.card = 1) (i : Fin D.card)
    (hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4)
    {J J₂ : Subgroup G} (hJ : J ∈ centralizingMembers Ω {x})
    (hJ₂ : J₂ ∈ centralizingMembers Ω {x}) (hJJ₂ : Commutes J₂ J) (hne : J₂ ≠ J)
    (hone : ∀ N ∈ centralizingMembers Ω {x}, Commutes N J → N = J₂) :
    ∃ R₀ ∈ compFund D i,
      Nat.card {S : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K //
        S ∈ compFund D i ∧ Commutes S R₀} = 1 := by
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers Ω x D i := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i ▸ hj⟩
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D hp2 hq4 hD
  obtain ⟨R₀, hR₀⟩ := exists_corr_left hΩ hex D (hall J hJ)
  obtain ⟨R₂, hR₂⟩ := exists_corr_left hΩ hex D (hall J₂ hJ₂)
  refine ⟨R₀, hR₀.2.1, ?_⟩
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨R₂, hR₂.2.1, (corr_commutes hΩ hP1 (hperf i) hR₂ hR₀).mp hJJ₂⟩, ?_⟩
  rintro ⟨S, hS, hSc⟩
  obtain ⟨N, hN⟩ := exists_corr_right hΩ D (hsc i) hS
  have hNJ : Commutes N J := (corr_commutes hΩ hP1 (hperf i) hN hR₀).mpr hSc
  have hNeq := hone N hN.1 hNJ
  subst hNeq
  exact Subtype.ext (corr_unique_left (hperf i) hN hR₂)


theorem exists_corr_commuting (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hcard : D.card = 1) (i : Fin D.card)
    (hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4) {J : Subgroup G}
    (hJ : J ∈ centralizingMembers Ω {x}) :
    ∃ R₀ ∈ compFund D i, Corr Ω x D i J R₀ ∧
      Nat.card {S : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K //
        S ∈ compFund D i ∧ Commutes S R₀} =
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers Ω {x} ∧ Commutes N J} := by
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  have hall : ∀ N ∈ centralizingMembers Ω {x}, N ∈ compMembers Ω x D i := by
    intro N hN
    obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
    exact ⟨hN, hsub.elim j i ▸ hj⟩
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨hsc, hperf⟩ := componentFacts_of_no_exotic D hp2 hq4 hD
  obtain ⟨R₀, hR₀⟩ := exists_corr_left hΩ hex D (hall J hJ)
  refine ⟨R₀, hR₀.2.1, hR₀, ?_⟩
  rw [show Nat.card {S : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K //
        S ∈ compFund D i ∧ Commutes S R₀} =
      Set.ncard {S : Subgroup (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).K |
        S ∈ compFund D i ∧ Commutes S R₀} from Nat.card_coe_set_eq _]
  symm
  have hex' : ∀ N ∈ {N : Subgroup G | N ∈ centralizingMembers Ω {x} ∧ Commutes N J},
      ∃ R, Corr Ω x D i N R := fun N hN => exists_corr_left hΩ hex D (hall N hN.1)
  choose! R hR using hex'
  refine Set.ncard_congr (fun N _ => R N) ?_ ?_ ?_
  · intro N hN
    exact ⟨(hR N hN).2.1, (corr_commutes hΩ hP1 (hperf i) (hR N hN) hR₀).mp hN.2⟩
  · intro N₁ N₂ h₁ h₂ h
    exact corr_unique_right hΩ hP1 (hR N₁ h₁) (h ▸ hR N₂ h₂)
  · rintro S ⟨hS, hSc⟩
    obtain ⟨N, hN⟩ := exists_corr_right hΩ D (hsc i) hS
    have hNJ : Commutes N J := (corr_commutes hΩ hP1 (hperf i) hN hR₀).mpr hSc
    refine ⟨N, ⟨hN.1, hNJ⟩, ?_⟩
    exact corr_unique_left (hperf i) (hR N ⟨hN.1, hNJ⟩) hN


theorem exists_corr_of_card_one (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hcard : D.card = 1) (i : Fin D.card)
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) : ∃ R, Corr Ω x D i N R := by
  have hsub : Subsingleton (Fin D.card) := Fin.subsingleton_iff_le_one.mpr hcard.le
  obtain ⟨j, hj⟩ := exists_range_of_mem D (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  exact exists_corr_left hΩ hex D ⟨hN, hsub.elim j i ▸ hj⟩

theorem exists_three_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (hcard : D.card = 1) (i : Fin D.card)
    (hD : ∀ j, D.tag j ≠ .G2 ∧ D.tag j ≠ .trialityD4) {J₁ J₂ J₃ : Subgroup G}
    (h₁ : J₁ ∈ centralizingMembers Ω {x}) (h₂ : J₂ ∈ centralizingMembers Ω {x})
    (h₃ : J₃ ∈ centralizingMembers Ω {x}) (n₁₂ : J₁ ≠ J₂) (n₁₃ : J₁ ≠ J₃) (n₂₃ : J₂ ≠ J₃)
    (c₁₂ : Commutes J₁ J₂) (c₁₃ : Commutes J₁ J₃) (c₂₃ : Commutes J₂ J₃) :
    ∃ A ∈ compFund D i, ∃ B ∈ compFund D i, ∃ C ∈ compFund D i, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧
      Commutes A B ∧ Commutes A C ∧ Commutes B C := by
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨-, hperf⟩ := componentFacts_of_no_exotic D hp2 hq4 hD
  obtain ⟨A, hA⟩ := exists_corr_of_card_one hΩ hex D hcard i h₁
  obtain ⟨B, hB⟩ := exists_corr_of_card_one hΩ hex D hcard i h₂
  obtain ⟨C, hC⟩ := exists_corr_of_card_one hΩ hex D hcard i h₃
  refine ⟨A, hA.2.1, B, hB.2.1, C, hC.2.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl
    exact n₁₂ (corr_unique_right hΩ hP1 hA hB)
  · rintro rfl
    exact n₁₃ (corr_unique_right hΩ hP1 hA hC)
  · rintro rfl
    exact n₂₃ (corr_unique_right hΩ hP1 hB hC)
  · exact (corr_commutes hΩ hP1 (hperf i) hA hB).mp c₁₂
  · exact (corr_commutes hΩ hP1 (hperf i) hA hC).mp c₁₃
  · exact (corr_commutes hΩ hP1 (hperf i) hB hC).mp c₂₃

end CFSG.ClassicalInvolution.RouteD.TWY
