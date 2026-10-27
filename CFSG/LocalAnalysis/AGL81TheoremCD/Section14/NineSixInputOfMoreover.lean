module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FiveTypes
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineSixStar
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.StarQuot
import CFSG.LocalAnalysis.RankThreeUC.AGL81CStarImgEquiv
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CZComp

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

variable {G : Type} [Group G] [Finite G] {M Q H E : Subgroup G}

private theorem exists_isKComp_starImg_eq_of_isComponent (hple : ¬ pLayerIn 3 H ≤ M)
    {C : Subgroup (StarGroup 3 H)} (hC : CFSG.IsComponent C) (hCM : ¬ C ≤ barInf 3 M H) :
    ∃ J : Subgroup G, IsKComp M H J ∧ ¬ J ≤ M ∧ starImg 3 H J = C := by
  obtain ⟨J, hJ, hJeq⟩ :=
    exists_isPComponentIn_starImg_eq (p := 3) (H := H) Nat.prime_three hC
  have hJM : ¬ J ≤ M := by
    intro hJM'
    apply hCM
    have hle : starImg 3 H J ≤ starImg 3 H M :=
      Subgroup.map_mono (Subgroup.comap_mono hJM')
    rwa [hJeq, starImg_eq_barInf] at hle
  exact ⟨J, isKComp_of_isPComponentIn hJ hJM hple, hJM, hJeq⟩

private theorem isL34Type_starImg_of_threeStar {J : Subgroup G}
    (hJ : IsPComponentIn 3 J H) (h : IsL34Type (threeStar J)) :
    IsL34Type ↥(starImg 3 H J) := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hJ
  exact IsL34Type.of_mulEquiv e h

private theorem isA6Type_starImg_of_threeStar {J : Subgroup G}
    (hJ : IsPComponentIn 3 J H) (h : IsA6Type (threeStar J)) :
    IsA6Type ↥(starImg 3 H J) := by
  obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hJ
  exact IsA6Type.of_mulEquiv e h

theorem nineSixInputGen_of_nineSixMoreoverGen (h96 : NineSixMoreoverGen) :
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.NineSixInputGen := by
  intro G _ _ M Q H E hT hH2 h3 hex
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Set (Subgroup (StarGroup 3 H)) :=
    {C | CFSG.IsComponent C ∧ ¬ C ≤ barInf 3 M H}
  obtain ⟨L, hL, hLM, htype⟩ := hex
  obtain ⟨L₀, hL₀, hL₀eq⟩ :=
    exists_isPComponentIn_starImg_eq (p := 3) (H := H) Nat.prime_three hL
  have hple : ¬ pLayerIn 3 H ≤ M := not_pLayerIn_le_of_component hL hLM
  have hL₀M : ¬ L₀ ≤ M := by
    intro hL₀M'
    apply hLM
    have hle : starImg 3 H L₀ ≤ starImg 3 H M :=
      Subgroup.map_mono (Subgroup.comap_mono hL₀M')
    rwa [hL₀eq, starImg_eq_barInf] at hle
  have hL₀K : IsKComp M H L₀ := isKComp_of_isPComponentIn hL₀ hL₀M hple
  have htype₀ : IsL34Type (threeStar L₀) ∨ IsA11Star L₀ := by
    obtain ⟨e⟩ := IsPComponentIn.nonempty_quotEquiv_starImg Nat.prime_three hL₀
    have e' : threeStar L₀ ≃* ↥L := e.trans (MulEquiv.subgroupCongr hL₀eq)
    rcases htype with h34 | h11
    · exact Or.inl (IsL34Type.of_mulEquiv e'.symm h34)
    · exact Or.inr (IsA11Type.of_mulEquiv e'.symm h11)
  rcases h96 G M Q H E hT hH2 h3 hple L₀ hL₀K htype₀ with hsingle | hdouble
  · have hK : IsKComp M H (kSub 3 M H) := by
      rw [hsingle]
      exact hL₀K
    have hcover : ∀ C ∈ S, C = starImg 3 H L₀ := by
      intro C hC
      obtain ⟨hCcomp, hCnot⟩ := hC
      obtain ⟨J, hJK, -, hJeq⟩ :=
        exists_isKComp_starImg_eq_of_isComponent hple hCcomp hCnot
      have hJeqL : J = L₀ := (IsKComp.eq_kSub_of_isKComp_self hK hJK).trans hsingle
      rw [← hJeq, hJeqL]
    have hSsub : S ⊆ ({starImg 3 H L₀} : Set (Subgroup (StarGroup 3 H))) := by
      intro C hC
      rw [Set.mem_singleton_iff]
      exact hcover C hC
    have hcard : S.ncard ≤ 2 := by
      refine (Set.ncard_le_ncard hSsub (Set.finite_singleton _)).trans ?_
      rw [Set.ncard_singleton]
      norm_num
    refine ⟨?_, ?_⟩
    · exact hcard
    · intro C₁ C₂ hC₁ hC₁not hC₂ hC₂not hne
      exact absurd ((hcover C₁ ⟨hC₁, hC₁not⟩).trans
        (hcover C₂ ⟨hC₂, hC₂not⟩).symm) hne
  · obtain ⟨I, hIne, hI, hkSub, huniq, hSL, hrest⟩ := hdouble
    have hcover : ∀ C ∈ S, C = starImg 3 H L₀ ∨ C = starImg 3 H I := by
      intro C hC
      obtain ⟨hCcomp, hCnot⟩ := hC
      obtain ⟨J, hJK, -, hJeq⟩ :=
        exists_isKComp_starImg_eq_of_isComponent hple hCcomp hCnot
      rcases huniq J hJK with hJL | hJI
      · exact Or.inl (by rw [← hJeq, hJL])
      · exact Or.inr (by rw [← hJeq, hJI])
    have hSsub : S ⊆ ({starImg 3 H L₀, starImg 3 H I} : Set (Subgroup (StarGroup 3 H))) := by
      intro C hC
      rcases hcover C hC with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    have hcard : S.ncard ≤ 2 := by
      refine (Set.ncard_le_ncard hSsub (Set.Finite.insert (starImg 3 H L₀)
        (Set.finite_singleton (starImg 3 H I)))).trans ?_
      have hle := Set.ncard_insert_le (starImg 3 H L₀)
        ({starImg 3 H I} : Set (Subgroup (StarGroup 3 H)))
      rw [Set.ncard_singleton] at hle
      simpa using hle
    have hL₀ty : IsL34Type ↥(starImg 3 H L₀) :=
      isL34Type_starImg_of_threeStar hL₀ hSL.1
    have hIty : IsL34Type ↥(starImg 3 H I) ∨ IsA6Type ↥(starImg 3 H I) := by
      rcases hrest with hSLI | hA6I
      · exact Or.inl (isL34Type_starImg_of_threeStar hI.isPComponentIn hSLI.1)
      · exact Or.inr (isA6Type_starImg_of_threeStar hI.isPComponentIn hA6I.1)
    have htypeOf : ∀ C ∈ S, IsL34Type ↥C ∨ IsA6Type ↥C := by
      intro C hC
      rcases hcover C hC with h | h
      · rw [h]
        exact Or.inl hL₀ty
      · rw [h]
        exact hIty
    refine ⟨?_, ?_⟩
    · exact hcard
    · intro C₁ C₂ hC₁ hC₁not hC₂ hC₂not hne
      exact ⟨htypeOf C₁ ⟨hC₁, hC₁not⟩, htypeOf C₂ ⟨hC₂, hC₂not⟩⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
