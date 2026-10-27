module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Dispatch

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmallData.false_of_spIn (hP5 : StmtSmallSPIn) (hI4 : StmtSmallSPInThree)
    (hG4 : D1SmallA6) (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))) {z : G}
    (hz : D1SmallCZElt p H R K z) (hLa : D1SmallLa p M H Rbar K) (hSP : D1CzSP p z)
    (hout : ¬ D1CzOutside p z) : False := by
  by_cases h5 : 5 ≤ p
  · exact hP5 G p P M H R Rbar K hd huniq z hz hLa h5 hSP hout
  have hp3 : p = 3 := by
    have h2 := hd.cfg.red.prime.two_le
    have hne := hd.cfg.red.ne_two
    have h4 : p ≠ 4 := by
      rintro rfl
      exact absurd hd.cfg.red.prime (by decide)
    omega
  by_cases hJ : IsAltTwoP 3 K ∧ D1CzJ3 p z
  · exact hG4 G p P M H R Rbar K hd huniq z hz hp3 hJ.1 (Or.inr ⟨hSP, hJ.2⟩)
  · exact hI4 G p P M H R Rbar K hd huniq z hz hLa hp3 hSP hout hJ

theorem D1OneSmallData.false_of_czRoute (hP5 : StmtSmallSPIn) (hP6 : StmtSmallSPOut)
    (hI1 : StmtSmallBOne) (hI4 : StmtSmallSPInThree) (hI2 : StmtSmallBZeroOdd)
    (hI3 : StmtSmallGEV) (hG1 : D1SmallIbEV) (hG2 : D1SmallSPL) (hG3 : D1SmallKC)
    (hG4 : D1SmallA6) (hG5 : D1SmallU33) (hG6 : D1SmallL34) (hG7 : D1SmallFi22)
    (hd : D1OneSmallData p P M H R Rbar K)
    (huniq : D1UniqueOver H R (nclIn H (d1LiftX p H R K))) {z : G}
    (hz : D1SmallCZElt p H R K z) (hLa : D1SmallLa p M H Rbar K)
    (hOP : D1SmallOpenPosIf p M H Rbar K)
    (hgp : ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)))
    (hfi : p = 5 → IsFi22 K → 3 ∉ GLBBetaFour G) : False := by
  by_cases hSP : D1CzSP p z
  · by_cases hout : D1CzOutside p z
    · by_cases hspl : IsSPLFamily p K
      · exact hG2 G p P M H R Rbar K hd huniq z hz hspl hSP hout hOP
      · exact hP6 G p P M H R Rbar K hd huniq z hz hLa hSP hout hspl
    · exact hd.false_of_spIn hP5 hI4 hG4 huniq hz hLa hSP hout
  by_cases hiso : D1CzIso p z K
  swap
  · exact hG3 G p P M H R Rbar K hd huniq z hz hSP hiso hOP
  by_cases hB0 : D1CzB0 p R z
  · by_cases hFi : p = 5 ∧ IsFi22 K
    · exact hG7 G p P M H R Rbar K hd huniq z hz hFi.1 hFi.2 (hfi hFi.1 hFi.2) hB0 hiso
    by_cases hL : p = 3 ∧ IsLinThreeFour K ∧ D1CzEven p z
    · exact hG6 G p P M H R Rbar K hd huniq z hz hL.1 hL.2.1
        (Or.inr (Or.inr ⟨hOP hFi, hSP, hiso, Or.inl ⟨hB0, hL.2.2⟩⟩))
    by_cases hU : p = 3 ∧ IsSmallUnitary 3 K
    · exact hG5 G p P M H R Rbar K hd huniq z hz hU.1 hU.2 hB0 hiso hOP
    by_cases hA : p = 3 ∧ IsAltTwoP 3 K ∧ (D1SmallExotic p H R K z ∨ D1CzEven p z)
    · exact hG4 G p P M H R Rbar K hd huniq z hz hA.1 hA.2.1 (Or.inl ⟨hB0, hiso, hA.2.2, hOP⟩)
    by_cases hE : D1CzEven p z
    · have hA' : ¬ (p = 3 ∧ IsAltTwoP 3 K) := fun h => hA ⟨h.1, h.2, Or.inr hE⟩
      have hL' : ¬ (p = 3 ∧ IsLinThreeFour K) := fun h => hL ⟨h.1, h.2, hE⟩
      by_cases hIa : D1SmallIa p H K
      · exact hI3 G p P M H R Rbar K hd huniq z hz hIa hB0 hE hiso hA' hU hL' hFi
      · exact hG1 G p P M H R Rbar K hd huniq z hz hIa hB0 hE hiso hA' hU hL' hFi hgp
          (hOP hFi)
    · exact hI2 G p P M H R Rbar K hd huniq z hz hB0 hE hiso
        (fun h => hA ⟨h.1, h.2.1, Or.inl h.2.2⟩) hU hFi hLa
  · by_cases hL : p = 3 ∧ IsLinThreeFour K ∧ D1CzOuterP p z
    · exact hG6 G p P M H R Rbar K hd huniq z hz hL.1 hL.2.1
        (Or.inr (Or.inr ⟨hOP (fun h => absurd (hL.1.symm.trans h.1) (by decide)), hSP, hiso,
          Or.inr ⟨hB0, hL.2.2⟩⟩))
    · exact hI1 G p P M H R Rbar K hd huniq z hz hSP hB0 hiso hLa
        (fun h3 hL34 h => hL ⟨h3, hL34, h⟩)

end Dispatch

theorem d1OneSmallUnique_of (hP1 : StmtSmallGuest) (hP2 : StmtSmallPosA)
    (hP3a : StmtSmallPoszSP) (hP3b : StmtSmallPoszOut) (hP4 : StmtSmallPosT)
    (hP5 : StmtSmallSPIn) (hP6 : StmtSmallSPOut) (hI1 : StmtSmallBOne)
    (hI2 : StmtSmallBZeroOdd) (hI3 : StmtSmallGEV) (hI4 : StmtSmallSPInThree)
    (hG1 : D1SmallIbEV) (hG2 : D1SmallSPL) (hG3 : D1SmallKC) (hG4 : D1SmallA6)
    (hG5 : D1SmallU33) (hG6 : D1SmallL34) (hG7 : D1SmallFi22) : D1OneSmallUnique := by
  intro G _ _ p P M H R Rbar K hd huniq
  obtain ⟨z, hz⟩ := hd.exists_czElt
  by_cases hGP : (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) ∨
      (p = 5 ∧ IsFi22 K ∧ 3 ∈ GLBBetaFour G)
  · exact hP1 G p P M H R Rbar K hd hGP
  have hgp : ¬ (IsAltTwoP p K ∧ 7 ≤ p ∧ (11 ≤ p ∨ 3 ∈ GLBBetaFour G)) :=
    fun h => hGP (Or.inl h)
  have hfi : p = 5 → IsFi22 K → 3 ∉ GLBBetaFour G := fun h5 hF h3 => hGP (Or.inr ⟨h5, hF, h3⟩)
  by_cases hLa : D1SmallLa p M H Rbar K
  swap
  · simp only [D1SmallLa, not_imp, not_and_or, not_not] at hLa
    obtain ⟨h3, hL34, hbc⟩ := hLa
    exact hG6 G p P M H R Rbar K hd huniq z hz h3 hL34 (hbc.imp id Or.inl)
  have cz := fun hOP => hd.false_of_czRoute hP5 hP6 hI1 hI4 hI2 hI3 hG1 hG2 hG3 hG4 hG5 hG6
    hG7 huniq hz hLa hOP hgp hfi
  by_cases hF : p = 5 ∧ IsFi22 K
  · exact cz fun hF' => absurd hF hF'
  by_cases hVK : d1MapPCore p M H ⊓ K = ⊥
  · by_cases hV0 : d1MapPCore p M H = ⊥
    · exact cz fun _ => ⟨fun _ => hV0, fun h => absurd hVK h, fun h => absurd hVK h⟩
    · have hSP := hP3a G p P M H R Rbar K hd hLa hF hV0 hVK z hz
      by_cases hout : D1CzOutside p z
      · exact hP3b G p P M H R Rbar K hd hLa hF hV0 hVK z hz hout
      · exact hd.false_of_spIn hP5 hI4 hG4 huniq hz hLa hSP hout
  · by_cases hVC : d1MapPCore p M H ⊓
        Subgroup.centralizer (K : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥
    · by_cases hT : D1SmallIa p H K ∧ 5 ≤ p ∧ (IsSmallLinTwo p K ∨ IsSmallUnitary p K) ∧
          ¬ D1SmallPosZ p M H Rbar K
      · exact hP4 G p P M H R Rbar K hd huniq hF hVK hVC hT.1 hT.2.1 hT.2.2.1 hT.2.2.2
      · exact cz fun _ => ⟨fun h => absurd h hVK, fun _ h => absurd hVC h,
          fun _ _ hIa h5 hLU => by_contra fun hZ => hT ⟨hIa, h5, hLU, hZ⟩⟩
    · by_cases hZ : D1SmallPosZ p M H Rbar K
      · exact cz fun _ => ⟨fun h => absurd h hVK, fun _ _ => hZ, fun _ h => absurd h hVC⟩
      · exact hP2 G p P M H R Rbar K hd huniq hLa hF hVK hVC hZ

theorem d1CaseOneSmall_of (hβ : KFactBeta) (hα : KFactAlphaW) (h2 : D1CaseTwo)
    (h3 : D1CaseThree) (hAR : KFactSmallAutRank) (hSch : KFactCatalogSchreier)
    (hP1 : StmtSmallGuest) (hP2 : StmtSmallPosA) (hP3a : StmtSmallPoszSP)
    (hP3b : StmtSmallPoszOut) (hP4 : StmtSmallPosT) (hP5 : StmtSmallSPIn)
    (hP6 : StmtSmallSPOut) (hI1 : StmtSmallBOne) (hI2 : StmtSmallBZeroOdd)
    (hI3 : StmtSmallGEV) (hI4 : StmtSmallSPInThree) (hG1 : D1SmallIbEV) (hG2 : D1SmallSPL)
    (hG3 : D1SmallKC) (hG4 : D1SmallA6) (hG5 : D1SmallU33) (hG6 : D1SmallL34)
    (hG7 : D1SmallFi22) : D1CaseOneSmall :=
  d1CaseOneSmall_of_unique hβ hα h2 h3 hAR hSch
    (d1OneSmallUnique_of hP1 hP2 hP3a hP3b hP4 hP5 hP6 hI1 hI2 hI3 hI4 hG1 hG2 hG3 hG4 hG5
      hG6 hG7)

end CFSG.AGLEmbedding
