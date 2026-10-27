module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut3
public import CFSG.LocalAnalysis.StandardType.GGRawAutRest
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityHolds
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega
public import CFSG.LocalAnalysis.StandardType.GGRecipeField

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI


theorem canonAll_derived {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : DerivedLab lab) {P : LargeEvenRawCont}
    (hG : lab.tag = .G2der → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      P (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevParentIDImage LargeEvenCartanG2 K (LargeEvenChevGroup LargeEvenCartanG2 K)
          (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)))
    (hT : lab.tag = .twF4der → ∀ (a : ℕ), a = 0 → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = 2 ^ (2 * a + 1) →
      P (LargeEvenCenterQuot (LargeEvenTwF4H a K))
        (if a = 0 then LargeEvenChevParentIDImage LargeEvenCartanF4 K (LargeEvenTwF4Parent a K)
          (LargeEvenTwF4H a K)
         else LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))) :
    CAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  rcases hd with hd | hd
  · dsimp only at hd
    subst hd
    intro Q h
    dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := h
    exact ⟨K, hF, hfin, hK, hQ, hG rfl K hK⟩
  · dsimp only at hd
    subst hd
    obtain ⟨-, -, hn1⟩ := hlab
    have hn1' : n = 1 := hn1
    have ha : (n - 1) / 2 = 0 := by omega
    intro Q h
    dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h ⊢
    obtain ⟨K, hF, hfin, hK, hQ⟩ := h
    exact ⟨K, hF, hfin, hK, hQ, hT rfl _ ha K hK⟩

theorem canonOddAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hD : ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)) :
    CAll lab (LargeEvenSimpleGuard fun R _ I F => GGOddAutInnField p I F) := by
  by_cases hd : DerivedLab lab
  · refine canonAll_derived hlab hd ?_ ?_
    · intro _ K _ _ hK hs hna
      exact (RawAutSmall.ggOddAutInnField_g2der hK (hp.odd_of_ne_two hp2) hna).mono
        (fun φ hφ => Subgroup.subset_closure (Or.inl hφ)) le_rfl
    · intro _ a ha K _ _ hK hs hna
      subst ha
      simp only [if_true]
      exact (RawAutSmall.ggOddAutInnField_twF4der rfl hK (hp.odd_of_ne_two hp2)).mono
        (fun φ hφ => Subgroup.subset_closure (Or.inl hφ)) le_rfl
  · exact (canonAll_iff_legacyAll hlab hd _).2 (ggOddAutOn_all p lab hp hp2 hlab trivial hD)

theorem canonRawFieldConj {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h3 : ¬ (lab.tag = .triD4 ∧ p = 3)) :
    CAll lab (GGRawFieldConj p) := by
  by_cases hd : DerivedLab lab
  · refine canonAll_derived hlab hd ?_ ?_
    · intro _ K _ _ hK
      exact ggRawFieldConj_of_forall_eq_one fun f hf => chevFieldImage_eq_one_of_card_two hK _ hf
    · intro _ a ha K _ _ hK
      subst ha
      exact ggRawFieldConj_of_forall_eq_one fun f hf =>
        chevFieldImage_eq_one_of_card_two (by simpa using hK) _ hf
  · exact (canonAll_iff_legacyAll hlab hd _).2 (ggRawFieldConjInputExc_holds p hp hp2 lab hlab h3)

theorem canonRawFieldCentral {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    CAll lab GGRawFieldCentral := by
  by_cases hd : DerivedLab lab
  · refine canonAll_derived hlab hd ?_ ?_
    · intro _ K _ _ hK hs hna α u hu f hf
      have hO := InndiagCommRest.ggOutComm_g2der hK hna
      have hf1 : f = 1 := eq_one_of_mem_closure_of_forall
        (fun g hg => chevFieldImage_eq_one_of_card_two hK _ hg) hf
      subst hf1
      rw [mul_one]
      set J : Subgroup (MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))) :=
        Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanG2 K
          (LargeEvenChevH LargeEvenCartanG2 K true) ∪ LargeEvenParentConjImage
          (LargeEvenChevGroup LargeEvenCartanG2 K) (LargeEvenChevH LargeEvenCartanG2 K true)) with hJdef
      have hJ : ∀ r, MulAut.conj r ∈ J := fun r =>
        Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))
      have hu' : u ∈ J := hu
      exact J.mul_mem (normal_of_outComm hO hJ α hu') (J.inv_mem hu')
    · intro _ a ha K _ _ hK hs hna α u hu f hf
      subst ha
      have hK2 : Nat.card K = 2 ^ (2 * 0 + 1) := hK
      have hO := InndiagCommRest.ggOutComm_twF4der rfl hK2
      have hf1 : f = 1 := eq_one_of_mem_closure_of_forall
        (fun g hg => chevFieldImage_eq_one_of_card_two (by simpa using hK2) _ hg) hf
      subst hf1
      rw [mul_one]
      simp only [if_true] at hu ⊢
      set J : Subgroup (MulAut (LargeEvenCenterQuot (LargeEvenTwF4H 0 K))) :=
        Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H 0 K) ∪
          LargeEvenParentConjImage (LargeEvenTwF4Parent 0 K) (LargeEvenTwF4H 0 K)) with hJdef
      have hJ : ∀ r, MulAut.conj r ∈ J := fun r =>
        Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))
      have hu' : u ∈ J := hu
      exact J.mul_mem (normal_of_outComm hO hJ α hu') (J.inv_mem hu')
  · exact (canonAll_iff_legacyAll hlab hd _).2
      (ggRawFieldCentralInput_of_triality plusFourTrialityInput_holds lab hlab)

theorem legacyPCyclicNotD4 : GGRawPCyclicOn fun p lab => GGNotD4Three p lab := by
  intro p hp hp2 lab hlab hne
  by_cases hdone : GGRawPCyclicDoneLabel lab
  · exact ggRawPCyclicOn_done p hp hp2 lab hlab hdone
  by_cases ho : GGOmegaLabel lab
  · exact ggRawPCyclicOn_omega plusFourTrialityInput_holds p hp hp2 lab hlab ⟨ho, hne⟩
  · exact ggRawPCyclicOn_rest5 p hp hp2 lab hlab ⟨hne, hdone, ho⟩

theorem canonRawPCyclic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hD : ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)) :
    CAll lab (GGRawPCyclic p) := by
  by_cases hd : DerivedLab lab
  · have hodd : Odd p := hp.odd_of_ne_two hp2
    refine canonAll_derived hlab hd ?_ ?_
    · intro _ K _ _ hK hs hna
      exact ggRawPCyclic_of_mem (F := ∅)
        (Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanG2 K
          (LargeEvenChevH LargeEvenCartanG2 K true) ∪ LargeEvenParentConjImage
          (LargeEvenChevGroup LargeEvenCartanG2 K) (LargeEvenChevH LargeEvenCartanG2 K true))) rfl
        (fun α ⟨k, hk⟩ => by
          obtain ⟨r, rfl⟩ := RawAutSmall.mem_inner_g2der hK hna hodd.pow hk
          exact Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))) hs hna
    · intro _ a ha K _ _ hK hs hna
      subst ha
      simp only [if_true]
      exact ggRawPCyclic_of_mem (F := ∅)
        (Subgroup.closure (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H 0 K) ∪
          LargeEvenParentConjImage (LargeEvenTwF4Parent 0 K) (LargeEvenTwF4H 0 K))) rfl
        (fun α ⟨k, hk⟩ => by
          obtain ⟨r, rfl⟩ := RawAut.mem_inner_of_isPGroup_outer
            (RawAutSmall.isPGroup_outer_twF4der rfl hK) hodd.pow hk
          exact Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage _ r))) hs hna
  · exact (canonAll_iff_legacyAll hlab hd _).2 (legacyPCyclicNotD4 p hp hp2 lab hlab hD)

end FP

end CFSG.LocalAnalysis.GLTheoremA
