module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace MI

open CFSG.Assembly CFSG.StandardType

theorem chevParentID_rawInnField {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {K : Type} [Field K]
    (hK : Nat.card K = 2) (P H : Subgroup (LargeEvenChevGL A K)) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot H) (LargeEvenChevParentIDImage A K P H)
      (LargeEvenChevFieldImage A K H) :=
  ggRawInnField_of_forall_eq_one hp
    (Subgroup.closure (LargeEvenChevIDImage A K H ∪ LargeEvenParentConjImage P H)) rfl
    (fun x => Subgroup.subset_closure (Or.inl (conj_mem_chevIDImage H x)))
    (fun _ hf => chevFieldImage_eq_one_of_card_two hK H hf)


theorem canonRawInn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : CAll lab (GGRawInnField p) := by
  by_cases hd : DerivedLab lab
  · obtain ⟨t, l, n⟩ := lab
    rcases hd with hd | hd
    · dsimp only at hd
      subst hd
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      exact ⟨K, hF, hfin, hK, hQ, chevParentID_rawInnField _ hK _ _ hp.ne_one⟩
    · dsimp only at hd
      subst hd
      obtain ⟨-, -, hn1⟩ := hlab
      have hn1' : n = 1 := hn1
      subst hn1'
      intro Q h
      dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeTwF4Inherited] at h ⊢
      obtain ⟨K, hF, hfin, hK, hQ⟩ := h
      have hK2 : Nat.card K = 2 := by simpa using hK
      refine ⟨K, hF, hfin, hK, hQ, ?_⟩
      simp only [show (1 - 1) / 2 = 0 from rfl, if_true]
      exact chevParentID_rawInnField _ hK2 _ _ hp.ne_one
  · exact (canonAll_iff_legacyAll hlab hd _).2
      (ggRawInnFieldInput_holds p hp hp2 lab hlab)

end MI

end CFSG.LocalAnalysis.GLTheoremA
