module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsGamma
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharCert
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB

private theorem lieIndex_u6two {S : Type} [Group S] (h : catalogIs S S9.isU6two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.twistedA 5 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | twistedA r q =>
    rcases r with _ | _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

private theorem lieIndex_sp8two {S : Type} [Group S] (h : catalogIs S S9.isSp8two) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 4 q).Valid), q.card = 2 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 4 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

theorem ys09_lieModel {S : Type} [Group S] (h : catalogIs S S10.isYs09Type) :
    ∃ (t : StatedLieTag) (n f : ℕ),
      ((t = .PSU ∧ n = 5 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
        (t = .PSp ∧ n = 4 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1)) ∧
      CFSG.Blueprint.LieModel S t n 2 f := by
  obtain ⟨i, hi, e⟩ := h
  rcases hi with h5 | h6 | h8 | h4
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := lieIndex_isU5two ⟨i, h5, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := lieModel_twistedA' 4 q hv e'
    rw [h1, h2] at hm
    exact ⟨.PSU, 5, 1, Or.inl ⟨rfl, rfl, rfl⟩, hm.toBlueprint (by decide)⟩
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := lieIndex_u6two ⟨i, h6, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := lieModel_twistedA' 5 q hv e'
    rw [h1, h2] at hm
    exact ⟨.PSU, 6, 1, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), hm.toBlueprint (by decide)⟩
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := lieIndex_sp8two ⟨i, h8, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    rcases CFSG.Models.lieModel_B 4 q hv e' with hm | hm
    · rw [h1, h2] at hm
      exact ⟨.PSp, 4, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)), hm.toBlueprint (by decide)⟩
    · rw [h1, h2] at hm
      exact absurd hm.admissible.2.2.2 (by norm_num)
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := lieIndex_isD4two ⟨i, h4, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := CFSG.Models.lieModel_D 4 q hv e'
    rw [h1, h2] at hm
    exact ⟨.POmegaPlus, 4, 1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)), hm.toBlueprint (by decide)⟩

theorem ys09Label_of_triple {lab : LargeEvenLabel}
    (hT : (CFSG.StandardType.markTag lab = .PSU ∧ CFSG.StandardType.markRank lab = 5 ∧
        CFSG.StandardType.markDeg lab = 1) ∨
      (CFSG.StandardType.markTag lab = .PSU ∧ CFSG.StandardType.markRank lab = 6 ∧
        CFSG.StandardType.markDeg lab = 1) ∨
      (CFSG.StandardType.markTag lab = .PSp ∧ CFSG.StandardType.markRank lab = 4 ∧
        CFSG.StandardType.markDeg lab = 1) ∨
      (CFSG.StandardType.markTag lab = .POmegaPlus ∧ CFSG.StandardType.markRank lab = 4 ∧
        CFSG.StandardType.markDeg lab = 1)) :
    Ys09Label lab := by
  obtain ⟨tg, r, nn⟩ := lab
  cases tg <;>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank, CFSG.StandardType.markDeg,
      Ys09Label] at hT ⊢ <;>
    (try split_ifs at hT ⊢) <;> simp_all <;> omega

section Cert


theorem ys09_typeDet {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hT : (t = .PSU ∧ n = 5 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .PSp ∧ n = 4 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1))
    (hG : CFSG.Blueprint.LieModel X t n 2 f) {t' : StatedLieTag} {n' f' : ℕ}
    (hE : CFSG.Blueprint.LieModel X t' n' 2 f') : t' = t ∧ n' = n ∧ f' = f := by
  rcases hT with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 5) (by norm_num) X 1 t' n' f'
      hG hE.admissible hE
  · exact CFSG.SeitzReduction.UnitaryPilot.sumEvenTypeDetAt (m := 6) (by norm_num) X 1 t' n' f'
      hG hE.admissible hE
  · exact CFSG.SeitzReduction.SymplecticPilot.sp2mEvenTypeDet 4 X 1 t' n' f' hG hE.admissible hE
  · exact CFSG.SeitzReduction.OmegaPilot.omegaEvenTypeDetAt 4 X .POmegaPlus 1 t' n' f' (Or.inl rfl)
      hG hE.admissible hE

private theorem not_odd_of_ys09 {Y : Type} [Group Y] {t : StatedLieTag} {n f : ℕ}
    (hT : (t = .PSU ∧ n = 5 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .PSp ∧ n = 4 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1))
    (hG : CFSG.Blueprint.LieModel Y t n 2 f) (hodd : CFSG.Blueprint.OddLieType Y) : False := by
  have hT' : t ≠ .Tits := by
    rcases hT with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> decide
  have key := CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hG hT' hodd
  rcases hT with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp at key

private theorem char3_B2der_contra {Q : Type} [Group Q] {t : StatedLieTag} {n f : ℕ}
    (hT : (t = .PSU ∧ n = 5 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .PSp ∧ n = 4 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1))
    (hG : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) t n 2 f) {r nn : ℕ}
    (hM : CFSG.StandardType.MarkedModel ⟨.B2der, r, nn⟩ (Q ⧸ Subgroup.center Q)) : False := by
  have hM' : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSL 2 3 2 := hM
  exact not_odd_of_ys09 hT hG ⟨.PSL, 2, 3, 2, Nat.prime_three, by decide, hM'.admissible, hM'⟩

private theorem char3_G2der_contra {Q : Type} [Group Q] {t : StatedLieTag} {n f : ℕ}
    (hT : (t = .PSU ∧ n = 5 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .PSp ∧ n = 4 ∧ f = 1) ∨ (t = .POmegaPlus ∧ n = 4 ∧ f = 1))
    (hG : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) t n 2 f) {r nn : ℕ}
    (hM : CFSG.StandardType.MarkedModel ⟨.G2der, r, nn⟩ (Q ⧸ Subgroup.center Q)) : False := by
  have hM' : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q) .PSU 3 3 1 := hM
  exact not_odd_of_ys09 hT hG ⟨.PSU, 3, 3, 1, Nat.prime_three, by decide, hM'.admissible, hM'⟩

theorem ys09Label_of_marked {Q : Type} [Group Q] [Finite Q] {lab : LargeEvenLabel}
    (hcat : catalogIs (Q ⧸ Subgroup.center Q) S10.isYs09Type)
    (hM : CFSG.StandardType.MarkedModel lab (Q ⧸ Subgroup.center Q)) : Ys09Label lab := by
  obtain ⟨t, n, f, hT, hG⟩ := ys09_lieModel hcat
  obtain ⟨tg, r, nn⟩ := lab
  by_cases h2 : CFSG.StandardType.markChar ⟨tg, r, nn⟩ = 2
  · have hE : CFSG.Blueprint.LieModel (Q ⧸ Subgroup.center Q)
        (CFSG.StandardType.markTag ⟨tg, r, nn⟩) (CFSG.StandardType.markRank ⟨tg, r, nn⟩) 2
        (CFSG.StandardType.markDeg ⟨tg, r, nn⟩) := by
      unfold CFSG.StandardType.MarkedModel at hM
      rwa [h2] at hM
    obtain ⟨e1, e2, e3⟩ := ys09_typeDet hT hG hE
    apply ys09Label_of_triple (lab := ⟨tg, r, nn⟩)
    rw [e1, e2, e3]
    exact hT
  · cases tg <;> simp [CFSG.StandardType.markChar] at h2
    · exact (char3_B2der_contra hT hG hM).elim
    · exact (char3_G2der_contra hT hG hM).elim

theorem labelDictAt_holds : LabelDictAt := by
  intro X _ _ _ hcat P hP
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hP
  refine ⟨hcomm, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_imp hlab ?_ ?_ hraw
  · intro R _ I F hq
    exact hq.2.1
  · rintro R _ I F ⟨hs, hna, θ, hθ⟩ hm
    exact ⟨hs, hna, θ,
      ys09Label_of_marked hcat (CFSG.StandardType.MarkedModel.of_mulEquiv θ.symm hm), hθ⟩

end Cert

end CFSG.LocalAnalysis.GLTheoremA
