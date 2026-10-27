module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09LabelDict
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S171

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA



theorem hod_tag_of_char_ne_two (tg : CFSG.Assembly.LargeEvenLieTag) (r nn : ℕ)
    (h : CFSG.StandardType.markChar ⟨tg, r, nn⟩ ≠ 2) :
    tg = .B2der ∨ tg = .G2der := by
  cases tg <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd rfl h

theorem hod_lab_triple_twA {lab : CFSG.Assembly.LargeEvenLabel}
    (h : CFSG.StandardType.markTag lab = StatedLieTag.PSU ∧ CFSG.StandardType.markRank lab = 5 ∧
      CFSG.StandardType.markDeg lab = 1) : lab = ⟨.twA, 4, 1⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨h1, h2, h3⟩ := h
  cases tg <;> simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
    CFSG.StandardType.markDeg] at h1 h2 h3 <;> (try split_ifs at h1 h2 h3) <;> simp_all <;> omega

theorem hod_lab_triple_D {lab : CFSG.Assembly.LargeEvenLabel}
    (h : CFSG.StandardType.markTag lab = StatedLieTag.POmegaPlus ∧
      CFSG.StandardType.markRank lab = 4 ∧ CFSG.StandardType.markDeg lab = 1) :
    lab = ⟨.D, 4, 1⟩ := by
  obtain ⟨tg, r, nn⟩ := lab
  obtain ⟨h1, h2, h3⟩ := h
  cases tg <;> simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
    CFSG.StandardType.markDeg] at h1 h2 h3 <;> (try split_ifs at h1 h2 h3) <;> simp_all <;> omega







section Cert


theorem hod_odd_false {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (hG : CFSG.Blueprint.LieModel X t n 2 f) (ht : t ≠ StatedLieTag.Tits)
    (hodd : CFSG.Blueprint.OddLieType X)
    (hT : ¬ ((t = StatedLieTag.PSL ∧ n = 2 ∧ f = 2) ∨ (t = StatedLieTag.PSL ∧ n = 3 ∧ f = 1) ∨
      (t = StatedLieTag.PSU ∧ n = 4 ∧ f = 1))) : False :=
  hT (CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType_of_ne_Tits hG ht hodd)

theorem hod_lab_u5 {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X StatedLieTag.PSU 5 2 1)
    {lab : CFSG.Assembly.LargeEvenLabel} (hM : CFSG.StandardType.MarkedModel lab X) :
    lab = ⟨.twA, 4, 1⟩ := by
  rcases lab with ⟨tg, r, nn⟩
  by_cases h2 : CFSG.StandardType.markChar ⟨tg, r, nn⟩ = 2
  · have hE : CFSG.Blueprint.LieModel X (CFSG.StandardType.markTag ⟨tg, r, nn⟩)
        (CFSG.StandardType.markRank ⟨tg, r, nn⟩) 2 (CFSG.StandardType.markDeg ⟨tg, r, nn⟩) := by
      unfold CFSG.StandardType.MarkedModel at hM
      rwa [h2] at hM
    exact hod_lab_triple_twA (ys09_typeDet (t := StatedLieTag.PSU) (n := 5) (f := 1)
      (Or.inl ⟨rfl, rfl, rfl⟩) hX hE)
  · exfalso
    rcases hod_tag_of_char_ne_two tg r nn h2 with ht | ht
    · subst ht
      have hM' : CFSG.Blueprint.LieModel X StatedLieTag.PSL 2 3 2 := hM
      exact hod_odd_false hX (by decide)
        ⟨StatedLieTag.PSL, 2, 3, 2, Nat.prime_three, by decide, hM'.admissible, hM'⟩ (by decide)
    · subst ht
      have hM' : CFSG.Blueprint.LieModel X StatedLieTag.PSU 3 3 1 := hM
      exact hod_odd_false hX (by decide)
        ⟨StatedLieTag.PSU, 3, 3, 1, Nat.prime_three, by decide, hM'.admissible, hM'⟩ (by decide)

theorem hod_lab_d4 {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X StatedLieTag.POmegaPlus 4 2 1)
    {lab : CFSG.Assembly.LargeEvenLabel} (hM : CFSG.StandardType.MarkedModel lab X) :
    lab = ⟨.D, 4, 1⟩ := by
  rcases lab with ⟨tg, r, nn⟩
  by_cases h2 : CFSG.StandardType.markChar ⟨tg, r, nn⟩ = 2
  · have hE : CFSG.Blueprint.LieModel X (CFSG.StandardType.markTag ⟨tg, r, nn⟩)
        (CFSG.StandardType.markRank ⟨tg, r, nn⟩) 2 (CFSG.StandardType.markDeg ⟨tg, r, nn⟩) := by
      unfold CFSG.StandardType.MarkedModel at hM
      rwa [h2] at hM
    exact hod_lab_triple_D (ys09_typeDet (t := StatedLieTag.POmegaPlus) (n := 4) (f := 1)
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) hX hE)
  · exfalso
    rcases hod_tag_of_char_ne_two tg r nn h2 with ht | ht
    · subst ht
      have hM' : CFSG.Blueprint.LieModel X StatedLieTag.PSL 2 3 2 := hM
      exact hod_odd_false hX (by decide)
        ⟨StatedLieTag.PSL, 2, 3, 2, Nat.prime_three, by decide, hM'.admissible, hM'⟩ (by decide)
    · subst ht
      have hM' : CFSG.Blueprint.LieModel X StatedLieTag.PSU 3 3 1 := hM
      exact hod_odd_false hX (by decide)
        ⟨StatedLieTag.PSU, 3, 3, 1, Nat.prime_three, by decide, hM'.admissible, hM'⟩ (by decide)

end Cert

theorem hod_rk2_twA41 : Rk2LabelAll ⟨.twA, 4, 1⟩
    (fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R)) := by
  intro Q hQ
  dsimp only [GLARawDatum, CFSG.Assembly.LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQK,
    CFSG.StandardType.TableB.matConjImage_gu_subset_inn (n := 1) (d := 4 + 1) hK (by norm_num)⟩

end CFSG.LocalAnalysis.GLTheoremA.S171

end
