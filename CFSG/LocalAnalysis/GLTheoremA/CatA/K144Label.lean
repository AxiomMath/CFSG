module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.CGT.PushingUpLit.Transport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)

private theorem lieModel_of_catalog_aux {S : Type} [Group S] (h : catalogIs S I144Cat) :
    ∃ (t : StatedLieTag) (n : ℕ),
      ((t = .PSU ∧ n = 4) ∨ (t = .PSU ∧ n = 5) ∨ (t = .PSp ∧ n = 3)) ∧
        CFSG.Blueprint.LieModel S t n 2 1 := by
  obtain ⟨i, hi, e⟩ := h
  rcases hi with h4 | h5 | h6
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU4two ⟨i, h4, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := lieModel_twistedA' 3 q hv e'
    rw [h1, h2] at hm
    exact ⟨.PSU, 4, Or.inl ⟨rfl, rfl⟩, hm.toBlueprint (by decide)⟩
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isU5two ⟨i, h5, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    have hm := lieModel_twistedA' 4 q hv e'
    rw [h1, h2] at hm
    exact ⟨.PSU, 5, Or.inr (Or.inl ⟨rfl, rfl⟩), hm.toBlueprint (by decide)⟩
  · obtain ⟨q, hv, hq, ⟨e'⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isSp6two ⟨i, h6, e⟩
    obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
      (hq.trans (by norm_num))
    rcases CFSG.Models.lieModel_B 3 q hv e' with hm | hm
    · rw [h1, h2] at hm
      exact ⟨.PSp, 3, Or.inr (Or.inr ⟨rfl, rfl⟩), hm.toBlueprint (by decide)⟩
    · rw [h1, h2] at hm
      exact absurd hm.admissible.2.2.2 (by norm_num)

private theorem canonLabel_of_catalog_params {lab : GLALabel} {t : StatedLieTag} {n : ℕ}
    (hT : (t = .PSU ∧ n = 4) ∨ (t = .PSU ∧ n = 5) ∨ (t = .PSp ∧ n = 3))
    (hP : CFSG.StandardType.markTag lab = t ∧ CFSG.StandardType.markRank lab = n ∧
      CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :
    (canonLabel lab).n = 1 ∧
      ((canonLabel lab).tag = .twA ∨ (canonLabel lab).tag = .B) := by
  rcases hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (obtain ⟨tg, r, nn⟩ := lab
     cases tg <;>
       simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
         CFSG.StandardType.markChar, CFSG.StandardType.markDeg, canonLabel] at hP ⊢ <;>
       (try split_ifs at hP ⊢) <;> simp_all <;> omega)

private theorem exists_label_of_marking_aux {X : Type} [Group X] {P : GLALabel → Prop}
    (h : HasLabel X P) : ∃ lab : GLALabel, P lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

section Label


theorem exists_label_of_catalog {X : Type} [Group X] (hq : CFSG.Open.IsQuasisimple X)
    (h : catalogIs (X ⧸ Subgroup.center X) I144Cat) :
    ∃ lab : GLALabel, HasLabel X (fun l : GLALabel => l = lab) ∧ (canonLabel lab).n = 1 ∧
      ((canonLabel lab).tag = .twA ∨ (canonLabel lab).tag = .B) := by
  obtain ⟨t, n, hT, hm⟩ := lieModel_of_catalog_aux h
  have hmark : HasLabel X (fun lab : GLALabel =>
      CFSG.StandardType.markTag lab = t ∧ CFSG.StandardType.markRank lab = n ∧
        CFSG.StandardType.markChar lab = 2 ∧ CFSG.StandardType.markDeg lab = 1) :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hm
  obtain ⟨lab, hP, hLab⟩ := exists_label_of_marking_aux hmark
  exact ⟨lab, hLab, canonLabel_of_catalog_params hT hP⟩

end Label

end CFSG.LocalAnalysis.GLTheoremA.K144
