module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCD
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110d

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.I171

theorem openQuasisimple_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ} {L J E : Subgroup G}
    {d : G} (h : Shape15Cfg p L J E d) : CFSG.Open.IsQuasisimple ↥L :=
  ⟨h.qs.1.commutator_eq_top, h.qs.2.1⟩

theorem wsetup_of_cfg {G : Type} [Group G] [Finite G] {p : ℕ} {L J E : Subgroup G} {d b : G}
    (h : Shape15Cfg p L J E d) (hb : b ∈ E) (hbN : b ∈ Subgroup.normalizer (J : Set G)) :
    T171Sh.WSetup p L J E d b := by
  have hq : CFSG.Open.IsQuasisimple ↥L := openQuasisimple_of_cfg h
  have hpJ : p ∣ Nat.card ↥J :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110d.prime_dvd_card_of_glaPComponent
      h.prime h.pcomp
  have hJleL : J ≤ L := h.pcomp.1.trans inf_le_left
  have hpL : p ∣ Nat.card ↥L := hpJ.trans (Subgroup.card_dvd_of_le hJleL)
  have hLL : GLAPComponent p L L := T171Sh.glaPComponent_self_of_dvd_card h.prime hq hpL
  exact ⟨h.prime, h.odd, hq, h.chev2, h.elem, (innDiagOn_iff hLL hq).2 h.idiag, h.faithful,
    h.d_mem, h.d_ne, hb, h.pcomp, hbN⟩

theorem compHalf_of_norm_diag {F : TauCeti.LieTypeIndex → Prop} (hN : NormHalf F)
    (hD : DiagHalf F) : CompHalf F := by
  intro G _ _ p L J E d b cfg hb hcat hshape hin
  have hbN := hN G p L J E d b cfg hb hcat hshape hin
  exact ⟨hbN, hD G p L J E d b (wsetup_of_cfg cfg hb hbN) hcat hshape hin⟩

theorem lieIdx_cases (i : TauCeti.LieTypeIndex) :
    KD264Lie.isLinearIdx i ∨ KD264Lie.isUnitaryIdx i ∨ isSympIdx i ∨ isOrthIdx i ∨
      KD264Lie.isTrialityIdx i ∨ KD264Lie.isExcUntwistedIdx i ∨ KD264Lie.isExcTwistedIdx i := by
  cases i <;> simp [KD264Lie.isLinearIdx, KD264Lie.isUnitaryIdx, isSympIdx, isOrthIdx,
    KD264Lie.isTrialityIdx, KD264Lie.isExcUntwistedIdx, KD264Lie.isExcTwistedIdx]

theorem family_cases {S : Type} [Group S]
    (h : catalogIs S (onLie fun d => d.characteristic = 2)) :
    catalogIs S (onLie (CharTwoOf KD264Lie.isLinearIdx)) ∨
      catalogIs S (onLie (CharTwoOf KD264Lie.isUnitaryIdx)) ∨
      catalogIs S (onLie (CharTwoOf isSympIdx)) ∨
      catalogIs S (onLie (CharTwoOf isOrthIdx)) ∨
      catalogIs S (onLie (CharTwoOf KD264Lie.isTrialityIdx)) ∨
      catalogIs S (onLie (CharTwoOf KD264Lie.isExcUntwistedIdx)) ∨
      catalogIs S (onLie (CharTwoOf KD264Lie.isExcTwistedIdx)) := by
  obtain ⟨i, hi, e⟩ := h
  cases i with
  | lie dd =>
    have hc : dd.1.characteristic = 2 := hi
    rcases lieIdx_cases dd.1 with h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩
    · exact Or.inr (Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨.lie dd, ⟨h1, hc⟩, e⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.lie dd, ⟨h1, hc⟩, e⟩)))))
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

theorem i171ShapeFact15_of_pieces (h : ShapePieces) : I171ShapeFact15 := by
  intro G _ _ p L J E d hp hp2 hqs hchev helem hcard hnorm hidiag hfaith hd hd1 hJ b hb
  have cfg : Shape15Cfg p L J E d :=
    ⟨hp, hp2, hqs, hchev, helem, hcard, hnorm, hidiag, hfaith, hd, hd1, hJ⟩
  by_cases hshape : I171LieShapeAt p L
  · exact Or.inr hshape
  · refine Or.inl ?_
    have hin : InducesInnerMod p L b := (h.out G p L J E d b cfg hb).resolve_right hshape
    rcases hchev with hlie | hamb
    · rcases family_cases hlie with hc | hc | hc | hc | hc | hc | hc
      · exact h.lin G p L J E d b cfg hb hc hshape hin
      · exact h.uni G p L J E d b cfg hb hc hshape hin
      · exact h.symp G p L J E d b cfg hb hc hshape hin
      · exact h.orth G p L J E d b cfg hb hc hshape hin
      · exact h.tri G p L J E d b cfg hb hc hshape hin
      · exact h.excU G p L J E d b cfg hb hc hshape hin
      · exact h.excT G p L J E d b cfg hb hc hshape hin
    · exact h.amb G p L J E d b cfg hb hamb hshape hin

theorem i171ShapeFact15_of_halves (hOut : OutHalf) (hAmb : AmbigHalf)
    (hLinN : NormHalf (CharTwoOf KD264Lie.isLinearIdx))
    (hLinD : DiagHalf (CharTwoOf KD264Lie.isLinearIdx))
    (hUniN : NormHalf (CharTwoOf KD264Lie.isUnitaryIdx))
    (hUniD : DiagHalf (CharTwoOf KD264Lie.isUnitaryIdx))
    (hSymp : CompHalf (CharTwoOf isSympIdx)) (hOrth : CompHalf (CharTwoOf isOrthIdx))
    (hTri : CompHalf (CharTwoOf KD264Lie.isTrialityIdx))
    (hExcU : CompHalf (CharTwoOf KD264Lie.isExcUntwistedIdx))
    (hExcT : CompHalf (CharTwoOf KD264Lie.isExcTwistedIdx)) : I171ShapeFact15 :=
  i171ShapeFact15_of_pieces
    ⟨hOut, hAmb, compHalf_of_norm_diag hLinN hLinD, compHalf_of_norm_diag hUniN hUniD, hSymp,
      hOrth, hTri, hExcU, hExcT⟩

theorem simpleModel_mono {F F' : TauCeti.LieTypeIndex → Prop} (h : SimpleModel F)
    (hle : ∀ i, F' i → F i) : SimpleModel F' := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, e⟩ := hcat
  cases i with
  | lie dd => exact h S p hp hp2 ⟨.lie dd, hle _ hi, e⟩ hshape
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

theorem simpleModel_union {F F' : TauCeti.LieTypeIndex → Prop} (h : SimpleModel F)
    (h' : SimpleModel F') : SimpleModel fun i => F i ∨ F' i := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨i, hi, e⟩ := hcat
  cases i with
  | lie dd =>
    rcases (hi : F dd.1 ∨ F' dd.1) with h1 | h1
    · exact h S p hp hp2 ⟨.lie dd, h1, e⟩ hshape
    · exact h' S p hp hp2 ⟨.lie dd, h1, e⟩ hshape
  | cyclic _ _ => simp [onLie] at hi
  | alternating _ _ => simp [onLie] at hi
  | sporadic _ => simp [onLie] at hi

theorem simpleModel_excT (hT : SimpleModel (CharTwoOf isTwE6Idx))
    (hR : SimpleModel (CharTwoOf isReeF4Idx)) (hS : SimpleModel (CharTwoOf isSuzTitsIdx)) :
    SimpleModel (CharTwoOf KD264Lie.isExcTwistedIdx) := by
  refine simpleModel_mono (simpleModel_union (simpleModel_union hT hR) hS) ?_
  intro i hi
  obtain ⟨hi, hc⟩ := hi
  cases i <;> simp_all [KD264Lie.isExcTwistedIdx, CharTwoOf, isTwE6Idx, isReeF4Idx, isSuzTitsIdx]

theorem shapeModelAt_of_halves {R : Type} [Group R] [Finite R] {p : ℕ}
    (hN : ShapeModelNormAt R p) (hD : ShapeModelDiagAt R p) : ShapeModelAt R p :=
  fun x y hx1 hxp hyp hc J hJ =>
    ⟨hN x y hx1 hxp hyp hc J hJ, hD x y hx1 hxp hyp hc J hJ (hN x y hx1 hxp hyp hc J hJ)⟩

theorem sympModel_of_halves (hN : SympNorm) (hD : SympDiag) : SympModel :=
  fun n m K _ _ hn hn22 hK p hp hp2 =>
    shapeModelAt_of_halves (hN n m K hn hn22 hK p hp hp2) (hD n m K hn hn22 hK p hp hp2)

theorem orthPlusModel_of_halves (hN : OrthPlusNorm) (hD : OrthPlusDiag) : OrthPlusModel :=
  fun n m K _ _ hn hK p hp hp2 =>
    shapeModelAt_of_halves (hN n m K hn hK p hp hp2) (hD n m K hn hK p hp hp2)

theorem orthMinusModel_of_halves (hN : OrthMinusNorm) (hD : OrthMinusDiag) : OrthMinusModel :=
  fun n m K _ _ hn hK b c hbc p hp hp2 =>
    shapeModelAt_of_halves (hN n m K hn hK b c hbc p hp hp2) (hD n m K hn hK b c hbc p hp hp2)

theorem simpleModel_of_halves {F : TauCeti.LieTypeIndex → Prop} (hN : SimpleNormModel F)
    (hD : SimpleDiagModel F) : SimpleModel F :=
  fun S _ _ p hp hp2 hcat hshape =>
    shapeModelAt_of_halves (hN S p hp hp2 hcat hshape) (hD S p hp hp2 hcat hshape)

end CFSG.LocalAnalysis.GLTheoremA.F151

end
