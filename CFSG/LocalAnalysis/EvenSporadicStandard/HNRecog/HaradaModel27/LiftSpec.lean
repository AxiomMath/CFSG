module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel27.LiftCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.S25.NoLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.BlockSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel CFSG.EvenSporadicStandard.HNRecog.Harada.S25

theorem rep_labU : Rep 5 labU a1 := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem rep_labV : Rep 5 labV a2 := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem lift_words (hg : gensOK = true) (hlift : liftOK = true) :
    wordOK uWord = true ∧ wordOK vWord = true ∧ elemW uWord * elemZ = elemZ * elemW uWord ∧
      elemW vWord * elemZ = elemZ * elemW vWord ∧
      (∀ p : Fin 1408, blkF 5 blkData1.blk (elemW uWord p) = (blkF 5 blkData1.blk p).map a1) ∧
      (∀ p : Fin 1408, blkF 5 blkData1.blk (elemW vWord p) = (blkF 5 blkData1.blk p).map a2) := by
  simp only [liftOK, Bool.and_eq_true] at hlift
  obtain ⟨⟨⟨⟨⟨⟨hwu, hwv⟩, hcu⟩, hcv⟩, hbu⟩, hbv⟩, -⟩ := hlift
  have hRu := rep_elemW_of_gensOK hg hwu
  have hRv := rep_elemW_of_gensOK hg hwv
  have hRz : Rep 1408 (tabW wordZ) elemZ := rep_elemW_of_gensOK hg (by decide)
  exact ⟨hwu, hwv, (commTT_iff hRu hRz).1 hcu, (commTT_iff hRv hRz).1 hcv,
    blkMapOK_spec hRu rep_labU hbu, blkMapOK_spec hRv rep_labV hbv⟩

private theorem sqZ_iff {x tz : Table} {a : Equiv.Perm (Fin 1408)}
    (hx : Rep 1408 x a) (hz : Rep 1408 tz elemZ) :
    sqZ x tz = true ↔ a * a = 1 ∨ a * a = elemZ := by
  have h1 : tblEq 1408 (compT 1408 x x) (idT 1408) = true ↔ a * a = 1 :=
    tblEq_iff_eq (Rep.compT hx hx) (Rep.idT (by norm_num : 1408 < 2 ^ 32))
  have h2 : tblEq 1408 (compT 1408 x x) tz = true ↔ a * a = elemZ :=
    tblEq_iff_eq (Rep.compT hx hx) hz
  rw [sqZ, Bool.or_eq_true, h1, h2]

private theorem commZ_iff {x y tz : Table} {a b : Equiv.Perm (Fin 1408)}
    (hx : Rep 1408 x a) (hy : Rep 1408 y b) (hz : Rep 1408 tz elemZ) :
    commZ x y tz = true ↔ a * b = b * a ∨ a * b = elemZ * (b * a) := by
  have h1 : tblEq 1408 (compT 1408 x y) (compT 1408 y x) = true ↔ a * b = b * a :=
    tblEq_iff_eq (Rep.compT hx hy) (Rep.compT hy hx)
  have h2 : tblEq 1408 (compT 1408 x y) (compT 1408 tz (compT 1408 y x)) = true ↔
      a * b = elemZ * (b * a) :=
    tblEq_iff_eq (Rep.compT hx hy) (Rep.compT hz (Rep.compT hy hx))
  rw [commZ, Bool.or_eq_true, h1, h2]

private theorem not_sqZ_iff {x tz : Table} {a : Equiv.Perm (Fin 1408)}
    (hx : Rep 1408 x a) (hz : Rep 1408 tz elemZ) :
    ((!sqZ x tz) = true) ↔ ¬ (a * a = 1 ∨ a * a = elemZ) := by
  rw [Bool.not_eq_true']
  exact Bool.eq_false_iff.trans (not_congr (sqZ_iff hx hz))

private theorem not_commZ_iff {x y tz : Table} {a b : Equiv.Perm (Fin 1408)}
    (hx : Rep 1408 x a) (hy : Rep 1408 y b) (hz : Rep 1408 tz elemZ) :
    ((!commZ x y tz) = true) ↔ ¬ (a * b = b * a ∨ a * b = elemZ * (b * a)) := by
  rw [Bool.not_eq_true']
  exact Bool.eq_false_iff.trans (not_congr (commZ_iff hx hy hz))

private theorem inner_iff {x : Table} {a : Equiv.Perm (Fin 1408)}
    (hN : enumW capI 256 nWords1 = true) (hV : Rep 1408 (tabW vWord) (elemW vWord))
    (hZ : Rep 1408 (tabW wordZ) elemZ) (hx : Rep 1408 x a) :
    ((subgroupList capI nWords1).all fun m =>
        !sqZ (compT 1408 (tabW vWord) m) (tabW wordZ) ||
          !commZ x (compT 1408 (tabW vWord) m) (tabW wordZ)) = true ↔
      ∀ h ∈ wordSubgroup nWords1,
        (elemW vWord * h) * (elemW vWord * h) = 1 ∨
          (elemW vWord * h) * (elemW vWord * h) = elemZ →
        ¬ (a * (elemW vWord * h) = (elemW vWord * h) * a ∨
          a * (elemW vWord * h) = elemZ * ((elemW vWord * h) * a)) := by
  have hE : IsEnumSet 1408 (subgroupList capI nWords1)
      (wordSubgroup nWords1 : Set (Equiv.Perm (Fin 1408))) := (enumW_spec hN).2
  refine hE.forall_iff _ _ ?_
  intro m h hm
  have hm' : Rep 1408 (compT 1408 (tabW vWord) m) (elemW vWord * h) := Rep.compT hV hm
  rw [Bool.or_eq_true]
  rw [not_sqZ_iff hm' hZ, not_commZ_iff hx hm' hZ]
  exact imp_iff_not_or.symm

theorem lift_noComm (hg : gensOK = true) (hN : enumW capI 256 nWords1 = true)
    (hlift : liftOK = true) :
    ∀ g ∈ wordSubgroup nWords1, ∀ h ∈ wordSubgroup nWords1,
      (elemW uWord * g * (elemW uWord * g) = 1 ∨
        elemW uWord * g * (elemW uWord * g) = elemZ) →
      (elemW vWord * h * (elemW vWord * h) = 1 ∨
        elemW vWord * h * (elemW vWord * h) = elemZ) →
      (elemW uWord * g * (elemW vWord * h) = elemW vWord * h * (elemW uWord * g) ∨
        elemW uWord * g * (elemW vWord * h) =
          elemZ * (elemW vWord * h * (elemW uWord * g))) → False := by
  simp only [liftOK, Bool.and_eq_true] at hlift
  obtain ⟨⟨⟨⟨⟨⟨hwu, hwv⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := hlift
  have hU : Rep 1408 (tabW uWord) (elemW uWord) := rep_elemW_of_gensOK hg hwu
  have hV : Rep 1408 (tabW vWord) (elemW vWord) := rep_elemW_of_gensOK hg hwv
  have hZ : Rep 1408 (tabW wordZ) elemZ := rep_elemW_of_gensOK hg (by decide)
  have hE : IsEnumSet 1408 (subgroupList capI nWords1)
      (wordSubgroup nWords1 : Set (Equiv.Perm (Fin 1408))) := (enumW_spec hN).2
  have houter : ∀ g ∈ wordSubgroup nWords1,
      ((elemW uWord * g) * (elemW uWord * g) = 1 ∨
        (elemW uWord * g) * (elemW uWord * g) = elemZ) →
      ∀ h ∈ wordSubgroup nWords1,
        ((elemW vWord * h) * (elemW vWord * h) = 1 ∨
          (elemW vWord * h) * (elemW vWord * h) = elemZ) →
        ¬ ((elemW uWord * g) * (elemW vWord * h) = (elemW vWord * h) * (elemW uWord * g) ∨
          (elemW uWord * g) * (elemW vWord * h) =
            elemZ * ((elemW vWord * h) * (elemW uWord * g))) := by
    refine (hE.forall_iff _ _ ?_).1 hall
    intro n g hn
    have ha : Rep 1408 (compT 1408 (tabW uWord) n) (elemW uWord * g) := Rep.compT hU hn
    rw [Bool.or_eq_true]
    rw [not_sqZ_iff ha hZ, inner_iff hN hV hZ ha]
    exact imp_iff_not_or.symm
  intro g hg h hh h1 h2 h3
  exact (houter g hg h1 h hh h2) h3

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
