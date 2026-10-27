module

public import CFSG.Open.StatedDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinFldGrp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LieType.SemisimpleCentralizers.HeldLangPSL
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem nonempty_centerQuot_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nonempty (X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem nonempty_centerQuot_sl {X : Type} [Group X] {E : Type} [Field E] (a : ℕ)
    (e : X ≃* Matrix.SpecialLinearGroup (Fin a) E) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨eZ⟩ := nonempty_centerQuot_of_mulEquiv e
  exact ⟨eZ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj a E)⟩

theorem nonempty_centerQuot_su {X : Type} [Group X] {E : Type} [Field E]
    {a q' Q : ℕ} (hq' : q' = Q) (e : X ≃* ↥(StatedSU a q' E))
    (τ : E ≃+* E) (hτ : ∀ y, τ (τ y) = y) (hτQ : ∀ y, τ y = y ^ Q) :
    Nonempty (X ⧸ Subgroup.center X ≃*
      ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ)) := by
  have hEq : heldSU a E τ hτ = StatedSU a Q E :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU hτQ
  have hEq' : StatedSU a q' E = heldSU a E τ hτ := by rw [hq']; exact hEq.symm
  exact nonempty_centerQuot_of_mulEquiv (e.trans (MulEquiv.subgroupCongr hEq'))

theorem nonempty_centerQuot_sp {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    {s : ℕ} (hs : 2 ≤ s) (hne : ¬(s = 2 ∧ Nat.card K = 2)) (hchar : CharP K 2)
    (e : X ≃* StatedSp s K) :
    Nonempty (X ⧸ Subgroup.center X ≃* StatedProj (StatedSp s K)) := by
  haveI : NeZero s := ⟨by omega⟩
  haveI := hchar
  let e' : X ≃* StatedProj (StatedSp s K) :=
    e.trans (MulEquiv.ofBijective (proj s K)
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo))
  obtain ⟨hsimp, hperf⟩ :=
    CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (r := s) (k := K) hs hne
  haveI : IsSimpleGroup (StatedProj (StatedSp s K)) := hsimp
  haveI : Group.IsPerfect (StatedProj (StatedSp s K)) := hperf
  haveI : IsSimpleGroup X := e'.isSimpleGroup
  haveI : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLinFld.nonempty_quotCenter_equiv e'

theorem linCase_of_factor {Y X : Type} [Group Y] [Group X] {ℓ n : ℕ}
    (eY : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X)
    (h : ∃ (m j : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 2 ≤ m ∧ 1 ≤ j ∧ ringChar E = ℓ ∧
      Fintype.card E = (2 ^ n) ^ j ∧ (m = 2 → 4 ≤ Fintype.card E) ∧
      Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin m) E)) :
    ∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E), 2 ≤ a ∧ Nat.card E = 2 ^ k ∧
      n ∣ k ∧ Nonempty (Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL a E)) := by
  obtain ⟨a, j, E, hEfield, hEf, ha2, -, -, hcardE, -, ⟨eX⟩⟩ := h
  letI := hEfield
  letI := hEf
  have hcard : Nat.card E = 2 ^ (n * j) := by
    rw [Nat.card_eq_fintype_card, hcardE, pow_mul]
  obtain ⟨eXZ⟩ := nonempty_centerQuot_sl (a := a) eX
  exact ⟨a, n * j, E, inferInstance, inferInstance, ha2, hcard, dvd_mul_right n j,
    ⟨eY.trans eXZ⟩⟩

theorem uniCase_of_factor {Y X : Type} [Group Y] [Group X] {ℓ n : ℕ}
    (eY : Y ⧸ Subgroup.center Y ≃* X ⧸ Subgroup.center X)
    (h : ∃ (m j q' : ℕ) (E : Type) (_ : Field E) (_ : Fintype E), 3 ≤ m ∧ 1 ≤ j ∧
      ringChar E = ℓ ∧ q' = (2 ^ n) ^ j ∧ Fintype.card E = q' ^ 2 ∧ (m, q') ≠ (3, 2) ∧
      Nonempty (X ≃* ↥(StatedSU m q' E))) :
    ∃ (a k : ℕ) (E : Type) (_ : Field E) (_ : Finite E) (τ : E ≃+* E)
      (hτ : ∀ y, τ (τ y) = y), 2 ≤ a ∧ (∀ y, τ y = y ^ (2 ^ k)) ∧
      Nat.card E = (2 ^ k) ^ 2 ∧ n ∣ k ∧
      Nonempty (Y ⧸ Subgroup.center Y ≃*
        ↥(heldSU a E τ hτ) ⧸ Subgroup.center ↥(heldSU a E τ hτ)) := by
  obtain ⟨a, j, q', E, hEfield, hEf, ha3, -, -, hq', hcardE, -, ⟨eX⟩⟩ := h
  letI := hEfield
  letI := hEf
  have hq'' : q' = 2 ^ (n * j) := by rw [hq', pow_mul]
  have hcard : Nat.card E = (2 ^ (n * j)) ^ 2 := by
    rw [Nat.card_eq_fintype_card, hcardE, hq'']
  obtain ⟨τ, hτq, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hcard
  obtain ⟨eXZ⟩ := nonempty_centerQuot_su (Q := 2 ^ (n * j)) hq'' eX τ hτ hτq
  exact ⟨a, n * j, E, inferInstance, inferInstance, τ, hτ, by omega, hτq, hcard,
    dvd_mul_right n j, ⟨eY.trans eXZ⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot

end
