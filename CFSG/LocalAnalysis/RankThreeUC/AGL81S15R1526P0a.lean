module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.ParabolicCover
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.Open.LocalVocabulary
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankBase
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511C
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.Bridge
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.Omega8Cited
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs
import CFSG.Quasithin.Background.B15P4LayerDict

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement
section LThreeLift

variable {X : Type} [Group X] [Finite X]
theorem isLThreeTwo_of_isLThreeOfExp_one {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsLThreeTwo S := by
  rcases h with ⟨-, d, q, hq, hd, e⟩ | ⟨h, -⟩
  · exact ⟨d, ⟨q, hq, hd⟩, e⟩
  · omega

theorem card_eq_of_isLThreeOfExp_one {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    Nat.card S = 168 :=
  CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_card_eq (isLThreeTwo_of_isLThreeOfExp_one h)

theorem card_barO2_mul (L : Subgroup X) :
    Nat.card (barO2 L) * Nat.card (L ⊓ CFSG.pCore 2 X : Subgroup X) = Nat.card L := by
  have h1 : Nat.card (barO2 L) = (CFSG.pCore 2 X).relIndex L :=
    CFSG.Quasithin.E1.card_barO2_eq_relIndex L
  have h2 := Subgroup.relIndex_mul_card (CFSG.pCore 2 X) L
  rw [inf_comm] at h2
  rw [h1]
  exact h2

theorem pRank_le_one_of_not_sq_dvd {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} {q : ℕ}
    (hq : q.Prime) (h : ¬ q ^ 2 ∣ Nat.card K) : CFSG.Open.pRank q K ≤ 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  refine CFSG.SectionRank.pRank_le hq.one_lt ?_
  intro E hEK hE
  have hEp : IsPGroup q E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hEp
  have hdvd : q ^ j ∣ Nat.card K := hj ▸ Subgroup.card_dvd_of_le hEK
  have hj1 : j ≤ 1 := by
    by_contra hj2
    push Not at hj2
    exact h ((pow_dvd_pow q hj2).trans hdvd)
  rw [hj]
  exact Nat.pow_le_pow_right hq.pos hj1

theorem card_sylow_three_of_isLThree {L A : Subgroup X} (hL : IsC2 L)
    (h3 : IsLThreeOfExp 1 ↥(barO2 L)) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) :
    Nat.card A = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_barO2_mul L
  rw [card_eq_of_isLThreeOfExp_one h3] at hcard
  have hK : IsPGroup 2 (L ⊓ CFSG.pCore 2 X : Subgroup X) :=
    (CFSG.pCore_isPGroup (p := 2) (G := X)).to_le inf_le_right
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hK
  rw [ha] at hcard
  have hf : (Nat.card L).factorization 3 = 1 := by
    rw [← hcard]
    have h168 : (168 : ℕ) * 2 ^ a = 2 ^ (a + 3) * 3 * 7 := by ring
    rw [h168, Nat.factorization_mul (by positivity) (by norm_num),
      Nat.factorization_mul (by positivity) (by norm_num)]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three,
      Nat.Prime.factorization (by norm_num : Nat.Prime 7)]
  rw [hA.card_eq, hf]
  norm_num

theorem pRank_eq_one_of_isLThree {L : Subgroup X} (hL : IsC2 L) (h : IsLThreeOfExp 1 ↥(barO2 L)) :
    CFSG.Open.pRank 3 L = 1 ∧ CFSG.Open.pRank 7 L = 1 := by
  have hc := card_eq_of_isLThreeOfExp_one h
  have key : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 168 → ¬ q ^ 2 ∣ 168 → CFSG.Open.pRank q L = 1 := by
    intro q hq hq2 h1 h2
    rw [pRank_barO2_eq hL hq hq2]
    apply le_antisymm
    · exact pRank_le_one_of_not_sq_dvd hq (by rw [hc]; exact h2)
    · exact one_le_pRank_of_dvd _ hq (by rw [hc]; exact h1)
  exact ⟨key 3 Nat.prime_three (by norm_num) (by norm_num) (by norm_num),
    key 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

theorem not_isPSolvable_barO2_of_isLThree {L : Subgroup X}
    (h3 : IsLThreeOfExp 1 ↥(barO2 L)) : ¬ CFSG.HallHigman.IsPSolvable 7 ↥(barO2 L) := by
  intro hps
  have hsimple := CFSG.AGLEmbeddingD2.McLaughlin.isLThreeTwo_simple
    (isLThreeTwo_of_isLThreeOfExp_one h3)
  have hc := card_eq_of_isLThreeOfExp_one h3
  have e : (↥(⊤ : Subgroup ↥(barO2 L)) ⧸ (⊥ : Subgroup ↥(⊤ : Subgroup ↥(barO2 L)))) ≃*
      ↥(barO2 L) := QuotientGroup.quotientBot.trans Subgroup.topEquiv
  haveI : IsSimpleGroup (↥(⊤ : Subgroup ↥(barO2 L)) ⧸
      (⊥ : Subgroup ↥(⊤ : Subgroup ↥(barO2 L)))) := MulEquiv.isSimpleGroup e
  have h := hps ⊤ Subgroup.IsSubnormal.top ⊥ inferInstance
  rw [Subgroup.index_bot, Subgroup.card_top, hc] at h
  rcases h with h | h
  · omega
  · norm_num at h

theorem gnV_le_pCore {T : Subgroup X} (hX : GNSetting X T) : gnV T ≤ CFSG.pCore 2 X := by
  have hn : (gnV T).Normal := Subgroup.normalClosure_normal
  have hea := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.isElemAbelian_gnV T hX
  have hp : IsPGroup 2 (gnV T) := fun x => ⟨1, by
    have := hea.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  exact le_sSup ⟨hn, hp⟩
end LThreeLift
theorem isSimpleGroup_of_isLThreeOfExp_one {S : Type} [Group S] (h : IsLThreeOfExp 1 S) :
    IsSimpleGroup S := by
  refine R1511C.isSimpleGroup_of_isLThreeTwoPow ?_
  rcases h with ⟨-, d, q, hq, hd, he⟩ | ⟨h2, -⟩
  · exact Or.inr ⟨d, ⟨q, hq, hd⟩, he⟩
  · omega
end CFSG.LocalAnalysis.RankThreeUC.S15
