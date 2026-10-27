module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankLists
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SecRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517A
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair

section DvdSpom

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_normalizer_of_spom_aux1 (p n : ℕ) (h : p ∣ n + 1) : p ∣ n ^ 2 - 1 := by
  rcases n with _ | m
  · simp
  · have e : (m + 1) ^ 2 - 1 = (m + 1 + 1) * m := by
      apply Nat.sub_eq_of_eq_add
      ring
    rw [e]
    exact Dvd.dvd.mul_right h m

theorem dvd_card_normalizer_of_spom (hK : K517_4a) {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls) {p : ℕ} (hp : p.Prime)
    (hbad : IsSpSix (fun Q => p ∣ Q + 1) ↥Ls ∨ IsOmegaEightMinus (fun Q => p ∣ Q + 1) ↥Ls) :
    p ∣ Nat.card (Subgroup.normalizer (T₁ : Set X)) ∧ p ∣ Nat.card (Subgroup.normalizer (T₂ : Set X)) := by
  obtain ⟨hsimple, hnab⟩ := bad1517_aux_simple_nonabelian (p := p) (S := ↥Ls) (Or.inr hbad)
  haveI := hsimple
  have hZ : Subgroup.center ↥Ls = ⊥ := bad1517_aux_center_eq_bot hnab
  have key : ∃ (Q : TauCeti.PrimePower) (d : TauCeti.ValidLieTypeIndex), Q.p = 2 ∧ p ∣ Q.card + 1 ∧
      (d.1 = TauCeti.LieTypeIndex.B 3 Q ∨ d.1 = TauCeti.LieTypeIndex.twistedD 4 Q) ∧
      Nonempty (↥Ls ≃* (TauCeti.CFSGIndex.lie d).Group) := by
    rcases hbad with ⟨Q, hQ2, hc, d, hd, he⟩ | ⟨Q, hQ2, hc, d, hd, he⟩
    · exact ⟨Q, d, hQ2, hc, Or.inl hd, he⟩
    · exact ⟨Q, d, hQ2, hc, Or.inr hd, he⟩
  obtain ⟨Q, d, hQ2, hdvdQ, hdB, ⟨e⟩⟩ := key
  have hrk : IsRankTwoPlus d.1 := by
    rcases hdB with h | h <;> rw [h] <;> exact ⟨hQ2, by norm_num⟩
  have hiq : KFactsPair.indexQ d.1 = Q.card := by
    rcases hdB with h | h <;> rw [h] <;> rfl
  have hiso : Nonempty ((↥Ls ⧸ Subgroup.center ↥Ls) ≃* (TauCeti.CFSGIndex.lie d).Group) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩
  have hdvd : p ∣ KFactsPair.indexQ d.1 ^ 2 - 1 := by
    rw [hiq]
    exact dvd_card_normalizer_of_spom_aux1 p Q.card hdvdQ
  obtain ⟨h1, h2⟩ := hK X T T₁ T₂ hX hg Ls hLs d hrk hiso p hp hdvd
  exact ⟨(dvd_card_normalizer_of_dvd_gnA T T₁ Ls hp h1).trans (Subgroup.card_dvd_of_le inf_le_left),
    (dvd_card_normalizer_of_dvd_gnA T T₂ Ls hp h2).trans (Subgroup.card_dvd_of_le inf_le_left)⟩

end DvdSpom

theorem three_dvd_card_of_pRank {Y : Type} [Group Y] [Finite Y]
    (h : 1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y)) : 3 ∣ Nat.card Y := by
  obtain ⟨E, -, -, hE⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup Y)
  have hk : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≠ 0 := by omega
  have h3 : 3 ∣ Nat.card E := by
    rw [hE]
    exact dvd_pow_self 3 hk
  have hEY : Nat.card E ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le (le_top : E ≤ ⊤)
    rwa [Subgroup.card_top] at this
  exact h3.trans hEY

end CFSG.LocalAnalysis.RankThreeUC.S15
