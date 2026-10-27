module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreLevi

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K1525dCoreProof

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData KFactsSmall

variable (m : ℕ)

theorem isL3TwoModO2_of_adjacent {A : Subgroup (SLF2 m)} (hp : CFSG.Open.pRank 3 A ≤ 1)
    (hBA : bor m ≤ A) {j j' : Fin m} (hj : j'.val = j.val + 1)
    (hjA : rankOne (dat m).rootGroup j ≤ A) (hj'A : rankOne (dat m).rootGroup j' ≤ A) :
    IsL3TwoModO2 A := by
  have hct := isCTGroupDatum m (ZMod 2)
  have hext := steinbergExtras m (ZMod 2)
  have hNo : ∀ k : Fin m, rankOne (dat m).rootGroup k ≤ A → k = j ∨ k = j' := by
    intro k hk
    by_contra hcon
    push Not at hcon
    rcases Nat.lt_or_ge k.val j.val with hlt | hge
    · have := two_le_pRank_of_orthogonal m (i := k) (j := j') (by omega) hk hj'A
      omega
    · have hk1 : k.val ≠ j.val := fun h => hcon.1 (Fin.ext h)
      have hk2 : k.val ≠ j'.val := fun h => hcon.2 (Fin.ext h)
      have := two_le_pRank_of_orthogonal m (i := j) (j := k) (by omega) hjA hk
      omega
  have hI : negIndices (dat m) A = {j, j'} := by
    ext k
    constructor
    · intro hk
      rcases hNo k (rankOne_le_of_mem_negIndices hBA hk) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · have hA := (eq_parJ_negIndices hct hext hBA).le
      rintro (rfl | rfl)
      · exact mem_of_rankOne_le_parJ hct hext (hjA.trans hA)
      · exact mem_of_rankOne_le_parJ hct hext (hj'A.trans hA)
  exact isL3TwoModO2_of_negIndices m hj hBA hI

theorem core_sl (hm : 3 ≤ m) (A₁ A₂ : Subgroup (SLF2 m))
    (hcov : ∀ i : Fin m, pElementSubgroup 2 (minPar m i) ≤ A₁ ∨
      pElementSubgroup 2 (minPar m i) ≤ A₂)
    (h1 : CFSG.Open.pRank 3 A₁ ≤ 1) (h2 : CFSG.Open.pRank 3 A₂ ≤ 1) :
    IsL3TwoModO2 A₁ ∨ IsL3TwoModO2 A₂ := by
  have key : ∀ {A : Subgroup (SLF2 m)} {i : Fin m}, pElementSubgroup 2 (minPar m i) ≤ A →
      bor m ≤ A ∧ rankOne (dat m).rootGroup i ≤ A := fun h =>
    ⟨(bor_le_pElementSubgroup m _).trans h, (rankOne_le_pElementSubgroup m _).trans h⟩
  let a : Fin m := ⟨0, by omega⟩
  let b : Fin m := ⟨1, by omega⟩
  let c : Fin m := ⟨2, by omega⟩
  have hac : a.val + 2 ≤ c.val := by simp [a, c]
  have hab : b.val = a.val + 1 := rfl
  have hbc : c.val = b.val + 1 := rfl
  rcases hcov a with ha | ha <;> rcases hcov c with hc | hc
  · exfalso
    have := two_le_pRank_of_orthogonal m hac (key ha).2 (key hc).2
    omega
  · rcases hcov b with hb | hb
    · exact Or.inl (isL3TwoModO2_of_adjacent m h1 (key ha).1 hab (key ha).2 (key hb).2)
    · exact Or.inr (isL3TwoModO2_of_adjacent m h2 (key hb).1 hbc (key hb).2 (key hc).2)
  · rcases hcov b with hb | hb
    · exact Or.inl (isL3TwoModO2_of_adjacent m h1 (key hb).1 hbc (key hb).2 (key hc).2)
    · exact Or.inr (isL3TwoModO2_of_adjacent m h2 (key ha).1 hab (key ha).2 (key hb).2)
  · exfalso
    have := two_le_pRank_of_orthogonal m hac (key ha).2 (key hc).2
    omega

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15
