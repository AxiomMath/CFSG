module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamNoTwoAlt

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding.KFactProofs.SmallIdent Subgroup

theorem signalizerInnAt_altTwoP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 5 ≤ 2 * p) :
    SignalizerInnAt p (.alternating (2 * p) h) := by
  rintro K _ _ ⟨e⟩ B Y hB hBc hY hBY
  have hK : CFSG.AGLEmbedding.IsAltTwoP p K := Nonempty.intro e
  have hp' : ¬ p ∣ Nat.card Y := (Nat.Prime.coprime_iff_not_dvd hp).1 hY
  have hBp : IsPGroup p B := fun b => ⟨1, by simpa using Subtype.ext (hB.2 b b.2)⟩
  obtain ⟨S, hBS⟩ := hBp.exists_le_sylow
  have hSc : Nat.card (S : Subgroup K) = p ^ 2 := sylowSq_of_isAltTwoP hp hp2 hK S
  have hBeq : B = (S : Subgroup K) :=
    Subgroup.eq_of_le_of_card_ge hBS (le_of_eq (by rw [hBc, hSc]))
  have hSY : (S : Subgroup K) ≤ normalizer (Y : Set K) := by
    rw [← hBeq]
    exact hBY
  have hY1 : Y = ⊥ := eq_bot_of_normalizes_of_isAltTwoP hp hp2 hK S Y hp' hSY
  intro b _
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  rw [hY1] at hy
  rw [Subgroup.mem_bot.1 hy, one_mul, mul_one]

theorem center_eq_bot_altTwoP {p : ℕ} (h : 5 ≤ 2 * p) :
    ∀ (K : Type) [Group K] [Finite K],
      Nonempty (K ≃* (TauCeti.CFSGIndex.alternating (2 * p) h).Group) → center K = ⊥ := by
  rintro K _ _ ⟨e⟩
  have e' : K ≃* alternatingGroup (Fin (2 * p)) := e
  exact center_eq_bot_of_mulEquiv e'
    (alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))

theorem signalizerAutAt_altTwoP {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : 5 ≤ 2 * p) :
    SignalizerAutAt p (.alternating (2 * p) h) := by
  have hout : ¬ GL83OuterType24 p (.alternating (2 * p) h) := by
    rintro ⟨d, hd, -⟩
    cases hd
  exact signalizerAutAt_of_signalizerInnAt hp (center_eq_bot_altTwoP h) hout
    (signalizerInnAt_altTwoP hp hp2 h)

end CFSG.LocalAnalysis.RankFourTheoremC
