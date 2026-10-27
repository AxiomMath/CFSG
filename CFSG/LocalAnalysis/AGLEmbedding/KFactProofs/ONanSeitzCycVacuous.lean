module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCycTransport
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieChar
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem false_of_cyclic_index {K : Type*} [Group K] (hnab : ∃ a b : K, a * b ≠ b * a) (q : ℕ)
    (hq : q.Prime) (e : K ≃* (TauCeti.CFSGIndex.cyclic q hq).Group) : False := by
  obtain ⟨a, b, hab⟩ := hnab
  apply hab
  apply e.injective
  rw [map_mul, map_mul]
  exact mul_comm (e a) (e b)

theorem false_of_alternating {K : Type} [Group K] (n : ℕ) (hn : 5 ≤ n)
    (e : K ≃* (TauCeti.CFSGIndex.alternating n hn).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hnotInn : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) : False := by
  refine hnotInn (le_range_conj_of_not_dvd_card_outer hp ?_ hE)
  rw [card_outer_eq_of_mulEquiv e]
  exact not_dvd_card_outer_alternatingGroup n hn p hp hp2

theorem false_of_sporadic
    (hOutS : ∀ s : TauCeti.SporadicName, ∀ p : ℕ, p.Prime → p ≠ 2 →
      ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (TauCeti.CFSGIndex.sporadic s).Group))
    {K : Type*} [Group K] (s : TauCeti.SporadicName)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hnotInn : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) : False := by
  refine hnotInn (le_range_conj_of_not_dvd_card_outer hp ?_ hE)
  rw [card_outer_eq_of_mulEquiv e]
  exact hOutS s p hp hp2

theorem false_of_lie_char (hRank : AGLEmbeddingD2.KFactLieCharRank)
    (hOut : AGLEmbeddingD2.KFactLieCharOut) {K : Type} [Group K] [Finite K]
    (d : TauCeti.ValidLieTypeIndex) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p = d.1.characteristic) (T : Sylow p K)
    (hT : IsCyclic (T : Subgroup K)) {E : Subgroup (MulAut K)} (hE : IsElemAbelian p E)
    (hnotInn : ¬ E ≤ (MulAut.conj : K →* MulAut K).range) : False := by
  by_cases hsmall : AGLEmbeddingD2.IsD2LieCharSmall p d.1
  · exact hnotInn (le_range_conj_of_not_dvd_card_outer hp (hOut K d ⟨e⟩ p hp hp2 hsmall) hE)
  · have h3 := hRank K d ⟨e⟩ p hp hp2 hpd hsmall
    have h1 := pRank_le_one_of_isCyclic_sylow hp T hT
    omega

end CFSG.AGLEmbedding
