module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Grp
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCount
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem card_le_of_twoLocalRank_le {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {B F W : Subgroup Y} (hB : IsElemAbelian p B)
    (hr : GLATwoLocalRank p Y ≤ CFSG.Open.pRank p B)
    (hF : IsElemAbelian p F) (hFW : F ≤ Subgroup.normalizer (W : Set Y)) (hW : W ≠ ⊥)
    (hWp : IsPGroup 2 W) : Nat.card F ≤ Nat.card B := by
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian hp hF
  have hk : m ≤ CFSG.Open.pRank p (Subgroup.normalizer (W : Set Y)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hFW hF hm
  have hN : CFSG.Open.pRank p (Subgroup.normalizer (W : Set Y)) ≤ GLATwoLocalRank p Y := by
    unfold GLATwoLocalRank CFSG.Open.twoLocalPrimeRank
    exact le_csSup (bddAbove_twoLocalPRanks hp.one_lt) ⟨_, ⟨W, hW, hWp, rfl⟩, rfl⟩
  obtain ⟨mB, hmB⟩ := exists_card_eq_pow_of_isElemAbelian hp hB
  have hBr : CFSG.Open.pRank p B ≤ mB := by
    refine CFSG.SectionRank.pRank_le hp.one_lt (fun E hEB _ => ?_)
    rw [← hmB]
    exact Subgroup.card_le_of_le hEB
  rw [hm, hmB]
  exact Nat.pow_le_pow_right hp.pos (hk.trans (hN.trans (hr.trans hBr)))

theorem hmax_of_rank {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {B : Subgroup Y}
    (hB : IsElemAbelian p B) (hr : GLATwoLocalRank p Y ≤ CFSG.Open.pRank p B) :
    ∀ F : Subgroup Y, IsElemAbelian p F →
      (∃ W : Subgroup Y, W ≠ ⊥ ∧ IsPGroup 2 W ∧ F ≤ Subgroup.normalizer (W : Set Y)) →
      Nat.card F ≤ Nat.card B := by
  rintro F hF ⟨W, hW, hWp, hFW⟩
  exact card_le_of_twoLocalRank_le hp hB hr hF hFW hW hWp

theorem card_le_nine_of_pRank_le_two {M : Type} [Group M] [Finite M] {H : Subgroup M}
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup M) ≤ 2) (hH : IsElemAbelian 3 H) :
    Nat.card H ≤ 9 := by
  obtain ⟨m, hm⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hH
  have hk : m ≤ CFSG.Open.pRank 3 (⊤ : Subgroup M) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hH hm
  rw [hm]
  calc 3 ^ m ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hk.trans hr)
    _ = 9 := by norm_num

theorem card_center_of_mulEquiv {A C : Type} [Group A] [Group C] (e : A ≃* C) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center C) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem catalogIs_of_mulEquiv {A C : Type} [Group A] [Group C] {Q : TauCeti.CFSGIndex → Prop}
    (e : A ≃* C) (h : catalogIs A Q) : catalogIs C Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.symm.trans f⟩⟩

theorem catalogIs_center_quot_of_mulEquiv {A C : Type} [Group A] [Group C]
    {Q : TauCeti.CFSGIndex → Prop} (e : A ≃* C)
    (h : catalogIs (A ⧸ Subgroup.center A) Q) : catalogIs (C ⧸ Subgroup.center C) Q :=
  catalogIs_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center C) e (Subgroup.map_center_eq e)) h

theorem elemCommute_cj_of_mem {Y : Type} [Group Y] [Finite Y] {B K : Subgroup Y}
    (hB : IsElemAbelian 3 B) (hK : CFSG.Open.IsComponentOf K ⊤) {b : Y} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K : Set Y)) : ElemCommute K (cj b K) := by
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i112f_three_commute hB hK (x := b⁻¹)
    (B.inv_mem hb) (fun h' => hbN (by simpa using (Subgroup.normalizer (K : Set Y)).inv_mem h'))
  have hc : GLBConj b⁻¹ K = cj b K := by
    unfold GLBConj cj
    rw [inv_inv]
  intro a ha c hc'
  rw [← hc] at hc'
  exact h.1 a ha c hc'

end CFSG.LocalAnalysis.GLTheoremA.I114
