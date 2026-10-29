module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KD291OuterDef
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporSmall
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamilies
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29Spor
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem spor_false (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (s : TauCeti.SporadicName) (e : ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hcen : centralizer (L : Set X) = ⊥) (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {x : X}
    (hxL : x ∈ L) (hxo : orderOf x = p)
    (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hout : ¬ p ∣ Nat.card (Outer ↥L) := by
    have h1 := hOut s p hp (by omega)
    rwa [← Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h1
  have hEL : ∀ E : Subgroup X, IsElemAbelian p E → E ≤ L := fun E hE y hy =>
    mem_of_pow_eq_one_of_not_dvd_card_outer hp L hcen hout (hE.2 y hy)
  have hL3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) :=
    h3.trans (pRank_top_le_pRank_top_of_forall_le L hEL)
  have hxo' : orderOf (⟨x, hxL⟩ : ↥L) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hxo
  have h4 := hR s p hp hp5 ↥L ⟨e⟩ hL3 ⟨x, hxL⟩ hxo'
  have h5 : CFSG.Open.pRank p (centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) ≤
      CFSG.Open.pRank p (centralizer ({x} : Set X)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 L.subtype L.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  omega

section DefChar


theorem outer_defChar_rank {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (hcen : centralizer (L : Set Y) = ⊥)
    {x : Y} (hxL : x ∉ L) (hxo : orderOf x = p) : 4 ≤ Open.pRank p (⊤ : Subgroup ↥L) := by
  obtain ⟨t, n, f, ht, hmodel⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3.kd291_lieModel_of_charp hp hp5 d hd e
  have hadm := hmodel.admissible
  have hf1 : 1 ≤ f := hadm.2.1
  have hαp : (MulAut.conjNormal x : MulAut ↥L) ^ p = 1 := by
    rw [← map_pow]
    have : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
    rw [this, map_one]
  have hαin : (MulAut.conjNormal x : MulAut ↥L) ∉ inner ↥L :=
    CFSG.ComponentClassification.RestrictedStd.Spor.conjNormal_not_mem_inner hcen hxL
  obtain ⟨f₀, hf0, -⟩ := CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds ↥L t n
    p f hadm hmodel ht p hp (by omega)
    (CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3.kd291_not_dvd_lieOrderDivisor hp hp5 t n
      hf1)
    (by rintro ⟨-, -, h3⟩; omega) (by rintro ⟨-, h3⟩; omega) _ hαp hαin
  have hf5 : 5 ≤ f := by
    have : 1 ≤ f₀ := by
      rcases Nat.eq_zero_or_pos f₀ with h | h
      · rw [h] at hf0; omega
      · exact h
    rw [hf0]
    nlinarith
  exact CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.N3.kd291_four_le_pRank_of_lieModel hp hp5
    hf5 hmodel

theorem le_pRank_L_of_defChar {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = p)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (hcen : centralizer (L : Set Y) = ⊥) {k : ℕ}
    (hk : k ≤ 4) (hkY : k ≤ Open.pRank p (⊤ : Subgroup Y)) :
    k ≤ Open.pRank p (⊤ : Subgroup ↥L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hall : ∀ E : Subgroup Y, IsElemAbelian p E → E ≤ L
  · exact hkY.trans (pRank_top_le_pRank_top_of_forall_le L hall)
  · push Not at hall
    obtain ⟨E, hE, hEL⟩ := hall
    obtain ⟨y, hyE, hyL⟩ := Set.not_subset.1 hEL
    have hy : y ^ p = 1 := hE.2 y hyE
    have hy1 : y ≠ 1 := fun h => hyL (h ▸ L.one_mem)
    have hyo : orderOf y = p := orderOf_eq_prime hy hy1
    exact hk.trans (outer_defChar_rank hp hp5 L d hd e hcen hyL hyo)

theorem defChar_false (hDef : KD291DefCharL) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type}
    [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal] (hs : IsSimpleGroup L)
    (hn : ∃ a b : L, a * b ≠ b * a) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1.characteristic = p) (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hcen : centralizer (L : Set Y) = ⊥) (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup Y)) {x : Y}
    (hxL : x ∈ L) (hxo : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hL4 := le_pRank_L_of_defChar hp hp5 L d hd e hcen le_rfl h4
  have hxo' : orderOf (⟨x, hxL⟩ : ↥L) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hxo
  have h5 : CFSG.Open.pRank p (centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L)) ≤
      CFSG.Open.pRank p (centralizer ({x} : Set Y)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 L.subtype L.subtype_injective _).trans
      (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({(⟨x, hxL⟩ : ↥L)} : Set ↥L) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hy')
  have h6 := hDef p hp hp5 ↥L hs hn ⟨d, hd, ⟨e⟩⟩ (by omega) ⟨x, hxL⟩ hxo' (h5.trans hx2)
  omega

end DefChar

section Inner


theorem cross_false (hAt : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X] (L : Subgroup X) [L.Normal]
    (hs : IsSimpleGroup L) (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L)
    (d : TauCeti.ValidLieTypeIndex) (hdp : d.1.characteristic ≠ p)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (hl : ¬ IsLinearOrUnitaryAt p L)
    (hcen : centralizer (L : Set X) = ⊥) (h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {x : X}
    (hxL : x ∈ L) (hx : orderOf x = p)
    (hxc : CFSG.Open.pRank p (centralizer ({x} : Set X)) ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hAb, hRk⟩ := hAt d
  exact false_of_cross_core L (pRank_quotient_le_one_of_catalog hp hp5 L hs hn hc hl hcen)
    (fun h3' y hy => hRk p hp hp5 hdp L hs ⟨e⟩ hl h3' y hy)
    (fun h2 => hAb p hp hp5 hdp L hs ⟨e⟩ hl h2) h3 hxL hx hxc

theorem inner_false (hOut : SporadicOutOdd) (hR : SporadicCentralizerRank)
    (hAt : ∀ d : TauCeti.ValidLieTypeIndex, CrossAt d) (hDef : KD291DefCharL) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hs : IsSimpleGroup L) (hn : ∃ a b : L, a * b ≠ b * a) (hc : IsCatalogGroup L)
    (hl : ¬ IsLinearOrUnitaryAt p L) (hcen : centralizer (L : Set Y) = ⊥)
    (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup Y)) {x : Y} (hxL : x ∈ L) (hxo : orderOf x = p)
    (hx2 : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2) : False := by
  obtain ⟨i, ⟨e⟩⟩ := id hc
  cases i with
  | cyclic r hr =>
    obtain ⟨a, b, hab⟩ := hn
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  | alternating n hn5 =>
    haveI := hs
    exact i294Alt_false hp hp5 L hn hn5 e hcen (by omega) hxL hxo hx2
  | sporadic s => exact spor_false hOut hR hp hp5 L s e hcen (by omega) hxL hxo hx2
  | lie m =>
    by_cases hch : m.1.characteristic = p
    · exact defChar_false hDef hp hp5 L hs hn m hch e hcen h4 hxL hxo hx2
    · exact cross_false hAt hp hp5 L hs hn hc m hch e hl hcen (by omega) hxL hxo hx2

end Inner

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
