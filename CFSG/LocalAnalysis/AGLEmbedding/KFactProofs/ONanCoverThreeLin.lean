module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverThreeAut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.RankThree.PartOne.N143.LieLeaves
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaKFacts3Out
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverThree

open CFSG.Open TauCeti CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.AGLEmbedding.KFactProofs.CoverFive (isQuasisimple_of_open)
open CFSG.RankThree.PartTwo.Sec4.Census (tableOrder card_center_dvd_tableOrder lieModel_typeA
  lieModel_of_statedClassicalModel)
open CFSG.RankThree.PartOne.N143 (IsLieThreeIndex IsLieE6Index)
open CFSG.AGLEmbeddingD2 (KFactSeitzRankTwo IsD2SeitzException)

theorem tableOrder_psl_three_dvd (p f : ℕ) : tableOrder .PSL (2 + 1) p f ∣ 48 := by
  unfold tableOrder
  have h1 : (CFSG.Blueprint.Multiplier.genericOrders .PSL (2 + 1) p f) =
      (Nat.gcd 3 (p ^ f - 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have h2 : (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (2 + 1) p f).1 *
      (CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (2 + 1) p f).2 ∣ 16 := by
    by_cases hp : p = 2
    · subst hp
      rcases f with _ | _ | _ | f
      · simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      · simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      · simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
      · simp [CFSG.Blueprint.Multiplier.exceptionalOrders]
    · have : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL (2 + 1) p f = (1, 1) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        split <;> simp_all
      simp [this]
  rw [h1]
  have h3 : Nat.gcd 3 (p ^ f - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have := mul_dvd_mul (mul_dvd_mul h3 (dvd_refl 1)) h2
  simpa using this

theorem tableOrder_psu_three_dvd (p f : ℕ) : tableOrder .PSU (2 + 1) p f ∣ 3 := by
  unfold tableOrder
  have h1 : (CFSG.Blueprint.Multiplier.genericOrders .PSU (2 + 1) p f) =
      (Nat.gcd 3 (p ^ f + 1), 1) := by
    simp [CFSG.Blueprint.Multiplier.genericOrders]
  have h2 : CFSG.Blueprint.Multiplier.exceptionalOrders .PSU (2 + 1) p f = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [h1, h2]
  simpa using Nat.gcd_dvd_left 3 (p ^ f + 1)

theorem card_center_linThree (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (hZp : IsPGroup 3 (Subgroup.center K))
    (hZ : Subgroup.center K ≠ ⊥) {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    Nat.card (Subgroup.center K) = 3 := by
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, -⟩ | ⟨q, hq, -⟩
  · change dd = .A 2 q at hq
    subst hq
    exact card_center_eq_three_of_dvd hZp hZ (m := 48)
      ((card_center_dvd_tableOrder hGA (isQuasisimple_of_open hK) e (lieModel_typeA 2 q hv)).trans
        (tableOrder_psl_three_dvd q.p q.exponent)) (by norm_num)
  · change dd = .twistedA 2 q at hq
    subst hq
    exact card_center_eq_three_of_dvd hZp hZ (m := 3)
      ((card_center_dvd_tableOrder hGA (isQuasisimple_of_open hK) e
        (lieModel_of_statedClassicalModel
          (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
            (MulEquiv.refl _)))).trans (tableOrder_psu_three_dvd q.p q.exponent)) (by norm_num)

theorem isLinThreeCover3_of_isLieThreeIndex {d : ValidLieTypeIndex}
    (h : IsLieThreeIndex (CFSGIndex.lie d)) : IsLinThreeCover3 d := by
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A r q =>
    obtain ⟨rfl, h3⟩ := h
    exact Or.inl ⟨q, rfl, h3⟩
  | twistedA r q =>
    obtain ⟨rfl, h3⟩ := h
    exact Or.inr ⟨q, rfl, h3⟩
  | _ => exact h.elim

theorem three_ne_characteristic {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d) :
    3 ≠ d.1.characteristic := by
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, h3⟩ | ⟨q, hq, h3⟩
  · change dd = .A 2 q at hq
    subst hq
    intro h
    simp only [LieTypeIndex.characteristic_A] at h
    have h1 : 0 < q.p ^ q.exponent := pow_pos q.prime_p.pos _
    have h2 : 3 ∣ q.p ^ q.exponent := h ▸ dvd_pow_self _ q.exponent_pos.ne'
    rw [PrimePower.card_def] at h3
    omega
  · change dd = .twistedA 2 q at hq
    subst hq
    intro h
    simp only [LieTypeIndex.characteristic_twistedA] at h
    have h2 : 3 ∣ q.p ^ q.exponent := h ▸ dvd_pow_self _ q.exponent_pos.ne'
    rw [PrimePower.card_def] at h3
    omega

theorem not_isD2SeitzException_linThree {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d)
    (hnot : ¬ ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) :
    ¬ IsD2SeitzException 3 d.1 := by
  obtain ⟨dd, hv⟩ := d
  rcases hd with ⟨q, hq, -⟩ | ⟨q, hq, -⟩
  · change dd = .A 2 q at hq
    subst hq
    simp [IsD2SeitzException]
    exact fun hp hf => hnot ⟨q, hp, hf, rfl⟩
  · change dd = .twistedA 2 q at hq
    subst hq
    simp [IsD2SeitzException]

theorem kGenTwoModAb_of_seitz {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hS : KFactSeitzRankTwo) {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d)
    (hnot : ¬ ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) : KGenTwoModAb 3 K := by
  have hperf : Group.IsPerfect K := ⟨hK.1⟩
  exact kGenTwoModAb_of_kGenTwoMod (kGenTwoMod_of_seitz hperf e fun E' hE' hc =>
    hS d 3 Nat.prime_three (by norm_num) (three_ne_characteristic hd)
      (not_isD2SeitzException_linThree hd hnot) E' hE' hc)

@[expose] def SL3FourGenTwoModAb : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Nat.card (Subgroup.center K) = 3 →
    ∀ d : ValidLieTypeIndex, (∃ q : PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) →
      Nonempty (K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) → KGenTwoModAb 3 K

@[expose] def SL3CoverGenTwoModAb : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Nat.card (Subgroup.center K) = 3 →
    ∀ d : ValidLieTypeIndex, IsLinThreeCover3 d →
      Nonempty (K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) → KGenTwoModAb 3 K

theorem sl3CoverGenTwoModAb_of_seitz (hS : KFactSeitzRankTwo) (hFour : SL3FourGenTwoModAb) :
    SL3CoverGenTwoModAb := by
  intro K _ _ hK hZ3 d hd ⟨e⟩
  by_cases h4 : ∃ q : PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q
  · exact hFour K hK hZ3 d h4 ⟨e⟩
  · exact kGenTwoModAb_of_seitz hK hS hd h4 e

@[expose] def CoverE6RankFour : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K → Subgroup.center K ≠ ⊥ →
    IsPGroup 3 (Subgroup.center K) → IsCyclic (Subgroup.center K) →
    ∀ d : ValidLieTypeIndex, IsLieE6Index (CFSGIndex.lie d) →
      Nonempty (K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) →
      4 ≤ Open.pRank 3 (⊤ : Subgroup K)

theorem linThree_case (hGA : GriessMultipliersAllModels) (hR1 : SL3CoverGenTwoModAb)
    {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hZp : IsPGroup 3 (Subgroup.center K)) (hZ : Subgroup.center K ≠ ⊥)
    {d : ValidLieTypeIndex} (hd : IsLinThreeCover3 d)
    (e : K ⧸ Subgroup.center K ≃* (CFSGIndex.lie d).Group) :
    KGenTwoModAb 3 K ∧ Nat.card (Subgroup.center K) = 3 ∧ KOutNormalSylow 3 K := by
  have hZ3 := card_center_linThree hGA hK hZp hZ hd e
  exact ⟨hR1 K hK hZ3 d hd ⟨e⟩, hZ3, kFactSL3OutNormalSylow K hK d hd ⟨e⟩⟩

end CFSG.AGLEmbedding.KFactProofs.CoverThree
