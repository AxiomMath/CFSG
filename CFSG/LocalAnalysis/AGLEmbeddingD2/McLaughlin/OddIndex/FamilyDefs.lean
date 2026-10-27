module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Lift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.OvergroupDefs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

@[expose] def OvergroupL32Odd (K : Type) [Group K] [Finite K] : Prop :=
  IsSimpleGroup K → (∃ a b : K, a * b ≠ b * a) → Open.IsCatalogGroup K →
    (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W Y : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W → Y ≤ W →
      A ≤ Y → IsLThreeTwo (↥Y ⧸ CFSG.pCore 2 ↥Y) → W = ⊤ ∨ ¬ 2 ∣ W.index

@[expose] def OvergroupL32L2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 3 → d.1 = .A 1 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupL32Odd K

@[expose] def OvergroupL32L3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.card % 3 = 2 → d.1 = .A 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupL32Odd K

@[expose] def OvergroupL32U3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.card % 3 = 1 → d.1 = .twistedA 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupL32Odd K

@[expose] def OvergroupL32J1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) → OvergroupL32Odd K

theorem overgroupL32Odd_of_A5 (K : Type) [Group K] [Finite K]
    (e : Nonempty (K ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group)) : OvergroupL32Odd K := by
  intro _ _ _ _ A W Y _ _ _ _ hY
  exfalso
  obtain ⟨e⟩ := e
  have hK : Nat.card K = 60 := by
    rw [Nat.card_congr e.toEquiv]
    show Nat.card (alternatingGroup (Fin 5)) = 60
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have h168 : 168 ∣ Nat.card Y := by
    rw [← isLThreeTwo_card_eq hY]
    exact Subgroup.card_dvd_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y))
  have hYK : Nat.card Y ∣ Nat.card K := Subgroup.card_subgroup_dvd_card Y
  rw [hK] at hYK
  have := Nat.le_of_dvd (by norm_num) (h168.trans hYK)
  omega

theorem kFactThreeRankOneOvergroupL32_of_families
    (hS : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    (h2 : OvergroupL32L2) (h3 : OvergroupL32L3) (hu : OvergroupL32U3) (hj : OvergroupL32J1) :
    KFactThreeRankOneOvergroupL32 := by
  intro K _ _ hK hnab hcat hcyc A W Y hA hNW hYW hAY hY
  obtain ⟨i, he⟩ := hcat
  have hr := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.pRank_three_eq_one_of_cyclic
    hcyc hA
  have key : OvergroupL32Odd K := by
    rcases hS K hK hnab i he hr with
      ⟨d, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), he'⟩ | he' | he'
    · exact h2 K d q hq hd he'
    · exact h3 K d q hq hd he'
    · exact hu K d q hq hd he'
    · exact hj K he'
    · exact overgroupL32Odd_of_A5 K he'
  exact key hK hnab ⟨i, he⟩ hcyc A W Y hA hNW hYW hAY hY

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
