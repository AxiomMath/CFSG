module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811CycDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOne

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

@[expose] def OvergroupOddIndex (K : Type) [Group K] [Finite K] : Prop :=
  IsSimpleGroup K → (∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) →
    ∀ A W : Subgroup K, Nat.card A = 3 → Subgroup.normalizer (A : Set K) ≤ W →
      ¬ CFSG.HallHigman.IsPSolvable 3 ↥W → ¬ 16 ∣ W.index → Odd W.index

@[expose] def KFactOvergroupL2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.p ≠ 3 → d.1 = .A 1 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupOddIndex K

@[expose] def KFactOvergroupL3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.card % 3 = 2 → d.1 = .A 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupOddIndex K

@[expose] def KFactOvergroupU3 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    q.card % 3 = 1 → d.1 = .twistedA 2 q → Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group) →
      OvergroupOddIndex K

@[expose] def KFactOvergroupJ1 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J1).Group) → OvergroupOddIndex K

@[expose] def KFactOvergroupA5 : Prop :=
  ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* (TauCeti.CFSGIndex.alternating 5 le_rfl).Group) → OvergroupOddIndex K

theorem pRank_three_eq_one_of_cyclic {K : Type} [Group K] [Finite K]
    (hcyc : ∀ X : Subgroup K, IsPGroup 3 X → IsCyclic X) {A : Subgroup K}
    (hA : Nat.card A = 3) : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsGreatest.csSup_eq ⟨⟨A, le_top, ?_, by rw [hA, pow_one]⟩, ?_⟩
  · have : IsCyclic A := isCyclic_of_prime_card hA
    refine ⟨IsCyclic.isMulCommutative, fun x hx => ?_⟩
    have h := pow_card_eq_one' (G := A) (x := ⟨x, hx⟩)
    rw [hA] at h
    exact congrArg Subtype.val h
  · rintro k ⟨E, -, ⟨-, hexp⟩, hE⟩
    have hp : IsPGroup 3 E := IsPGroup.of_card hE
    obtain ⟨g, hg⟩ := (hcyc E hp).exists_generator
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hexp g g.2))
    rw [hord, hE] at h3
    by_contra hk
    have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := Nat.le_of_dvd (by norm_num) (this.trans h3)
    norm_num at this

theorem kFactThreeRankOneOvergroup_of_families (hS : KFactThreeRankOneSimple)
    (h2 : KFactOvergroupL2) (h3 : KFactOvergroupL3) (hu : KFactOvergroupU3)
    (hj : KFactOvergroupJ1) (h5 : KFactOvergroupA5) : KFactThreeRankOneOvergroup := by
  intro K _ _ hK hnab ⟨i, he⟩ hcyc A W hA hNW hW h16
  have hr := pRank_three_eq_one_of_cyclic hcyc hA
  rcases hS K hK hnab i he hr with ⟨d, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), he'⟩ | he' | he'
  · exact h2 K d q hq hd he' hK hcyc A W hA hNW hW h16
  · exact h3 K d q hq hd he' hK hcyc A W hA hNW hW h16
  · exact hu K d q hq hd he' hK hcyc A W hA hNW hW h16
  · exact hj K he' hK hcyc A W hA hNW hW h16
  · exact h5 K he' hK hcyc A W hA hNW hW h16

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811
