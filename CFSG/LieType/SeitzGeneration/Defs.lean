module

public import CFSG.LieType.SeitzGeneration.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

abbrev Cat (d : TauCeti.ValidLieTypeIndex) : Type := (TauCeti.CFSGIndex.lie d).Group

@[expose] def SeitzPlanes
    (S : ∀ d : TauCeti.ValidLieTypeIndex, ℕ → Subgroup (MulAut (Cat d)) → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) (p : ℕ), p.Prime → p ≠ 2 → p ≠ d.1.characteristic →
    ¬ IsD2SeitzException p d.1 → ∀ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E →
      Nat.card E = p ^ 2 → S d p E → PlaneGen E

@[expose] def InnerPlane (d : TauCeti.ValidLieTypeIndex) (_ : ℕ)
    (E : Subgroup (MulAut (Cat d))) : Prop :=
  E ≤ (MulAut.conj : Cat d →* MulAut (Cat d)).range

@[expose] def RankLE2 (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ F : Subgroup K, IsElemAbelian p F → Nat.card F ≤ p ^ 2

@[expose] def KFactSeitzRankTwoInner : Prop := SeitzPlanes InnerPlane

@[expose] def KFactSeitzRankTwoOuter : Prop := SeitzPlanes fun d p E => ¬ InnerPlane d p E

@[expose] def KFactSeitzRankTwoLow : Prop := SeitzPlanes fun d p _ => RankLE2 p (Cat d)

theorem kFactSeitzRankTwo_iff : KFactSeitzRankTwo ↔ SeitzPlanes fun _ _ _ => True :=
  ⟨fun h d p hp hp2 hpd hex E hE hc _ => h d p hp hp2 hpd hex E hE hc,
    fun h d p hp hp2 hpd hex E hE hc => h d p hp hp2 hpd hex E hE hc trivial⟩

theorem SeitzPlanes.mono {S S' : ∀ d : TauCeti.ValidLieTypeIndex, ℕ →
    Subgroup (MulAut (Cat d)) → Prop} (h : ∀ d p E, S d p E → S' d p E) (hS' : SeitzPlanes S') :
    SeitzPlanes S :=
  fun d p hp hp2 hpd hex E hE hc hs => hS' d p hp hp2 hpd hex E hE hc (h d p E hs)

theorem SeitzPlanes.of_cover {S S₁ S₂ : ∀ d : TauCeti.ValidLieTypeIndex, ℕ →
    Subgroup (MulAut (Cat d)) → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → ∀ E, S d p E → S₁ d p E ∨ S₂ d p E)
    (h₁ : SeitzPlanes S₁) (h₂ : SeitzPlanes S₂) : SeitzPlanes S := by
  intro d p hp hp2 hpd hex E hE hc hs
  rcases hcov d p hp hp2 E hs with h | h
  · exact h₁ d p hp hp2 hpd hex E hE hc h
  · exact h₂ d p hp hp2 hpd hex E hE hc h

theorem _root_.CFSG.AGLEmbeddingD2.KFactSeitzRankTwo.inner (h : KFactSeitzRankTwo) :
    KFactSeitzRankTwoInner :=
  fun d p hp hp2 hpd hex E hE hc _ => h d p hp hp2 hpd hex E hE hc

theorem _root_.CFSG.AGLEmbeddingD2.KFactSeitzRankTwo.outer (h : KFactSeitzRankTwo) :
    KFactSeitzRankTwoOuter :=
  fun d p hp hp2 hpd hex E hE hc _ => h d p hp hp2 hpd hex E hE hc

theorem _root_.CFSG.AGLEmbeddingD2.KFactSeitzRankTwo.low (h : KFactSeitzRankTwo) :
    KFactSeitzRankTwoLow :=
  fun d p hp hp2 hpd hex E hE hc _ => h d p hp hp2 hpd hex E hE hc

theorem kFactSeitzRankTwo_of_inner_outer (hi : KFactSeitzRankTwoInner)
    (ho : KFactSeitzRankTwoOuter) : KFactSeitzRankTwo :=
  kFactSeitzRankTwo_iff.mpr (SeitzPlanes.of_cover
    (fun d p _ _ E _ => by by_cases h : InnerPlane d p E; exacts [Or.inl h, Or.inr h]) hi ho)

theorem kFactSeitzRankTwo_of_p3_p5 (h3 : SeitzPlanes fun _ p _ => p = 3)
    (h5 : SeitzPlanes fun _ p _ => 5 ≤ p) : KFactSeitzRankTwo :=
  kFactSeitzRankTwo_iff.mpr (SeitzPlanes.of_cover
    (fun _ p hp hp2 _ _ => by
      have h2 := hp.two_le
      rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
      · exact Or.inl h
      · subst h
        exact absurd hp (by norm_num)
      · exact Or.inr h) h3 h5)

theorem kFactSeitzRankTwo_of_low_high (hl : KFactSeitzRankTwoLow)
    (hh : SeitzPlanes fun d p _ => ¬ RankLE2 p (Cat d)) : KFactSeitzRankTwo :=
  kFactSeitzRankTwo_iff.mpr (SeitzPlanes.of_cover
    (fun d p _ _ _ _ => by by_cases h : RankLE2 p (Cat d); exacts [Or.inl h, Or.inr h]) hl hh)

theorem RankLE2.of_pRank {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (h : Open.pRank p (⊤ : Subgroup K) ≤ 2) : RankLE2 p K := by
  intro F hF
  have : Fact p.Prime := ⟨hp⟩
  have hFp : IsPGroup p F := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hF.2 g g.2⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hkle : k ≤ Open.pRank p (⊤ : Subgroup K) := by
    refine le_csSup ⟨Nat.card K, ?_⟩ ⟨F, le_top, hF, hk⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card K := Subgroup.card_le_card_group B
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos (hkle.trans h)

theorem RankLE2.of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L) {p : ℕ}
    (h : RankLE2 p K) : RankLE2 p L := by
  intro F hF
  have hF' : IsElemAbelian p (F.map e.symm.toMonoidHom) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF _
  have := h _ hF'
  rwa [Subgroup.card_map_of_injective e.symm.injective] at this

theorem mulAut_congr_conj {K L : Type*} [Group K] [Group L] (e : K ≃* L) (x : K) :
    (MulAut.congr e).toMonoidHom (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply]

theorem InnerPlane.map_congr_conj {d : TauCeti.ValidLieTypeIndex} {K : Type*} [Group K]
    (e : K ≃* Cat d) (E₀ : Subgroup K) (p : ℕ) :
    InnerPlane d p (E₀.map ((MulAut.congr e).toMonoidHom.comp MulAut.conj)) := by
  rintro _ ⟨x, -, rfl⟩
  exact ⟨e x, (mulAut_congr_conj e x).symm⟩

end CFSG.LieType.SeitzGeneration
