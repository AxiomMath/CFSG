module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.CentralExtRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Tables112Spor

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open

theorem pRank_centerQuotient_le_of_center {L : Type} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpZ : p ∣ Nat.card (Subgroup.center L))
    (hp2Z : ¬ p ^ 2 ∣ Nat.card (Subgroup.center L)) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ Subgroup.center L)) / 2 + 1 ≤
      CFSG.Open.pRank p (⊤ : Subgroup L) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) p hpZ
  set Z₃ : Subgroup L := Subgroup.zpowers (z : L) with hZ₃
  have hZ₃c : Z₃ ≤ Subgroup.center L := Subgroup.zpowers_le.mpr z.2
  have : Z₃.Normal := Subgroup.normal_of_le_center hZ₃c
  have hZ₃card : Nat.card Z₃ = p := by
    rw [hZ₃, Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  set N : Subgroup (L ⧸ Z₃) := (Subgroup.center L).map (QuotientGroup.mk' Z₃) with hN
  let f : Subgroup.center L →* L ⧸ Z₃ := (QuotientGroup.mk' Z₃).comp (Subgroup.center L).subtype
  have hfker : f.ker = Z₃.subgroupOf (Subgroup.center L) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp [f, QuotientGroup.eq_one_iff]
  have hfrange : f.range = N := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hNcard : p * Nat.card N = Nat.card (Subgroup.center L) := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hfrange] at h
    rw [← h, ← hZ₃card]
    congr 1
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ₃c).toEquiv).symm
  have hNp : ¬ p ∣ Nat.card N := fun h =>
    hp2Z (by rw [← hNcard, pow_two]; exact Nat.mul_dvd_mul_left p h)
  have hNn : N.Normal := Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z₃)
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := p) N hNp
  have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) hp.one_lt
    (QuotientGroup.quotientQuotientEquivQuotient Z₃ (Subgroup.center L) hZ₃c)
  rw [← h2, h1]
  exact pRank_quotient_le_of_central hp hp2 Z₃ hZ₃c hZ₃card

theorem eq_of_three_dvd_sporadicMultiplierOrder {s : TauCeti.SporadicName}
    (h : 3 ∣ Tables.Multiplier.sporadicMultiplierOrder s) :
    s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime := by
  cases s <;> simp_all [Tables.Multiplier.sporadicMultiplierOrder]

theorem card_center_dvd_sporadicMultiplierOrder (hSpM : Tables.Multiplier.SporadicMultipliers)
    {K : Type} [Group K] [Finite K] (hq : CFSG.Open.IsQuasisimple K) (s : TauCeti.SporadicName)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    Nat.card (Subgroup.center K) ∣ Tables.Multiplier.sporadicMultiplierOrder s := by
  have hq' : CFSG.IsQuasisimple K :=
    ⟨⟨hq.1⟩, hq.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian
      K hq⟩
  have hdvd := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq' e
  rwa [hSpM.1 s] at hdvd

@[expose] def SporadicThreeRankLe (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ r

@[expose] def SporadicThreeRankGe (s : TauCeti.SporadicName) (r : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S)

@[expose] def SporadicBigCoverRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L → ∀ s : TauCeti.SporadicName,
    (s = .McL ∨ s = .Suz ∨ s = .Fi22 ∨ s = .Fi24Prime) →
    Nonempty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    3 ∣ Nat.card (Subgroup.center L) →
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup L) + 1

@[expose] def J3CoverRank : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    Nonempty (L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) →
    Nat.card (Subgroup.center L) = 3 → 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L)

theorem sporadicCoverRank_of_data (hSpM : Tables.Multiplier.SporadicMultipliers)
    (hM22 : SporadicThreeRankLe .M22 4) (hJ3 : SporadicThreeRankLe .J3 4)
    (hON : SporadicThreeRankLe .ONan 4) (hBig : SporadicBigCoverRank) : SporadicCoverRank := by
  intro L _ _ hq hF p hp hp2 hpZ
  obtain ⟨s, ⟨e⟩⟩ := hF
  have h12 := card_center_dvd_twelve_of_spor hSpM hq ⟨s, ⟨e⟩⟩
  obtain ⟨rfl, h9⟩ := eq_three_of_dvd_of_dvd_twelve h12 hp hp2 hpZ
  have hs := eq_of_three_dvd_sporadicMultiplierOrder
    (hpZ.trans (card_center_dvd_sporadicMultiplierOrder hSpM hq s e))
  have hle := pRank_centerQuotient_le_of_center hp hp2 hpZ (by norm_num; exact h9)
  have hsmall : ∀ r, CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 4 →
      r = CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) →
      CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup L) + 1 := by
    intro r h4 _
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hsmall _ (hM22 _ ⟨e⟩) rfl
  · exact hsmall _ (hJ3 _ ⟨e⟩) rfl
  · exact hBig L hq _ (Or.inl rfl) ⟨e⟩ hpZ
  · exact hBig L hq _ (Or.inr (Or.inl rfl)) ⟨e⟩ hpZ
  · exact hsmall _ (hON _ ⟨e⟩) rfl
  · exact hBig L hq _ (Or.inr (Or.inr (Or.inl rfl))) ⟨e⟩ hpZ
  · exact hBig L hq _ (Or.inr (Or.inr (Or.inr rfl))) ⟨e⟩ hpZ

theorem sporadicCoverRankTwo_of_data (hSpM : Tables.Multiplier.SporadicMultipliers)
    (hM22 : SporadicThreeRankLe .M22 2) (hJ3 : J3CoverRank) (hMcL : SporadicThreeRankGe .McL 4)
    (hON : SporadicThreeRankGe .ONan 4) (hSuz : SporadicThreeRankGe .Suz 4)
    (hFi22 : SporadicThreeRankGe .Fi22 4) (hFi24 : SporadicThreeRankGe .Fi24Prime 4) :
    SporadicCoverRankTwo := by
  intro L _ _ hq hF hZ3 hL2
  obtain ⟨s, ⟨e⟩⟩ := hF
  have h3Z : 3 ∣ Nat.card (Subgroup.center L) := by rw [hZ3]
  have hs := eq_of_three_dvd_sporadicMultiplierOrder
    (h3Z.trans (card_center_dvd_sporadicMultiplierOrder hSpM hq s e))
  have hle := pRank_quotient_le_of_central Nat.prime_three (by norm_num) (Subgroup.center L)
    le_rfl hZ3
  rw [hL2] at hle
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hM22 _ ⟨e⟩
  · have := hJ3 L hq ⟨e⟩ hZ3
    omega
  · have := hMcL _ ⟨e⟩
    omega
  · have := hSuz _ ⟨e⟩
    omega
  · have := hON _ ⟨e⟩
    omega
  · have := hFi22 _ ⟨e⟩
    omega
  · have := hFi24 _ ⟨e⟩
    omega

end CFSG.HardMathSupport.Timmesfeld.Coordinator
