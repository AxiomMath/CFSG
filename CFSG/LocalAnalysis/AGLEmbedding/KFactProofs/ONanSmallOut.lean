module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData
public import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutPCard
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def AutPInner (p : ℕ) (K : Type) [Group K] : Prop :=
  ∀ f : MulAut K, (∃ n : ℕ, f ^ p ^ n = 1) → f ∈ (MulAut.conj : K →* MulAut K).range

variable {K : Type} [Group K] [Finite K] {p : ℕ}

omit [Finite K] in
theorem autPInner_of_not_dvd_outer (hp : p.Prime) (hout : ¬ p ∣ Nat.card (Outer K)) :
    AutPInner p K := by
  rintro f ⟨n, hf⟩
  set o : Outer K := QuotientGroup.mk f with ho
  have ho' : o ^ p ^ n = 1 := by rw [ho, ← QuotientGroup.mk_pow, hf, QuotientGroup.mk_one]
  have h1 : orderOf o ∣ p ^ n := orderOf_dvd_of_pow_eq_one ho'
  have h2 : orderOf o ∣ Nat.card (Outer K) := orderOf_dvd_natCard o
  have hcop : Nat.Coprime (p ^ n) (Nat.card (Outer K)) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hout)
  have h3 : orderOf o = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
  exact (QuotientGroup.eq_one_iff (N := inner K) f).1 (orderOf_eq_one_iff.1 h3)

omit [Finite K] in
theorem autPInner_of_equiv {H : Type} [Group H] (hp : p.Prime) (e : K ≃* H)
    (hH : ¬ p ∣ Nat.card (Outer H)) : AutPInner p K := by
  refine autPInner_of_not_dvd_outer hp ?_
  rwa [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]

omit [Finite K] in
theorem autPInner_of_pInner (hin : ∀ Y : Subgroup (MulAut K), IsPGroup p Y →
    Y ≤ (MulAut.conj : K →* MulAut K).range) : AutPInner p K := by
  rintro f ⟨n, hf⟩
  have hY : IsPGroup p (Subgroup.zpowers f) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hf, one_zpow]
  exact hin (Subgroup.zpowers f) hY (Subgroup.mem_zpowers f)

theorem autPInner_of_isSmallLinTwo (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallLinTwo p K) :
    AutPInner p K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  have hq : 4 ≤ p ^ 2 := by
    have h2 := hp.two_le
    have : 3 ≤ p := by omega
    nlinarith
  exact autPInner_of_not_dvd_outer hp
    (CFSG.AGLEmbeddingD2.not_dvd_card_outer_of_linTwo hp2 (by norm_num) (by norm_num) hq
      (e.trans e₂))

omit [Finite K] in
theorem autPInner_of_isAltTwoP (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsAltTwoP p K) :
    AutPInner p K := by
  obtain ⟨e⟩ := hK
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  exact autPInner_of_equiv hp e (not_dvd_card_outer_alternatingGroup (2 * p) (by omega) p hp hp2)

theorem autPInner_of_isSmallUnitary (hp : p.Prime) (hp2 : p ≠ 2) (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) (hK : IsSmallUnitary p K) : AutPInner p K := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨T⟩ : Nonempty (Sylow p K) := inferInstance
  have hcard : Nat.card T = p ^ 3 := (sylowCube_of_isSmallUnitary hp hp2 hK T).1
  obtain ⟨d, ⟨q, hqp, hqe, hd⟩, ⟨e⟩⟩ := hK
  have hfe : d.1.fieldExponent = 1 := by
    rw [hd]
    simpa using hqe
  refine autPInner_of_pInner (pInner_of_card_dvd hp T
    (center_eq_bot_of_isSimpleGroup_nonabelian hnab) 1 (by simpa using hp.one_lt.ne') ?_)
  intro S hS
  have h := kFactUnitaryAutPCard K p d hp2 ⟨q, hqp, hd⟩ ⟨e⟩ S hS
  rw [hfe] at h
  simpa [hcard] using h

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
