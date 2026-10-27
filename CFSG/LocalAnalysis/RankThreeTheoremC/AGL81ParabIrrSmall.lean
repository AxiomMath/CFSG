module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrLin
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSmallU33
import CFSG.LargeExtraspecial.S4TwoH
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiagK
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSmall
import CFSG.Adapters.LinearCatalogStated

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

open CFSG.Open CFSG.AGLEmbedding CFSG.ComponentClassification
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {A : Type} [Group A]

@[expose] noncomputable def quotAutN (Y : Subgroup A) :
    ↥(Subgroup.normalizer (Y : Set A)) →* MulAut (↥Y ⧸ Subgroup.center ↥Y) :=
  (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥Y).comp
    Y.normalizerMonoidHom

theorem centralizes_of_quotAutN_eq_one {Y : Subgroup A} (hY : Open.IsQuasisimple ↥Y)
    {c : ↥(Subgroup.normalizer (Y : Set A))} (h : quotAutN Y c = 1) :
    ∀ y ∈ Y, (c : A) * y = y * c := by
  haveI : Group.IsPerfect ↥Y := Group.isPerfect_def.mpr hY.1
  have hφ : Y.normalizerMonoidHom c = 1 :=
    CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective ↥Y
      (by rw [map_one]; exact h)
  intro y hy
  have h1 := Y.normalizerMonoidHom_apply_apply_coe c ⟨y, hy⟩
  rw [hφ] at h1
  change y = (c : A) * y * (c : A)⁻¹ at h1
  calc (c : A) * y = (c : A) * y * (c : A)⁻¹ * c := by group
    _ = y * c := by rw [← h1]

theorem centralizes_of_card_range_dvd [Finite A] {Y B N : Subgroup A} {p : ℕ} (hp : p.Prime)
    (hY : Open.IsQuasisimple ↥Y) (hBY : B ≤ Subgroup.normalizer (Y : Set A))
    (hNY : N ≤ Subgroup.normalizer (Y : Set A)) (hcyc : ¬ IsCyclic ↥B) (hN : IrredOn N B)
    (hNB : N ≤ Subgroup.normalizer (B : Set A)) (hcard : Nat.card (quotAut hBY).range ∣ p) :
    ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b := by
  have key : ∃ x, ∃ hx : x ∈ B, ∀ b (hb : b ∈ B),
      quotAutN Y ⟨b, hBY hb⟩ ∈ Subgroup.zpowers (quotAutN Y ⟨x, hBY hx⟩) := by
    by_cases h : ∃ x, ∃ hx : x ∈ B, quotAutN Y ⟨x, hBY hx⟩ ≠ 1
    · obtain ⟨x, hx, hx1⟩ := h
      refine ⟨x, hx, fun b hb => ?_⟩
      have hle : Subgroup.zpowers (quotAutN Y ⟨x, hBY hx⟩) ≤ (quotAut hBY).range :=
        (Subgroup.zpowers_le).2 ⟨⟨x, hx⟩, rfl⟩
      have hord : orderOf (quotAutN Y ⟨x, hBY hx⟩) = p := by
        have h1 : orderOf (quotAutN Y ⟨x, hBY hx⟩) ∣ p := by
          rw [← Nat.card_zpowers]
          exact (Subgroup.card_dvd_of_le hle).trans hcard
        rcases (Nat.dvd_prime hp).1 h1 with h | h
        · exact absurd (orderOf_eq_one_iff.1 h) hx1
        · exact h
      have heq : Subgroup.zpowers (quotAutN Y ⟨x, hBY hx⟩) = (quotAut hBY).range :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Nat.card_zpowers, hord]
          exact Nat.le_of_dvd hp.pos hcard)
      rw [heq]
      exact ⟨⟨b, hb⟩, rfl⟩
    · push Not at h
      refine ⟨1, B.one_mem, fun b hb => ?_⟩
      rw [h b hb]
      exact Subgroup.one_mem _
  obtain ⟨x, hx, hgen⟩ := key
  have h1 := forall_eq_one_of_cyclic (ρ := quotAutN Y) hBY hNY hcyc hN hNB hx hgen
  intro b hb y hy
  exact centralizes_of_quotAutN_eq_one hY (h1 b hb) y hy

theorem card_range_dvd_of_not_sq [Finite A] {Y B : Subgroup A} {p : ℕ} (hp : p.Prime)
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) (hB : IsPGroup p ↥B)
    (h2 : ¬ p ^ 2 ∣ Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y))) :
    Nat.card (quotAut hBY).range ∣ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥(quotAut hBY).range :=
    Finite.of_surjective _ (quotAut hBY).rangeRestrict_surjective
  have hS : IsPGroup p ↥(quotAut hBY).range :=
    hB.of_surjective (quotAut hBY).rangeRestrict (quotAut hBY).rangeRestrict_surjective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdvd : p ^ k ∣ Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) :=
    hk ▸ Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra h
    exact h2 ((pow_dvd_pow p (by omega)).trans hdvd)
  rw [hk]
  exact (pow_dvd_pow p hk1).trans (by rw [pow_one])

theorem mem_inner_of_odd_two_pow {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    {j : ℕ} (hA : Nat.card (MulAut X) = 2 ^ j * Nat.card X) {σ : MulAut X}
    (hσ : Odd (orderOf σ)) : σ ∈ OuterAutomorphisms.inner X := by
  have hinj := conj_injective_of_center hZ
  have hI : Nat.card (OuterAutomorphisms.inner X) = Nat.card X := by
    rw [OuterAutomorphisms.inner, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj,
      Subgroup.card_top]
  have hO : Nat.card (OuterAutomorphisms.Outer X) = 2 ^ j := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (OuterAutomorphisms.inner X)
    rw [hI, hA] at h
    have hX : 0 < Nat.card X := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hX h).symm
  set s : OuterAutomorphisms.Outer X := QuotientGroup.mk' (OuterAutomorphisms.inner X) σ with hs
  have hcop : Nat.Coprime (orderOf σ) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hσ)
  have hord : orderOf s = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_map_dvd _ σ) (hO ▸ orderOf_dvd_natCard s)
  rw [orderOf_eq_one_iff, hs, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hord
  exact hord

theorem card_range_dvd_three_of_overgroup96 [Finite A] {Y P B : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (hpar : IsParabolicTwo Y P) (hne : P ≠ Y)
    (hBY : B ≤ Subgroup.normalizer (Y : Set A)) (hBP : B ≤ Subgroup.normalizer (P : Set A))
    (hB : IsPGroup 3 ↥B) {j : ℕ}
    (hA : Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) =
      2 ^ j * Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    (hX2 : 2 ∣ Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    (h96 : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 (↥Y ⧸ Subgroup.center ↥Y)) :
    Nat.card (quotAut hBY).range ∣ 3 := by
  haveI : IsSimpleGroup (↥Y ⧸ Subgroup.center ↥Y) := hY.2
  have hZ : Subgroup.center (↥Y ⧸ Subgroup.center ↥Y) = ⊥ := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥Y hY
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥Y ⧸ Subgroup.center ↥Y)) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm hab
  have hinj := conj_injective_of_center hZ
  have hS : IsPGroup 3 ↥(quotAut hBY).range :=
    hB.of_surjective (quotAut hBY).rangeRestrict (quotAut hBY).rangeRestrict_surjective
  have hin : ∀ b : ↥B, ∃ x, MulAut.conj x = quotAut hBY b := fun b => by
    refine mem_inner_of_odd_two_pow hZ hA ?_
    obtain ⟨k, hk⟩ := hS ⟨_, ⟨b, rfl⟩⟩
    have hdvd : orderOf (quotAut hBY b) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one
      (by simpa using congrArg Subtype.val hk)
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hdvd
  choose x hx using hin
  set D : Subgroup (↥Y ⧸ Subgroup.center ↥Y) :=
    (quotAut hBY).range.comap (MulAut.conj : _ →* MulAut (↥Y ⧸ Subgroup.center ↥Y)) with hDdef
  set Nn := Subgroup.normalizer ((quotSub Y P : Subgroup (↥Y ⧸ Subgroup.center ↥Y)) :
    Set (↥Y ⧸ Subgroup.center ↥Y)) with hNdef
  have hDN : D ≤ Nn := by
    intro y hy
    obtain ⟨b, hb⟩ := hy
    have hle := quotAut_map_le hBY hBP b
    rw [hb] at hle
    have heq : (quotSub Y P).map (MulAut.conj y).toMonoidHom = quotSub Y P :=
      Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj y).injective).ge
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ⟨h, hh, rfl⟩
    · intro hh
      rw [← heq] at hh
      obtain ⟨h', hh', hhh⟩ := hh
      have : h' = h := (MulAut.conj y).injective hhh
      exact this ▸ hh'
  obtain ⟨T, hT, hTP⟩ := exists_sylow_le_quotSub hpar
  have hNtop : Nn ≠ ⊤ := by
    intro hN
    haveI hnorm : (quotSub Y P).Normal := Subgroup.normalizer_eq_top_iff.mp hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (quotSub Y P) with h | h
    · apply hT.2.2
      have hTb : T = ⊥ := le_bot_iff.mp (h ▸ hTP)
      rw [hTb, show ((⊥ : Subgroup (↥Y ⧸ Subgroup.center ↥Y)).subgroupOf ⊤).index =
        (⊥ : Subgroup (↥Y ⧸ Subgroup.center ↥Y)).index from Subgroup.relIndex_top_right _,
        Subgroup.index_bot]
      exact hX2
    · exact quotSub_ne_top hpar hne h
  have hN96 : Nat.card Nn ∣ 96 := h96 T Nn hT (hTP.trans Subgroup.le_normalizer) hNtop
  have hD3 : IsPGroup 3 ↥D := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := hS ⟨_, hy⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    simpa using congrArg Subtype.val hk
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hD3
  have hDdvd : 3 ^ k ∣ 96 := hk ▸ (Subgroup.card_dvd_of_le hDN).trans hN96
  have hk1 : k ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ∣ 96 := (pow_dvd_pow 3 (by omega)).trans hDdvd
    norm_num at this
  have hrange : (quotAut hBY).range =
      D.map (MulAut.conj : _ →* MulAut (↥Y ⧸ Subgroup.center ↥Y)) := by
    ext σ
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨x b, ⟨b, (hx b).symm⟩, hx b⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  rw [hrange, Subgroup.card_map_of_injective hinj, hk]
  exact (pow_dvd_pow 3 hk1).trans (by norm_num)

theorem sq_dvd_of_sq_dvd_two_pow_mul {p k m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ^ 2 ∣ 2 ^ k * m) : p ^ 2 ∣ m :=
  (Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)).dvd_of_dvd_mul_left h

theorem not_sq_dvd_small {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : m = 15 ∨ m = 21 ∨ ((m = 45 ∨ m = 315 ∨ m = 189) ∧ p ≠ 3)) : ¬ p ^ 2 ∣ m := by
  intro h
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hm0 : 0 < m := by rcases hm with rfl | rfl | ⟨rfl | rfl | rfl, -⟩ <;> norm_num
  have hle : p ^ 2 ≤ m := Nat.le_of_dvd hm0 h
  have hp17 : p ≤ 17 := by
    by_contra hc
    have : 18 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rcases hm with rfl | rfl | ⟨rfl | rfl | rfl, -⟩ <;> omega
  rcases hm with rfl | rfl | ⟨rfl | rfl | rfl, h3⟩ <;> interval_cases p <;>
    first | exact absurd h (by decide) | exact absurd rfl h3

theorem nonempty_mulEquiv_projectiveSL_of_alt8 {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 8)) : Nonempty (X ≃* projectiveSL 4 (GaloisField 2 1)) := by
  obtain ⟨e₁⟩ := CFSG.LargeExtraspecial.S4.nonempty_mulEquiv_psl_of_alternating_eight e
  have := Fintype.ofFinite (GaloisField 2 1)
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num), pow_one]
  exact ⟨((e₁.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod 2)).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 (ZMod 2))).trans
      (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard))⟩

theorem parabIrrOn_alternating
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ParabIrrOn fun X _ => ∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧
      Nonempty (X ≃* alternatingGroup (Fin n)) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  left
  obtain ⟨n, hn, ⟨e⟩⟩ := hF
  have hcardAut := Nat.card_congr (MulAut.congr e).toEquiv
  rcases hn with rfl | rfl | rfl
  · refine centralizes_of_card_range_dvd hp hY hBY hNY hcyc hirr hNB
      (card_range_dvd_of_not_sq hp hBY hB ?_)
    rw [hcardAut, card_mulAut_alternatingGroup (Or.inl rfl),
      show Nat.factorial 5 = 2 ^ 3 * 15 by decide]
    exact fun h => not_sq_dvd_small hp hp2 (Or.inl rfl) (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)
  · by_cases hp3 : p = 3
    · subst hp3
      have hXc : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 360 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      obtain ⟨j, hj⟩ : ∃ j, Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) =
          2 ^ j * Nat.card (↥Y ⧸ Subgroup.center ↥Y) := by
        rw [hcardAut, hXc]
        rcases CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.card_mulAut_six with h | h
        · exact ⟨1, by rw [h]; norm_num⟩
        · exact ⟨2, by rw [h]; norm_num⟩
      exact centralizes_of_card_range_dvd Nat.prime_three hY hBY hNY hcyc hirr hNB
        (card_range_dvd_three_of_overgroup96 hY hpar hne hBY hBP hB hj (by rw [hXc]; norm_num)
          (CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96.of_mulEquiv e.symm
            CFSG.HardMathSupport.Curtis.Proving.ordBound_alt_six))
    · refine centralizes_of_card_range_dvd hp hY hBY hNY hcyc hirr hNB
        (card_range_dvd_of_not_sq hp hBY hB ?_)
      rw [hcardAut]
      rcases CFSG.RankThree.PartTwo.Sec15.Proof15Res8Diag.card_mulAut_six with h | h <;> rw [h]
      · rw [show (720 : ℕ) = 2 ^ 4 * 45 by norm_num]
        exact fun h => not_sq_dvd_small hp hp2 (Or.inr (Or.inr ⟨Or.inl rfl, hp3⟩))
          (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)
      · rw [show (1440 : ℕ) = 2 ^ 5 * 45 by norm_num]
        exact fun h => not_sq_dvd_small hp hp2 (Or.inr (Or.inr ⟨Or.inl rfl, hp3⟩))
          (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)
  · by_cases hp3 : p = 3
    · obtain ⟨e₈⟩ := nonempty_mulEquiv_projectiveSL_of_alt8 e
      exact parabIrr_of_projectiveSL hGA hp hp2 hY h2 (by norm_num) le_rfl e₈ hpar hne hna hB hcyc
        hBY hBP hW hNY hNP hNB hirr
    · refine centralizes_of_card_range_dvd hp hY hBY hNY hcyc hirr hNB
        (card_range_dvd_of_not_sq hp hBY hB ?_)
      rw [hcardAut, card_mulAut_alternatingGroup (Or.inr (by norm_num : 7 ≤ 8)),
        show Nat.factorial 8 = 2 ^ 7 * 315 by decide]
      exact fun h => not_sq_dvd_small hp hp2 (Or.inr (Or.inr ⟨Or.inr (Or.inl rfl), hp3⟩))
        (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)

theorem parabIrrOn_psl27 :
    ParabIrrOn fun X _ => ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  left
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := hF
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_seven hq
  have h := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
  rw [hpq, hf] at h
  obtain ⟨e₇⟩ := CFSG.GH74.KGroups.L27.equiv_of_lieModel (Or.inl ⟨by decide, h⟩)
  refine centralizes_of_card_range_dvd hp hY hBY hNY hcyc hirr hNB
    (card_range_dvd_of_not_sq hp hBY hB ?_)
  rw [CFSG.GH74.KGroups.L27.card_mulAut e₇, show (336 : ℕ) = 2 ^ 4 * 21 by norm_num]
  exact fun h => not_sq_dvd_small hp hp2 (Or.inr (Or.inl rfl))
    (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)

theorem parabIrrOn_psu33 :
    ParabIrrOn fun X _ => ∃ d : TauCeti.ValidLieTypeIndex,
      (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q) ∧
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  intro A _ _ Y P B N p hp hp2 hY h2 hF hpar hne hna hB hcyc hBY hBP hW hNY hNP hNB hirr
  left
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨e⟩⟩ := hF
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  obtain ⟨hpq, hf⟩ := CFSG.AGLEmbedding.ParabHub.primePower_eq_of_card_eq Nat.prime_three hq
  have hM := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  rw [hpq, hf] at hM
  obtain ⟨eU⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel (Or.inl ⟨by decide, hM⟩)
  have hAut : Nat.card (MulAut (↥Y ⧸ Subgroup.center ↥Y)) = 12096 :=
    CFSG.GH74.KGroups.U33.card_mulAut eU
  have hXc : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 6048 := by
    rw [Nat.card_congr eU.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
      CFSG.GH74.KGroups.U33.QP_valid.2]
  by_cases hp3 : p = 3
  · subst hp3
    exact centralizes_of_card_range_dvd Nat.prime_three hY hBY hNY hcyc hirr hNB
      (card_range_dvd_three_of_overgroup96 hY hpar hne hBY hBP hB (j := 1)
        (by rw [hAut, hXc]; norm_num) (by rw [hXc]; norm_num)
        (CFSG.HardMathSupport.Curtis.Proving.ordBound_psu_three_three hM))
  · refine centralizes_of_card_range_dvd hp hY hBY hNY hcyc hirr hNB
      (card_range_dvd_of_not_sq hp hBY hB ?_)
    rw [hAut, show (12096 : ℕ) = 2 ^ 6 * 189 by norm_num]
    exact fun h => not_sq_dvd_small hp hp2 (Or.inr (Or.inr ⟨Or.inr (Or.inr rfl), hp3⟩))
      (sq_dvd_of_sq_dvd_two_pow_mul hp hp2 h)

theorem parabIrrOn_small
    (hGA : CFSG.Open.GriessAllModelsStatement) : ParabIrrOn IsSmallTwoOrG2 := by
  refine ParabIrrOn.mono (parabIrrOn_or (parabIrrOn_alternating hGA)
    (parabIrrOn_or parabIrrOn_psl27 parabIrrOn_psu33)) ?_
  rintro X _ (h | ⟨d, h7 | h3, e⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨d, h7, e⟩)
  · exact Or.inr (Or.inr ⟨d, h3, e⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr
