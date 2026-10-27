module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.ClassicalInvolution.Orders.Classical
import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Catalog
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.Timmesfeld.Orders.Classical
import CFSG.Timmesfeld.Orders.Exceptional
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

theorem card_catGroup_linTwo {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex} (hn : n ≠ 0) (hd : IsLinTwoIndex p n d) :
    Nat.card (CatGroup d) = p ^ n * (((p ^ n) ^ 2 - 1) / 2) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.SectionRank.OddCover.card_psl_two Fact.out hp2 (GaloisField.card p n hn)

theorem card_catGroup_twistedA {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (h : d.1 = .twistedA r q) : Nat.card (CatGroup d) = ordTwistedA r (q.p ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedA r q := h
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv
    (MulEquiv.refl (CatGroup ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩))
  rcases eq_or_ne q.p 2 with hp2 | hp2
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two (f := q.exponent)
      (by rwa [hp2] at hm)).2.1 rfl
    rw [Nat.add_sub_cancel] at this
    rw [this, hp2]
  · have := (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hm).2.1 rfl
    rwa [Nat.add_sub_cancel] at this

theorem prod_toNat_icc_two_three (q : ℕ) (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat = (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h2 : Finset.Icc 2 3 = {2, 3} := by decide
  have h₂ : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      push_cast [Nat.cast_sub this]
      ring
    rw [this, Int.toNat_natCast]
  have h₃ : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [h2, Finset.prod_pair (by norm_num), h₂, h₃]

theorem pow_dvd_ordTwistedA_two (q : ℕ) (hq : 1 ≤ q) : q ^ 3 ∣ ordTwistedA 2 q := by
  unfold ordTwistedA
  rw [show 2 * (2 + 1) / 2 = 3 by norm_num, prod_toNat_icc_two_three q hq]
  have hg : Nat.gcd (2 + 1) (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    refine (Nat.gcd_dvd_right _ _).trans ?_
    refine Dvd.dvd.mul_right ?_ _
    obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact ⟨k, by
      have h : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
      omega⟩
  rw [Nat.mul_div_assoc _ hg]
  exact Dvd.intro _ rfl

theorem pow_dvd_card_catGroup_unitary {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) : p ^ (3 * d.1.fieldExponent) ∣ Nat.card (CatGroup d) := by
  obtain ⟨q, rfl, hdq⟩ := hd
  have hfe : d.1.fieldExponent = q.exponent := by rw [hdq]; simp
  rw [hfe, card_catGroup_twistedA hdq, mul_comm, pow_mul]
  exact pow_dvd_ordTwistedA_two _ (Nat.one_le_pow _ _ q.prime_p.pos)

theorem card_catGroup_B2 {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (h : d.1 = .B 2 q) : Nat.card (CatGroup d) = ordBC 2 (q.p ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B 2 q := h
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv
    (MulEquiv.refl (CatGroup ⟨TauCeti.LieTypeIndex.B 2 q, hv⟩))
  rcases eq_or_ne q.p 2 with hp2 | hp2
  · have := (CFSG.Timmesfeld.card_statedClassicalModel_two (f := q.exponent)
      (by rwa [hp2] at hm)).2.2.1 rfl
    rw [this, hp2]
  · exact (CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two hp2 hm).2.2.1 rfl

theorem card_catGroup_B_even {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hr : 3 ≤ r) (hq : q.p = 2) (h : d.1 = .B r q) :
    Nat.card (CatGroup d) = ordBC r (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.B r q := h
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq hr
    (MulEquiv.refl (CatGroup ⟨TauCeti.LieTypeIndex.B r q, hv⟩))
  rw [hq] at hm
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl

theorem card_catGroup_D_even {d : TauCeti.ValidLieTypeIndex} {r : ℕ} {q : TauCeti.PrimePower}
    (hq : q.p = 2) (h : d.1 = .D r q) : Nat.card (CatGroup d) = ordD r (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.D r q := h
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq
    (MulEquiv.refl (CatGroup ⟨TauCeti.LieTypeIndex.D r q, hv⟩))
  rw [hq] at hm
  exact (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.2.1 rfl

theorem card_catGroup_F4_even
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h : d.1 = .F4 q) : Nat.card (CatGroup d) = ordF4 (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.F4 q := h
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (CatGroup ⟨TauCeti.LieTypeIndex.F4 q, hv⟩)
      .F4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hq (MulEquiv.refl _)⟩
  rw [hq] at hm
  exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm

theorem card_catGroup_E6_even
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h : d.1 = .E6 q) : Nat.card (CatGroup d) = ordE6 (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.E6 q := h
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (CatGroup ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)
      .E6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.e6 q hv hq (MulEquiv.refl _)⟩
  rw [hq] at hm
  exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm

theorem card_catGroup_G2_even
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h : d.1 = .G2 q) : Nat.card (CatGroup d) = ordG2 (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.G2 q := h
  have h3 : 3 ≤ q.p ^ q.exponent := by
    have h := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def] using h
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel (CatGroup ⟨TauCeti.LieTypeIndex.G2 q, hv⟩)
      .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, h3⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hq (MulEquiv.refl _)⟩
  rw [hq] at hm
  exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm

theorem card_catGroup_trialityD4_even
    {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.p = 2)
    (h : d.1 = .trialityD4 q) : Nat.card (CatGroup d) = ordTrialityD4 (2 ^ q.exponent) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.trialityD4 q := h
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel
      (CatGroup ⟨TauCeti.LieTypeIndex.trialityD4 q, hv⟩) .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hq (by decide)
        (MulEquiv.refl _)⟩
  rw [hq] at hm
  exact CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hm

theorem card_of_reeTitsModel_twistedF4_exact
    {G : Type} [Group G] {f : ℕ} (h : CFSG.Blueprint.ReeTitsModel G .twistedF4 2 f) :
    Nat.card G = ordTwistedF4 (2 ^ f) := by
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier G 2 f h
  obtain ⟨hadm, a, hfa, hmodel⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hmodel
  have : Fintype K := Fintype.ofFinite K
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨E⟩ := hS.2.2.2.2.2 a K hfa hK ⟨e⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hord :=
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK').1
  rw [Nat.card_congr E.toEquiv, hord, ordTwistedF4, hfa]
  set q := 2 ^ (2 * a + 1) with hq
  have h1 : 1 ≤ q := Nat.one_le_two_pow
  have h2 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h3 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3, h4]
  ring

theorem reeTitsModel_of_catGroup_reeF4
    {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (h : d.1 = .reeF4 m) :
    CFSG.Blueprint.ReeTitsModel (CatGroup d) .twistedF4 2 (2 * m + 1) := by
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.reeF4 m := h
  have hfin : ∀ d : TauCeti.ReeF4LieIndex, Finite d.1.fixedField := fun _ => inferInstance
  have hchar : ∀ d : TauCeti.ReeF4LieIndex, CharP d.1.fixedField 2 := fun _ => inferInstance
  have := hfin (TauCeti.ReeF4LieIndex.of m hv)
  have := hchar (TauCeti.ReeF4LieIndex.of m hv)
  have hm : 1 ≤ m := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hhalf : (TauCeti.ReeF4LieIndex.of m hv).toSuzukiReeIndex.halfExponent = m :=
    TauCeti.SuzukiReeIndex.halfExponent_reeF4 m hv
  obtain ⟨e₁⟩ := CFSG.TauCetiBridge.ReeF4.nonempty_candidate_equiv_reeF4
    (TauCeti.ReeF4LieIndex.of m hv)
  rw [hhalf] at e₁
  have hK := CFSG.TauCetiBridge.ReeF4.card_fixedField_reeF4 (TauCeti.ReeF4LieIndex.of m hv)
  rw [hhalf] at hK
  exact ⟨⟨Nat.prime_two, by omega, rfl, rfl, ⟨m, rfl⟩, by omega⟩, m, rfl,
    (TauCeti.ReeF4LieIndex.of m hv).1.fixedField, inferInstance, inferInstance, hK,
    ⟨e₁.trans (CFSG.TauCetiBridge.ReeF4.nativeModelEquiv m).symm⟩⟩

theorem card_catGroup_reeF4
    {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (h : d.1 = .reeF4 m) :
    Nat.card (CatGroup d) = ordTwistedF4 (2 ^ (2 * m + 1)) :=
  card_of_reeTitsModel_twistedF4_exact (reeTitsModel_of_catGroup_reeF4 h)

theorem isSimpleGroup_of_catGroup_reeF4
    {d : TauCeti.ValidLieTypeIndex} {m : ℕ} (h : d.1 = .reeF4 m) :
    IsSimpleGroup (CatGroup d) :=
  (CFSG.LieType.Simplicity.fam_ree_tits_simplicity (CatGroup d) .twistedF4 2 (2 * m + 1)
    (reeTitsModel_of_catGroup_reeF4 h)).2

end CFSG.AGLEmbedding
