module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFacts
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open TauCeti CFSG.Assembly.LowTwoRank CFSG.Yardstones.Md0ec50421ce4
  CFSG.Adapters.RankTwoModelTransports
open CFSG.ComponentClassification.PresentationLocal (sympFour isSimpleGroup_commutator_sympFour
  isPerfect_commutator_sympFour commutatorEquivAlternating)
open CFSG.RankThree.PartOne.KCSpComm (statedProjEquivSympFour)
open CFSG.Monster.Existence.Compat (statedScalars_eq_bot statedProjEquivOfBot)

private theorem lt_order_sp (q m : ℕ) (hq : 2 ≤ q) (hm : 2 ≤ m) (h : (m, q) ≠ (2, 2)) :
    720 < q ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1) := by
  have hmem : 1 ∈ Finset.Icc 1 m := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hpos : 0 < ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1) := by
    refine Finset.prod_pos fun j hj => ?_
    have hj1 := (Finset.mem_Icc.1 hj).1
    have : 1 < q ^ (2 * j) := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hprod : q ^ 2 - 1 ≤ ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1) := by
    have := Finset.dvd_prod_of_mem (fun j => q ^ (2 * j) - 1) hmem
    simpa using Nat.le_of_dvd hpos this
  have hq2 : 4 ≤ q ^ 2 := by nlinarith
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · obtain rfl : m = 2 := by omega
    have hq3 : 3 ≤ q := by
      by_contra hcon
      exact h (by rw [show q = 2 by omega])
    have hq4 : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq3 4
    have hq22 : 9 ≤ q ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hIcc, Finset.prod_pair (by norm_num)]
    have h1 : 8 ≤ q ^ (2 * 1) - 1 := by simp; omega
    have h2 : 80 ≤ q ^ (2 * 2) - 1 := by simp; omega
    calc 720 < 81 * (8 * 80) := by norm_num
      _ ≤ q ^ (2 ^ 2) * ((q ^ (2 * 1) - 1) * (q ^ (2 * 2) - 1)) := by
        apply Nat.mul_le_mul (by simpa using hq4) (Nat.mul_le_mul h1 h2)
  · have h9 : 9 ≤ m ^ 2 := by nlinarith
    have : 2 ^ 9 ≤ q ^ (m ^ 2) :=
      (Nat.pow_le_pow_left hq 9).trans (Nat.pow_le_pow_right (by omega) h9)
    calc 720 < 2 ^ 9 * 3 := by norm_num
      _ ≤ q ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (q ^ (2 * j) - 1) :=
        Nat.mul_le_mul this (by omega)

theorem spAltSixFacts_holds : SpAltSixFacts := by
  intro E _ _ m hm hne
  refine ⟨fun e => ?_⟩
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have hne' : (m, Nat.card E) ≠ (2, 2) := by rwa [Nat.card_eq_fintype_card]
  have h360 : Nat.card (StatedProj (StatedSp m E)) = 360 := by
    rw [← Nat.card_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m E).toEquiv,
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  have hlt := lt_order_sp (Nat.card E) m hq hm hne'
  by_cases h2 : ringChar E = 2
  · haveI : CharP E 2 := h2 ▸ ringChar.charP E
    have := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := E) m
    omega
  · have := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := E) (n := m)
      (Ring.two_ne_zero h2) (by omega)
    omega

private theorem isChevSimple_of_carrier {E : Type} [Field E] [Fintype E] (r : ℕ)
    (d : ValidLieTypeIndex) (hch : d.characteristic = ringChar E)
    (hK : Fintype.card E = d.fieldOrder)
    (eT : d.Group ≃* StatedProj (StatedSp r ↥d.fixedField)) :
    IsChevSimple (ringChar E) (StatedProj (StatedSp r E)) := by
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  let _ : Fintype d.fixedField := Fintype.ofFinite _
  have hcard : Fintype.card E = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card (α := d.fixedField), ValidLieTypeIndex.card_fixedField]
    exact hK
  let φ : E ≃+* d.fixedField := FiniteField.ringEquivOfCardEq hcard
  exact Or.inl ⟨.lie d, hch, ⟨(statedProjCongr (glCongr φ) (glCongr_statedSp φ r)
    (glCongr_statedScalars φ)).trans eT.symm⟩⟩

private theorem isChevSimple_three_psp_two_three {E : Type} [Field E] [Fintype E]
    (h3 : Fintype.card E = 3) : IsChevSimple 3 (StatedProj (StatedSp 2 E)) := by
  let q : PrimePower := ⟨2, 1, Nat.prime_two, one_pos⟩
  have hv : (LieTypeIndex.twistedA 3 q).Valid := by
    rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
      LieTypeIndex.isDuplicateRepresentative_iff]
    simp [q, PrimePower.card_def]
  have hcE : Fintype.card E = Fintype.card (ZMod 3) := by rw [h3, ZMod.card]
  let φ : E ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcE
  let e1 := statedProjCongr (glCongr φ) (glCongr_statedSp φ 2) (glCongr_statedScalars φ)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eT := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv
  exact Or.inr ⟨.lie ⟨_, hv⟩, ⟨by simp [q, PrimePower.card_def], rfl⟩,
    ⟨((e1.trans CFSG.GH74.Exceptional.psp43EquivU2).trans
      CFSG.GH74.Exceptional.u2FourEquiv).trans eT.symm⟩⟩

private theorem isChevSimple_statedProj_sp {E : Type} [Field E] [Fintype E] (m : ℕ) (hm : 2 ≤ m)
    (hne : (m, Fintype.card E) ≠ (2, 2)) :
    IsChevSimple (ringChar E) (StatedProj (StatedSp m E)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card E (ringChar E)
  have hn : 0 < (n : ℕ) := n.pos
  let q : PrimePower := ⟨ringChar E, n, hp, hn⟩
  have hqc : q.card = Fintype.card E := by rw [hcard, PrimePower.card_def]
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | hm3
  · by_cases h3 : Fintype.card E = 3
    · have hch : ringChar E = 3 := by
        have hdvd : ringChar E ∣ 3 := h3 ▸ hcard ▸ dvd_pow_self _ hn.ne'
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
      rw [hch]
      exact isChevSimple_three_psp_two_three h3
    · have h22 : Fintype.card E ≠ 2 := fun h => hne (by rw [h])
      have hv : (LieTypeIndex.B 2 q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨⟨le_rfl, fun h => h22 (hqc.symm.trans h.2)⟩, fun h => h3 (hqc.symm.trans h.2)⟩
      exact isChevSimple_of_carrier 2 ⟨.B 2 q, hv⟩ (LieTypeIndex.characteristic_B 2 q)
        (by rw [← hqc]; simp [ValidLieTypeIndex.fieldOrder])
        (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
  · by_cases h2 : ringChar E = 2
    · have hv : (LieTypeIndex.B m q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
      exact isChevSimple_of_carrier m ⟨.B m q, hv⟩ (LieTypeIndex.characteristic_B m q)
        (by rw [← hqc]; simp [ValidLieTypeIndex.fieldOrder])
        (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj m q hv h2 hm3)
    · have hv : (LieTypeIndex.C m q).Valid := by
        rw [LieTypeIndex.valid_iff, LieTypeIndex.inStandardRange_iff,
          LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨⟨hm3, h2⟩, not_false⟩
      exact isChevSimple_of_carrier m ⟨.C m q, hv⟩ (LieTypeIndex.characteristic_C m q)
        (by rw [← hqc]; simp [ValidLieTypeIndex.fieldOrder])
        (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj m q hv)

theorem spFactorFacts_holds : SpFactorFacts := by
  intro E _ _ m hm hne
  have hq : 2 ≤ Nat.card E := Nat.succ_le_of_lt Finite.one_lt_card
  have hne' : ¬ (m = 2 ∧ Nat.card E = 2) := fun h =>
    hne (by rw [h.1, ← Nat.card_eq_fintype_card, h.2])
  have hF : (Infinite E ∨ 4 ≤ Nat.card E) ∨ (Nat.card E = 3 ∧ 2 ≤ m) ∨
      (Nat.card E = 2 ∧ 3 ≤ m) := by
    rcases Nat.lt_or_ge (Nat.card E) 4 with h4 | h4
    · rcases (show Nat.card E = 2 ∨ Nat.card E = 3 by omega) with h2 | h3
      · exact Or.inr (Or.inr ⟨h2, by omega⟩)
      · exact Or.inr (Or.inl ⟨h3, hm⟩)
    · exact Or.inl (Or.inr h4)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨hperf, -, -⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple m E (by omega) hF
    exact hperf.commutator_eq_top
  · exact isChevSimple_congr (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv m E).symm
      (isChevSimple_statedProj_sp m hm hne)
  · rintro ⟨e⟩
    exact (spAltSixFacts_holds E m hm hne).elim e

private noncomputable def spFourEquiv {k : Type} [Field k] [Finite k] (hk : Nat.card k = 2) :
    StatedSp 2 k ≃* sympFour :=
  (statedProjEquivOfBot (StatedSp 2 k) (statedScalars_eq_bot hk)).symm.trans
    (statedProjEquivSympFour hk)

private theorem map_commutator_spFourEquiv {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) :
    (commutator (StatedSp 2 k)).map (spFourEquiv hk).toMonoidHom = commutator sympFour := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    (spFourEquiv hk).toMonoidHom.range_eq_top_of_surjective (spFourEquiv hk).surjective]

private noncomputable def commutatorSpFourEquiv {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = 2) : ↥(commutator (StatedSp 2 k)) ≃* ↥(commutator sympFour) :=
  ((spFourEquiv hk).subgroupMap (commutator (StatedSp 2 k))).trans
    (MulEquiv.subgroupCongr (map_commutator_spFourEquiv hk))

theorem spFourTwoFacts_holds : SpFourTwoFacts := by
  intro E _ _ hE
  have hk : Nat.card E = 2 := by rw [Nat.card_eq_fintype_card]; exact hE
  let e : ↥(commutator ↥(StatedSp 2 E)) ≃* ↥(commutator sympFour) := commutatorSpFourEquiv hk
  haveI : IsSimpleGroup ↥(commutator sympFour) := isSimpleGroup_commutator_sympFour
  haveI : Group.IsPerfect ↥(commutator sympFour) := isPerfect_commutator_sympFour
  haveI : IsSimpleGroup ↥(commutator ↥(StatedSp 2 E)) := e.isSimpleGroup
  haveI : Group.IsPerfect ↥(commutator ↥(StatedSp 2 E)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcen : Subgroup.center ↥(commutator ↥(StatedSp 2 E)) = ⊥ := by
    rcases (inferInstance :
      (Subgroup.center ↥(commutator ↥(StatedSp 2 E))).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact absurd (Subgroup.center_eq_top_iff.1 h) (Group.IsPerfect.not_isMulCommutative _)
  have h56 : 5 ≤ 6 := by norm_num
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_, fun _ => ?_⟩
  · exact Or.inr ⟨.alternating 6 h56, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩),
      ⟨(QuotientGroup.quotientMulEquivOfEq hcen).trans
        (QuotientGroup.quotientBot.trans (e.trans commutatorEquivAlternating))⟩⟩
  · rw [hcen, Subgroup.card_bot]
    omega

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
