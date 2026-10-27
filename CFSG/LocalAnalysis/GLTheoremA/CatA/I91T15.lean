module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T14
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.StandardType CFSG.Assembly TauCeti
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.CatB


theorem chev2_onLie_lieModel {S : Type} [Group S] [Finite S]
    (h : catalogIs S (onLie fun d => d.characteristic = 2)) :
    ∃ (t : StatedLieTag) (n f : ℕ), CFSG.Blueprint.LieModel S t n 2 f := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨dd, hvd⟩ := d
    exact CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid ⟨dd, hvd⟩ hi f
  | _ => exact hi.elim

theorem chev2_not_card_2520 {S : Type} [Group S] [Finite S] (hch : IsChevSimple 2 S)
    (hS : Nat.card S = 2520) : False := by
  rcases hch with h | h
  · obtain ⟨t, n, f, hX⟩ := chev2_onLie_lieModel h
    exact CFSG.ComponentClassification.CatFC.not_lieModel_two_card_2520
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hS
      (CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hX) hX
  · have := card_mem_ambiguous h
    omega

theorem chev2_not_card_443520 {S : Type} [Group S] [Finite S] (hch : IsChevSimple 2 S)
    (hS : Nat.card S = 443520) : False := by
  rcases hch with h | h
  · obtain ⟨t, n, f, hX⟩ := chev2_onLie_lieModel h
    exact CFSG.LocalAnalysis.GLTheoremA.i112d_not_lieModel_two_card_443520 hS
      (CFSG.SeitzReduction.CrossChar.statedLieAdmissible_of_lieModel hX) hX
  · have := card_mem_ambiguous h
    omega

theorem chev2_not_odd_A2 (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] (hch : IsChevSimple 2 S)
    (q : TauCeti.PrimePower) (hv : (LieTypeIndex.A 2 q).Valid) (hq : q.p ≠ 2) (hq7 : 7 ≤ q.card)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hv⟩).Group) : False := by
  have hcard : Nat.card S = orderA 2 q.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.A 2 q, hv⟩ S ⟨e⟩
  rcases hch with h | h
  · obtain ⟨i, hi, ⟨f⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨dd, hvd⟩ := d
      have hdchar : dd.characteristic = 2 := hi
      have hadm : StatedLieAdmissible .PSL 3 q.p q.exponent :=
        ⟨q.prime_p, q.exponent_pos, by norm_num, by simp, by simp⟩
      have hM' : Nat.card S * CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (q.p ^ q.exponent) =
          CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (q.p ^ q.exponent) := by
        refine CatDistinct.hM'_of_card hadm ?_
        rw [hcard]
        simp [orderA, CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
          CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, TauCeti.PrimePower.card_def]
      exact CatDistinct.xc hc (t' := .PSL) (n' := 3) (p := q.p) (g := q.exponent)
        ⟨by simp, by simp⟩ hadm hq hM' ⟨dd, hvd⟩ hdchar f
    | _ => exact hi.elim
  · have := card_mem_ambiguous h
    have := orderA_two_gt_25920 hq7
    omega

theorem chev2_not_odd_U3 (hc : CatDistinct.Ctx) {S : Type} [Group S] [Finite S] (hch : IsChevSimple 2 S)
    (q : TauCeti.PrimePower) (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.p ≠ 2) (hq5 : 5 ≤ q.card)
    (e : S ≃* (CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hv⟩).Group) : False := by
  have hcard : Nat.card S = orderTwistedA 2 q.card :=
    CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds ⟨.twistedA 2 q, hv⟩ S ⟨e⟩
  rcases hch with h | h
  · obtain ⟨i, hi, ⟨f⟩⟩ := h
    cases i with
    | lie d =>
      obtain ⟨dd, hvd⟩ := d
      have hdchar : dd.characteristic = 2 := hi
      have hne : q.p ^ q.exponent ≠ 2 := by
        rw [← TauCeti.PrimePower.card_def]
        omega
      have hadm : StatedLieAdmissible .PSU 3 q.p q.exponent :=
        ⟨q.prime_p, q.exponent_pos, by norm_num, fun h => hne (congrArg Prod.snd h)⟩
      have hM' : Nat.card S * CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (q.p ^ q.exponent) =
          CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (q.p ^ q.exponent) := by
        refine CatDistinct.hM'_of_card hadm ?_
        rw [hcard]
        simp [orderTwistedA, CFSG.ComponentClassification.CatLeaf.lieOrderNumerator,
          CFSG.ComponentClassification.CatLeaf.lieOrderDivisor, TauCeti.PrimePower.card_def]
      exact CatDistinct.xc hc (t' := .PSU) (n' := 3) (p := q.p) (g := q.exponent)
        ⟨by simp, by simp⟩ hadm hq hM' ⟨dd, hvd⟩ hdchar f
    | _ => exact hi.elim
  · have := card_mem_ambiguous h
    have := orderTwistedA_two_gt_25920 hq5
    omega

theorem excChev2_class (hc : CatDistinct.Ctx) : ExcChev2Class := by
  unfold ExcChev2Class
  intro S _ _ hexc hch
  obtain ⟨i, hi, ⟨e⟩⟩ := hexc
  cases i with
  | alternating n hn =>
    have hi' : n = 6 ∨ n = 7 := hi
    rcases hi' with rfl | rfl
    · exact Or.inl ⟨CFSGIndex.alternating 6 hn, rfl, ⟨e⟩⟩
    · have hS : Nat.card S = 2520 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        norm_num [Nat.card_eq_fintype_card, Nat.factorial]
      exact (chev2_not_card_2520 hch hS).elim
  | cyclic _ _ => exact hi.elim
  | sporadic s =>
    have hs : s = SporadicName.M22 := hi
    subst hs
    have hS : Nat.card S = 443520 := by
      rw [Nat.card_congr e.toEquiv]
      exact hc.m22
    exact (chev2_not_card_443520 hch hS).elim
  | lie d =>
    obtain ⟨dd, hvd⟩ := d
    cases dd with
    | A r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      ·
        have hi' : q.card % 9 = 4 ∨ q.card % 9 = 7 := hi
        by_cases hp : q.p = 2
        · have hc2 : q.card = 2 ^ q.exponent := by
            rw [TauCeti.PrimePower.card_def, hp]
          have h2m : 2 ^ q.exponent % 9 = 4 ∨ 2 ^ q.exponent % 9 = 7 := by
            rw [← hc2]
            exact hi'
          have hev : Even q.exponent := even_of_mod_nine_47 h2m
          have hk2 : 2 ≤ q.exponent := by
            obtain ⟨j, hj⟩ := hev
            have := q.exponent_pos
            omega
          exact Or.inr (Or.inl ⟨q.exponent, hk2, hev,
            CFSGIndex.lie ⟨LieTypeIndex.A 2 q, hvd⟩, ⟨hp, rfl⟩, ⟨e⟩⟩)
        · have hodd : q.card % 2 = 1 := by
            rw [TauCeti.PrimePower.card_def]
            exact Nat.odd_iff.1 (Odd.pow (Nat.Prime.odd_of_ne_two q.prime_p hp))
          exact (chev2_not_odd_A2 hc hch q hvd hp (by omega) e).elim
      · exact hi.elim
    | twistedA r q =>
      rcases r with _ | _ | _ | r
      · exact hi.elim
      · exact hi.elim
      ·
        have hi' : q.card % 9 = 2 ∨ q.card % 9 = 5 := hi
        have h3 : 3 ≤ q.card := by
          have h := ((LieTypeIndex.valid_iff _).1 hvd).1
          have h' : 2 ≤ 2 ∧ (2 = 2 → 3 ≤ q.card) := (LieTypeIndex.inStandardRange_iff _).1 h
          exact h'.2 rfl
        by_cases hp : q.p = 2
        · have hc2 : q.card = 2 ^ q.exponent := by
            rw [TauCeti.PrimePower.card_def, hp]
          have hk2 : 2 ≤ q.exponent := by
            by_contra hlt
            have h1 : q.exponent = 1 := by
              have := q.exponent_pos
              omega
            rw [hc2, h1] at h3
            norm_num at h3
          have h2m : 2 ^ q.exponent % 9 = 2 ∨ 2 ^ q.exponent % 9 = 5 := by
            rw [← hc2]
            exact hi'
          obtain ⟨hodd, h5⟩ := odd_of_mod_nine_25 h2m hk2
          exact Or.inr (Or.inr ⟨q.exponent, h5, hodd,
            CFSGIndex.lie ⟨LieTypeIndex.twistedA 2 q, hvd⟩, ⟨hp, rfl⟩, ⟨e⟩⟩)
        · exact (chev2_not_odd_U3 hc hch q hvd hp (by omega) e).elim
      · exact hi.elim
    | _ => exact hi.elim

end I91T

end CFSG.LocalAnalysis.GLTheoremA
