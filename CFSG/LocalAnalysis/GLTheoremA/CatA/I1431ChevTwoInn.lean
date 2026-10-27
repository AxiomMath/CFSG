module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ZBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxUnitary
public import CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridgeHolds
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I1431C2

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem ordTwistedA_three_two : ordTwistedA 3 (2 ^ 1) = 25920 := by
  decide +kernel

theorem ordTwistedA_two_four : ordTwistedA 2 (2 ^ 2) = 62400 := by
  decide +kernel

theorem not_mem_evenOrders_u42 : (25920 : ℕ) ∉ evenOrdersExceptUnitarySp4 := by
  intro hm
  exact (evenOrdersExceptUnitarySp4_ne hm).1 3 1 (by norm_num) le_rfl ordTwistedA_three_two.symm

theorem ordTwistedA_eq_orderTwistedA_of_pos (n Q : ℕ) (hQ : 1 ≤ Q) :
    ordTwistedA n Q = orderTwistedA n Q := by
  unfold ordTwistedA orderTwistedA
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
  have hc : ((Q ^ i : ℕ) : ℤ) = (Q : ℤ) ^ i := Nat.cast_pow Q i
  rcases Nat.even_or_odd i with hi | hi
  · rw [if_pos hi, hi.neg_one_pow]
    omega
  · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
    omega

theorem card_eq_two_pow {q : TauCeti.PrimePower} (hp : q.p = 2) : q.card = 2 ^ q.exponent := by
  rw [TauCeti.PrimePower.card_def, hp]

theorem exists_fieldSize_two_pow {e : TauCeti.LieTypeIndex} (hc : e.characteristic = 2) :
    ∃ k : ℕ, 1 ≤ k ∧ fieldSize e = 2 ^ k := by
  cases e with
  | A _ q | twistedA _ q | B _ q | C _ q | D _ q | twistedD _ q =>
    have hp : q.p = 2 := by simpa using hc
    exact ⟨q.exponent, q.exponent_pos, by simp [fieldSize, hp]⟩
  | E6 q | E7 q | E8 q | F4 q | G2 q | twistedE6 q | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hc
    exact ⟨q.exponent, q.exponent_pos, by simp [fieldSize, hp]⟩
  | suzuki k => exact ⟨2 * k + 1, by omega, rfl⟩
  | reeG2 k => simp at hc
  | reeF4 k => exact ⟨2 * k + 1, by omega, rfl⟩
  | tits => exact ⟨1, le_rfl, rfl⟩

theorem fieldSize_eq_two_of_twistedA {n : ℕ} {q : TauCeti.PrimePower} (hn : 2 ≤ n)
    (hp : q.p = 2) (h : orderTwistedA n q.card = 25920) : q.card = 2 := by
  have hq : q.card = 2 ^ q.exponent := card_eq_two_pow hp
  have h2 : ordTwistedA n (2 ^ q.exponent) = 25920 := by
    rw [← hq, ordTwistedA_eq_orderTwistedA_of_pos n _ (by rw [hq]; exact Nat.one_le_two_pow)]
    exact h
  obtain ⟨r, hr, hm⟩ := (profile_ordTwistedA hn q.exponent_pos).two
  have hN : q.exponent * (n * (n + 1) / 2) = 6 :=
    eq_of_two_pow_mul_odd hr (by decide : Odd 405)
      ((hm.symm.trans h2).trans (by norm_num : (25920 : ℕ) = 2 ^ 6 * 405))
  have hn3 : n ≤ 3 := by
    by_contra hn4
    have h10 : 10 ≤ n * (n + 1) / 2 := by
      have : 20 ≤ n * (n + 1) := by nlinarith
      omega
    have := q.exponent_pos
    nlinarith
  have hq1 : q.exponent = 1 := by
    rcases (show n = 2 ∨ n = 3 by omega) with rfl | rfl
    · have h2' : q.exponent = 2 := by norm_num at hN; omega
      rw [h2'] at h2
      have := ordTwistedA_two_four
      omega
    · norm_num at hN
      omega
  rw [hq, hq1]
  rfl

theorem false_of_orderBC_two {q : TauCeti.PrimePower} (hp : q.p = 2)
    (h : orderBC 2 q.card = 25920) : False := by
  have h2 : ordBC 2 (2 ^ q.exponent) = 25920 := by rw [← card_eq_two_pow hp]; exact h
  obtain ⟨r, hr, hm⟩ := (profile_ordBC (n := 2) q.exponent_pos).two
  have hN : q.exponent * (2 * 2) = 6 :=
    eq_of_two_pow_mul_odd hr (by decide : Odd 405)
      ((hm.symm.trans h2).trans (by norm_num : (25920 : ℕ) = 2 ^ 6 * 405))
  omega

theorem fieldSize_eq_two_of_lieOrderFormula {e : TauCeti.LieTypeIndex} (he : e.Valid)
    (hc : e.characteristic = 2) (h : lieOrderFormula e = 25920) : fieldSize e = 2 := by
  have hs := ((TauCeti.LieTypeIndex.valid_iff e).1 he).1
  rw [TauCeti.LieTypeIndex.inStandardRange_iff] at hs
  cases e with
  | A n q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, Or.inl ⟨n, hs.1, ?_, ?_⟩⟩)
    · intro hnf
      have h4 : 4 ≤ q.card := hs.2 (Prod.mk.inj hnf).1
      rw [card_eq_two_pow hp, (Prod.mk.inj hnf).2] at h4
      omega
    · rw [← card_eq_two_pow hp]
      exact h.symm
  | twistedA n q =>
    have hp : q.p = 2 := by simpa using hc
    have hq2 : q.card = 2 := fieldSize_eq_two_of_twistedA hs.1 hp h
    simpa [fieldSize] using hq2
  | B n q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by have := hs.1; omega
      exact false_of_orderBC_two hp h
    · refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
      right
      left
      exact ⟨n, h3, by rw [← card_eq_two_pow hp]; exact h.symm⟩
  | C n q =>
    have hp : q.p = 2 := by simpa using hc
    exact absurd hp hs.2
  | D n q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 2 right
    left
    exact ⟨n, hs, Or.inl (by rw [← card_eq_two_pow hp]; exact h.symm)⟩
  | twistedD n q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 2 right
    left
    exact ⟨n, hs, Or.inr (by rw [← card_eq_two_pow hp]; exact h.symm)⟩
  | E6 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 6 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | E7 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 8 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | E8 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 9 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | F4 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 5 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | G2 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 3 right
    left
    refine ⟨?_, by rw [← card_eq_two_pow hp]; exact h.symm⟩
    by_contra hlt
    have h3 : 3 ≤ q.card := hs
    rw [card_eq_two_pow hp, (by have := q.exponent_pos; omega : q.exponent = 1)] at h3
    omega
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 7 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hc
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨q.exponent, q.exponent_pos, ?_⟩)
    iterate 4 right
    left
    rw [← card_eq_two_pow hp]
    exact h.symm
  | suzuki k =>
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨2 * k + 1, by omega, ?_⟩)
    iterate 10 right
    exact ⟨odd_two_mul_add_one k, by omega, Or.inl h.symm⟩
  | reeG2 k => simp at hc
  | reeF4 k =>
    exfalso
    refine not_mem_evenOrders_u42 (Or.inl ⟨2 * k + 1, by omega, ?_⟩)
    iterate 10 right
    exact ⟨odd_two_mul_add_one k, by omega, Or.inr h.symm⟩
  | tits =>
    exfalso
    exact not_mem_evenOrders_u42 (Or.inr h.symm)

theorem compIdxAt_three_of_families
    (h1 : LieCompIdx isLinearIdx) (h2 : LieCompIdx isUnitaryIdx)
    (h3 : LieCompIdx isClassicalBCDIdx) (h4 : LieCompIdx isTrialityIdx)
    (h5 : LieCompIdx isExcUntwistedIdx) (h6 : LieCompIdx isExcTwistedIdx)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2) :
    CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨e, hv⟩ := d
  have hne : 3 ≠ e.characteristic := by
    have h2 : e.characteristic = 2 := hd
    rw [h2]
    norm_num
  cases e with
  | A _ _ => exact h1 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | twistedA _ _ => exact h2 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | B _ _ => exact h3 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | C _ _ => exact h3 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | D _ _ => exact h3 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | twistedD _ _ => exact h3 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | E6 _ => exact h5 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | E7 _ => exact h5 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | E8 _ => exact h5 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | F4 _ => exact h5 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | G2 _ => exact h5 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | twistedE6 _ => exact h6 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | trialityD4 _ => exact h4 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | suzuki _ => exact h6 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | reeG2 _ => exact h6 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | reeF4 _ => exact h6 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial
  | tits => exact h6 ⟨_, hv⟩ 3 Nat.prime_three (by norm_num) hne trivial

theorem exists_component_index (hL : LieSemisimpleCent) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hI : CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group)
    {α : MulAut S} (hα : α ∈ innAutDerived S) (hP : U42Pumpup S α) :
    ∃ (i : TauCeti.CFSGIndex) (J : Subgroup S), compRelC d.1 i ∧
      Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      catalogIs (↥J ⧸ Subgroup.center ↥J) S9.isU4two := by
  obtain ⟨hα3, hα1, J, hJ, hU⟩ := hP
  have hpil : PerfectInLayer α :=
    hL S hS hnc d ⟨e⟩ 3 Nat.prime_three (by norm_num) (by rw [hd]; norm_num) α hα3 hα1
  have hJle : J ≤ GLALayer (fixSubgroup α) := hpil J hJ.1 (glaPComponent_perfect hJ)
  have hJcomp : IsComponentOf J (fixSubgroup α) :=
    (glaPComponent_isComponent_of_le_layer hJ hJle).1
  obtain ⟨i, ⟨φ⟩, hrel⟩ := (compIdxAt_of_mulEquiv e.symm hI) α hα hα3 hα1 J hJcomp
  refine ⟨i, J, hrel, ⟨φ⟩, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 J) := isQuasisimple_quotient_of_glaPComponent hJ
  haveI : Nontrivial (PQuot 3 J) := by
    have := hq.2.toNontrivial
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J ⧸ Subgroup.center (PQuot 3 J))
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨⟨a, b, fun h => hab (by rw [h])⟩⟩
  have hne : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := exists_pair_ne (PQuot 3 J)
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [QuotientGroup.eq, htop]
    exact Subgroup.mem_top _
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).ker ≤ Subgroup.center ↥J := by
    rw [QuotientGroup.ker_mk']
    exact le_center_of_normal_of_isQuasisimple hJcomp.2.2 (GLAPPrimeCore.normal 3 ↥J) hne
  obtain ⟨ψ⟩ := psimple_equiv_of_central_surj hJcomp.2.2
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) (QuotientGroup.mk'_surjective _) hker
  obtain ⟨i', hi', ⟨f⟩⟩ := hU
  exact ⟨i', hi', ⟨ψ.trans f⟩⟩

theorem fieldSize_eq_two_of_compRelC (hB : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1.characteristic = 2)
    (i : TauCeti.CFSGIndex) (hrel : compRelC d.1 i) (φ : T ≃* i.Group)
    (hT : catalogIs T S9.isU4two) : fieldSize d.1 = 2 := by
  obtain ⟨k, hk, hkd⟩ := exists_fieldSize_two_pow hd
  cases i with
  | cyclic _ _ => exact hrel.elim
  | sporadic _ => exact hrel.elim
  | alternating n hn => exact (i1431_u42_not_alt hn hT φ).elim
  | lie e =>
    have hord : lieOrderFormula e.1 = 25920 :=
      (hB e T ⟨φ⟩).symm.trans (I1431Z.card_eq_of_u4two hT)
    rcases hrel with ⟨hc, ⟨j, hj, hf⟩, -⟩ | ⟨hf2, -⟩ | ⟨hf3, -⟩
    · have he2 : fieldSize e.1 = 2 :=
        fieldSize_eq_two_of_lieOrderFormula e.2 (hc.trans hd) hord
      rw [he2, hkd, ← pow_mul] at hf
      have hkj : k * j = 1 := by
        have : 2 ^ 1 = 2 ^ (k * j) := by simpa using hf
        exact (Nat.pow_right_injective le_rfl this).symm
      rw [hkd, Nat.eq_one_of_mul_eq_one_right hkj]
      rfl
    · exact hf2
    · exfalso
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rw [← hkd, hf3] at h2
      omega

theorem u42InnField_of_inputs (hL : LieSemisimpleCent) (hB : LieOrderBridge)
    (hI : ∀ d : TauCeti.ValidLieTypeIndex, d.1.characteristic = 2 →
      CompIdxAt 3 d.1 (TauCeti.CFSGIndex.lie d).Group) : U42InnField := by
  intro S _ _ hS hnc d hd hSd α hα hP
  obtain ⟨e⟩ := hSd
  obtain ⟨i, J, hrel, ⟨φ⟩, hcat⟩ := exists_component_index hL hS hnc d hd e (hI d hd) hα hP
  exact fieldSize_eq_two_of_compRelC hB d hd i hrel φ hcat

theorem u42InnField_holds :
    U42InnField :=
  u42InnField_of_inputs LieSemisimple.lieSemisimpleCent lieOrderBridge_holds
    (compIdxAt_three_of_families lieCompIdx_linear lieCompIdx_unitary lieCompIdx_classicalBCD
      lieCompIdx_triality lieCompIdx_excUntwisted lieCompIdx_excTwisted)

end CFSG.LocalAnalysis.GLTheoremA.I1431C2

end
