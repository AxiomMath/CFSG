module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoBase
public import CFSG.HardMathSupport.Dickson.Bal207.Closed
public import CFSG.HardMathSupport.Dickson.Bal207.D42Triality
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1431ChevTwoClMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieTwoDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (IsTwoPow)
open CFSG.HardMathSupport.Dickson.Bal207 (CompShapeOn OrthCompIdx OrthCompType
  isoInvariant_orthCompType)
open CFSG.HardMathSupport.Dickson.Sec6.I1431 (RkY)
open CFSG.Timmesfeld.Orders (profile_ordD profile_ordTwistedD profile_ordTwistedA
  eq_of_two_pow_mul_odd)
open CFSG.RankThree.PartTwo.Census.Carrier.SpinD (typeDGroupEquivStatedProj_of_valid)

@[expose] def D4TwoShape : Prop :=
  ∀ (S : Type) [Group S] [Finite S], StatedClassicalModel S .POmegaPlus 4 2 1 →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → CompShapeOn 3 OrthCompType ⊤ β

section Shape


theorem d4TwoShape_holds : D4TwoShape :=
  fun _ _ _ hM _ h3 h1 =>
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.compShapeOn_top_of_model
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthInnerShapeInput_holds
      CFSG.HardMathSupport.Dickson.Bal207.OrthFix.orthInnerUniqueTwo_holds
      CFSG.HardMathSupport.Dickson.Bal207.D42Tri.d42TrialityShape_proved (Or.inl rfl)
      (Or.inl ⟨rfl, by norm_num, Or.inr ⟨rfl, rfl⟩⟩) hM h3 h1

end Shape

theorem lieSTwo_ordTwistedA_eq (n Q : ℕ) (hQ : 1 ≤ Q) : ordTwistedA n Q = orderTwistedA n Q := by
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

theorem lieSTwo_lieOrderFormula_ne_of_orthCompIdx {d : TauCeti.LieTypeIndex} (hd : OrthCompIdx d) :
    lieOrderFormula d ≠ 1451520 := by
  intro h
  cases d with
  | D s q =>
    obtain ⟨hq, -, h4⟩ := hd
    have hp : q.p = 2 := by rcases hq with h | h <;> exact h.1
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
    change orderD s q.card = 1451520 at h
    rw [hcard] at h
    obtain ⟨r, hr, hm⟩ := (profile_ordD (n := s) (f := q.exponent) (by omega) q.exponent_pos).two
    have hN : q.exponent * (s * (s - 1)) = 9 := eq_of_two_pow_mul_odd hr (by decide : Odd 2835)
      ((hm.symm.trans h).trans (by norm_num : (1451520 : ℕ) = 2 ^ 9 * 2835))
    have h12 : 12 ≤ s * (s - 1) := Nat.mul_le_mul (show 4 ≤ s from h4) (by omega : 3 ≤ s - 1)
    have hX : 1 * 12 ≤ q.exponent * (s * (s - 1)) := Nat.mul_le_mul q.exponent_pos h12
    omega
  | twistedD s q =>
    obtain ⟨hq, -, h5⟩ := hd
    have hp : q.p = 2 := by rcases hq with h | h <;> exact h.1
    have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
    change orderTwistedD s q.card = 1451520 at h
    rw [hcard] at h
    obtain ⟨r, hr, hm⟩ :=
      (profile_ordTwistedD (n := s) (f := q.exponent) (by omega) q.exponent_pos).two
    have hN : q.exponent * (s * (s - 1)) = 9 := eq_of_two_pow_mul_odd hr (by decide : Odd 2835)
      ((hm.symm.trans h).trans (by norm_num : (1451520 : ℕ) = 2 ^ 9 * 2835))
    have h12 : 12 ≤ s * (s - 1) := Nat.mul_le_mul (show 4 ≤ s by omega) (by omega : 3 ≤ s - 1)
    have hX : 1 * 12 ≤ q.exponent * (s * (s - 1)) := Nat.mul_le_mul q.exponent_pos h12
    omega
  | twistedA r q =>
    change orderTwistedA r q.card = 1451520 at h
    rcases hd with ⟨hq, hr2, hne⟩ | ⟨rfl, hp3, he⟩
    · have hp : q.p = 2 := by rcases hq with h | h <;> exact h.1
      have hcard : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hp]
      have hpos : 1 ≤ 2 ^ q.exponent := Nat.one_le_two_pow
      have h2 : ordTwistedA r (2 ^ q.exponent) = 1451520 := by
        rw [lieSTwo_ordTwistedA_eq r _ hpos, ← hcard]
        exact h
      obtain ⟨m, hm, hmeq⟩ := (profile_ordTwistedA (n := r) (g := q.exponent) hr2
        q.exponent_pos).two
      have hN : q.exponent * (r * (r + 1) / 2) = 9 := eq_of_two_pow_mul_odd hm
        (by decide : Odd 2835)
        ((hmeq.symm.trans h2).trans (by norm_num : (1451520 : ℕ) = 2 ^ 9 * 2835))
      have hr4 : r ≤ 3 := by
        by_contra hr4
        have h20 : 4 * 5 ≤ r * (r + 1) :=
          Nat.mul_le_mul (by omega : 4 ≤ r) (by omega : 5 ≤ r + 1)
        have h10 : 10 ≤ r * (r + 1) / 2 := by omega
        have hX : 1 * 10 ≤ q.exponent * (r * (r + 1) / 2) := Nat.mul_le_mul q.exponent_pos h10
        omega
      have hk : q.exponent = 1 ∨ q.exponent = 3 := by
        rcases hq with h | h
        · exact Or.inl h.2
        · exact Or.inr h.2
      rcases (show r = 2 ∨ r = 3 by omega) with rfl | rfl
      · rcases hk with hk | hk
        · exact hne ⟨rfl, And.intro hp hk⟩
        · rw [hk] at hcard
          rw [hcard] at h
          exact (by decide +kernel : orderTwistedA 2 (2 ^ 3) ≠ 1451520) h
      · omega
    · have hqcard : q.card = 3 := by
        rw [TauCeti.PrimePower.card_def, hp3, he]
        norm_num
      rw [hqcard] at h
      exact (by decide +kernel : orderTwistedA 2 3 ≠ 1451520) h
  | A r q =>
    obtain ⟨rfl, hq⟩ := hd
    have hqcard : q.card = 8 := by
      rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
      norm_num
    change orderA 1 q.card = 1451520 at h
    rw [hqcard] at h
    exact (by decide +kernel : orderA 1 8 ≠ 1451520) h
  | _ => exact hd.elim

theorem lieSTwo_d4_noSp (hLO : LieOrderBridge) (hSh : D4TwoShape) {S : Type} [Group S] [Finite S]
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq : IsTwoPow q 1)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) {α : MulAut S} (hα3 : α ^ 3 = 1)
    (hα1 : α ≠ 1) : ¬ CompOfType S α S9.isSp6two ∧ ¬ CompOfType S α S8.L84.isSp48 := by
  have hqcard : q.card = 2 := by
    rw [TauCeti.PrimePower.card_def, hq.1, hq.2]
    norm_num
  have hM : StatedClassicalModel S .POmegaPlus 4 2 1 := by
    haveI : Finite (TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hK : Nat.card (TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 1 := by
      rw [TauCeti.ValidLieTypeIndex.card_fixedField]
      simp [TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.PrimePower.card_def, hq.1, hq.2]
    exact ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩,
      TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩, inferInstance, inferInstance, hK,
      ⟨e.trans (typeDGroupEquivStatedProj_of_valid 4 q hv)⟩⟩
  have hsh := hSh S hM α hα3 hα1
  have hS : Nat.card S = 174182400 := by
    rw [hLO ⟨.D 4 q, hv⟩ S ⟨e⟩]
    change orderD 4 q.card = 174182400
    rw [hqcard]
    decide +kernel
  refine ⟨?_, lieSTwo_not_sp48_of_not_dvd hLO (by rw [hS]; norm_num)⟩
  rintro ⟨J, hJ, hT⟩
  obtain ⟨hcomp, ⟨eZ⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.component_of_glaPComponent
      Nat.prime_three hsh.layer hJ
  obtain ⟨d, hd, ⟨eQ⟩⟩ := isoInvariant_orthCompType _ _ eZ (hsh.type J hcomp)
  have hc : Nat.card (PSimple 3 J) = lieOrderFormula d.1 := hLO d _ ⟨eQ⟩
  exact lieSTwo_lieOrderFormula_ne_of_orthCompIdx hd (hc.symm.trans (lieSTwo_card_sp6two hLO hT))

theorem lieSTwoAt_D (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge)
    (hSh : D4TwoShape) : LieSTwoAt fun d => ∃ n q, d = .D n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α - hα3 hα1
  have hq : q.card = 2 := hf
  obtain ⟨hp2, hexp⟩ := I1431C2.cl_primePower_card_two hq
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
  simp only [] at hr
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · obtain ⟨h6, h48⟩ := lieSTwo_d4_noSp hLO hSh hv ⟨hp2, hexp⟩ e hα3 hα1
    exact lieSTwo_concl_of_not h6 h48
  · exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.D n q, hv⟩) (fun h => h) e
      (I1431C2.local81_D n q hv hp2 h5)).elim

theorem lieSTwoAt_twistedD (hGA : CFSG.Open.GriessAllModelsStatement) (hLO : LieOrderBridge) :
    LieSTwoAt fun d => ∃ n q, d = .twistedD n q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨n, q, rfl⟩ - hf ⟨e⟩ α hα hα3 hα1
  have hq : q.card = 2 := hf
  obtain ⟨hp2, hexp⟩ := I1431C2.cl_primePower_card_two hq
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
  simp only [] at hr
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | h5
  · haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hY.2
    have hn := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hY
    have hcard : Nat.card (Y ⧸ Subgroup.center Y) = orderTwistedD 4 q.card :=
      hLO ⟨.twistedD 4 q, hv⟩ _ ⟨e⟩
    have h5 : ¬ 3 ^ 5 ∣ Nat.card (Y ⧸ Subgroup.center Y) := by
      rw [hcard, hq]
      exact I1431C2.orthm_not_three_pow_five_dvd_orderTwistedD_four_two
    have hinn := I1431C2.orthm_mem_inner_of_twistedD_four hv hp2 e hα hα3
    exact lieSTwo_of_no_pump hLO fun J hJ h4 =>
      lieSTwo_false_of_inner (I1431C2.cl_center_eq_bot_of_simple hn) hα3 hα1 hJ h4 hinn h5
  · exact (I1431C2.false_of_local81_group hGA hY hRk (d := ⟨.twistedD n q, hv⟩) (fun h => h) e
      (I1431C2.local81_twistedD n q hv hp2 hexp h5)).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
