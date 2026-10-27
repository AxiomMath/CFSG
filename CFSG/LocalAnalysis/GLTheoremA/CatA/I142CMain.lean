module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Cyc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142CSmall
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsU33
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142C

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

theorem centFix_zpowers' {X : Type*} [Group X] (β : MulAut X) :
    CFSG.LocalAnalysis.GLTheoremA.I142.centFix (Subgroup.zpowers β) = fixSubgroup β := by
  ext x
  rw [CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix, mem_fixSubgroup]
  constructor
  · intro h
    exact h β (Subgroup.mem_zpowers β)
  · intro hx e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hβs : β ∈ MulAction.stabilizer (MulAut X) x := MulAction.mem_stabilizer_iff.2 hx
    exact MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer (MulAut X) x).zpow_mem hβs k)

theorem primePower_eq_of_card {q : TauCeti.PrimePower} {r : ℕ} (hr : r.Prime) (h : q.card = r) :
    q.p = r ∧ q.exponent = 1 :=
  (Nat.Prime.pow_eq_iff hr).1 ((TauCeti.PrimePower.card_def q).symm.trans h)

theorem chevA_cases (r : ℕ) (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A r q, hv⟩)) :
    r = 1 ∧ q.card = 7 := by
  simp only [ambiguousChev] at h
  split at h
  · rename_i q' heq
    cases heq
    rcases h with h | h
    · exact ⟨rfl, h.1⟩
    · exact absurd h.2 (by norm_num)
  · rename_i q' heq
    cases heq
  · rename_i q' heq
    cases heq
  · exact h.elim

theorem chevTwistedA_cases (r : ℕ) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩)) :
    r = 2 ∧ q.card = 3 := by
  simp only [ambiguousChev] at h
  split at h
  · rename_i q' heq
    cases heq
  · rename_i q' heq
    cases heq
    exact ⟨rfl, h.1⟩
  · rename_i q' heq
    cases heq
    exact absurd h.2 (by norm_num)
  · exact h.elim

theorem chev2_lie_cases (d1 : TauCeti.LieTypeIndex) (hv : d1.Valid)
    (h : ambiguousChev 2 (TauCeti.CFSGIndex.lie ⟨d1, hv⟩)) :
    (∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.A 1 q ∧ q.card = 7) ∨
    (∃ q : TauCeti.PrimePower, d1 = TauCeti.LieTypeIndex.twistedA 2 q ∧ q.card = 3) := by
  cases d1 with
  | A r q =>
    obtain ⟨rfl, hq⟩ := chevA_cases r q hv h
    exact Or.inl ⟨q, rfl, hq⟩
  | twistedA r q =>
    obtain ⟨rfl, hq⟩ := chevTwistedA_cases r q hv h
    exact Or.inr ⟨q, rfl, hq⟩
  | B r q => simp [ambiguousChev] at h
  | C r q => simp [ambiguousChev] at h
  | D r q => simp [ambiguousChev] at h
  | twistedD r q => simp [ambiguousChev] at h
  | E6 q => simp [ambiguousChev] at h
  | E7 q => simp [ambiguousChev] at h
  | E8 q => simp [ambiguousChev] at h
  | F4 q => simp [ambiguousChev] at h
  | G2 q => simp [ambiguousChev] at h
  | twistedE6 q => simp [ambiguousChev] at h
  | trialityD4 q => simp [ambiguousChev] at h
  | suzuki m => simp [ambiguousChev] at h
  | reeG2 m => simp [ambiguousChev] at h
  | reeF4 m => simp [ambiguousChev] at h
  | tits => simp [ambiguousChev] at h

section Cert


theorem u33_data {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnc : ∃ a b : S, a * b ≠ b * a) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq3 : q.card = 3)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩).Group) :
    Nat.card S = 6048 ∧ (MulAut.conj : S →* MulAut S).range.index ≤ 2 ∧
      ∀ x : S, x ^ 3 = 1 → x ≠ 1 → ¬ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set S)) := by
  obtain ⟨hq3p, -⟩ := primePower_eq_of_card Nat.prime_three hq3
  have hL := CFSG.Models.lieModel_twistedA 2 q hv e
  have hchar : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 3 :=
    (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hq3p
  have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 1 :=
    (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans (primePower_eq_of_card Nat.prime_three hq3).2
  rw [hchar, hfe] at hL
  obtain ⟨-, hSCor⟩ := hL
  rcases hSCor with hSC | ⟨h0, -⟩
  · have hcard : Nat.card S = 6048 := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hSC
    have hrel := CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.relIndex_inn_le_two_of_statedClassicalModel_psu33 hSC
    have hidx : (MulAut.conj : S →* MulAut S).range.index ≤ 2 := by
      rw [← Subgroup.relIndex_top_right]
      exact hrel
    have hd : (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 3 :=
      (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hq3p
    refine ⟨hcard, hidx, fun x hx3 hx1 => ?_⟩
    exact not_seven_dvd_card_cent_u33 hS hnc ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ hd e hcard hx3 hx1
  · exact absurd h0 (by norm_num)

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142C

namespace CFSG.LocalAnalysis.GLTheoremA.I142

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.I142C
open scoped commutatorElement

section Cert


theorem residualCyc_holds : ResidualCyc := by
  intro S _ _ hS hnc hchev p hp hp2 hH β hβ
  haveI := hS
  have hz : Subgroup.center S = ⊥ := b3Lie_center_eq_bot hnc
  have hPIL : PerfectInLayer β := by
    by_cases hβ1 : β = 1
    · subst hβ1
      exact perfectInLayer_one hnc
    rcases hchev with hon | hamb
    · exfalso
      obtain ⟨i, hi, ⟨e⟩⟩ := hon
      cases i with
      | cyclic p' hp' => simp [onLie] at hi
      | alternating n h => simp [onLie] at hi
      | lie d =>
        have h3 := hH d ⟨e⟩
        have h2 : d.1.characteristic = 2 := hi
        omega
      | sporadic s => simp [onLie] at hi
    · obtain ⟨i, hi, ⟨e⟩⟩ := hamb
      cases i with
      | cyclic p' hp' => simp [ambiguousChev] at hi
      | alternating n h =>
        have hn : n = 5 ∨ n = 6 ∨ n = 8 := by
          simp [ambiguousChev] at hi
          omega
        have hn5 : 5 ≤ n := by omega
        have e' : S ≃* alternatingGroup (Fin n) := e
        have hO : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer S) := by
          rw [Nat.card_congr
            (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
          exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
        obtain ⟨x, rfl⟩ := exists_conj_of_pow_eq_one hp hO hβ
        have hxp : x ^ p = 1 :=
          conj_injective_of_center hz (by rw [map_pow, map_one]; exact hβ)
        have hx1 : x ≠ 1 := fun h => hβ1 (by rw [h, map_one])
        exact perfectInLayer_of_alt n hn e' hp hp2 hxp hx1
      | lie d =>
        obtain ⟨d1, hv⟩ := d
        rcases chev2_lie_cases d1 hv hi with ⟨q, rfl, hq7⟩ | ⟨q, rfl, hq3⟩
        ·
          have hcard : Nat.card S = 168 := by
            obtain ⟨hq7p, he1⟩ := primePower_eq_of_card (by norm_num : Nat.Prime 7) hq7
            obtain ⟨-, hSCor⟩ := CFSG.Models.lieModel_A 1 q hv e
            rcases hSCor with hSC | ⟨h0, -⟩
            · rw [hq7p, he1] at hSC
              exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_seven hSC
            · exact absurd h0 (by norm_num)
          exact perfectInLayer_of_card_168 hcard hβ1
        ·
          have hp3 : p = 3 := by
            have h3 := hH ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ ⟨e⟩
            have hc3 : (TauCeti.LieTypeIndex.twistedA 2 q).characteristic = 3 :=
              (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans
                (primePower_eq_of_card Nat.prime_three hq3).1
            rw [← h3]
            exact hc3
          subst hp3
          obtain ⟨hcard, hidx, h7⟩ := u33_data hS hnc q hv hq3 e
          exact perfectInLayer_conj_u33 hnc hcard hidx h7 hβ hβ1
      | sporadic s => simp [ambiguousChev] at hi
  intro P hP hperf
  rw [centFix_zpowers'] at hP ⊢
  exact hPIL P hP hperf

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I142
