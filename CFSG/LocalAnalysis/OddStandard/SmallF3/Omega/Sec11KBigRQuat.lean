module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.Open.ClassicalInvolutionTheoremMilestoneDefs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L115cA
import CFSG.Holt.TwoGroups
import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem s900_mem_of_odd_orderOf {X : Type*} [Group X] [Finite X] (K : Subgroup X)
    [K.Normal] (hq : IsPGroup 2 (X ⧸ K)) {g : X} (hg : Odd (orderOf g)) : g ∈ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hq (g : X ⧸ K)
  have h1 : orderOf (g : X ⧸ K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : orderOf (g : X ⧸ K) ∣ orderOf g := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl
  have h3 : orderOf (g : X ⧸ K) ∣ Nat.gcd (orderOf g) (2 ^ n) := Nat.dvd_gcd h2 h1
  have hc2 : Nat.Coprime (orderOf g) 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
      (by have := Nat.odd_iff.1 hg; omega)).symm
  have hcop : Nat.gcd (orderOf g) (2 ^ n) = 1 := Nat.Coprime.pow_right n hc2
  rw [hcop] at h3
  have : (g : X ⧸ K) = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact (QuotientGroup.eq_one_iff g).1 this

theorem s900_oTwoRes_idem (X : Subgroup G) : oTwoRes (oTwoRes X) = oTwoRes X := by
  refine le_antisymm (sec11c_oTwoRes_mono (sec11c_oTwoRes_le X)) ?_
  exact (Subgroup.closure_le _).2 fun x hx =>
    sec11c_mem_oTwoRes (Subgroup.subset_closure hx) hx.2

theorem s900_not_isPGroup_quot [Finite G] {E : Subgroup G} (hgen : oTwoRes E = E)
    (h2 : 2 ∣ Nat.card E) :
    ¬ IsPGroup 2 (↥E ⧸ CFSG.Open.classicalInvolutionOddCore ↥E) := by
  intro hq
  let O : Subgroup ↥E := CFSG.Open.classicalInvolutionOddCore ↥E
  haveI : O.Normal := CFSG.Open.classicalInvolutionOddCore_normal ↥E
  have hle' : oTwoRes E ≤ O.map E.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxE, hxodd⟩
    refine ⟨⟨x, hxE⟩, ?_, rfl⟩
    exact s900_mem_of_odd_orderOf O hq (by rw [Subgroup.orderOf_mk]; exact hxodd)
  have hle : E ≤ O.map E.subtype := (le_of_eq hgen.symm).trans hle'
  have hEmap : E = O.map E.subtype := le_antisymm hle (Subgroup.map_subtype_le O)
  have hcard : Nat.card E = Nat.card O :=
    (congrArg (fun H : Subgroup G => Nat.card H) hEmap).trans
      (Subgroup.card_map_of_injective E.subtype_injective)
  have hodd : Odd (Nat.card E) := by
    rw [hcard]
    have hO : O = CFSG.pPrimeCore 2 ↥E := by
      rw [show O = CFSG.oddCore ↥E from rfl, CFSG.oddCore_eq_piCore (G := ↥E),
        ← CFSG.pPrimeCore_eq_piCore (G := ↥E) (p := 2)]
    rw [hO]
    exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem s900_sylow_quaternion [Finite G] {E : Subgroup G} {z : G} (hgen : oTwoRes E = E)
    (h2 : 2 ∣ Nat.card E) (huniq : ∀ s ∈ E, orderOf s = 2 → s = z) (S : Sylow 2 ↥E) :
    ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup ↥E) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have hatmost : CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution
      ↥(S : Subgroup ↥E) := by
    intro s t hs ht
    apply Subtype.ext
    apply Subtype.ext
    have hs2 : orderOf ((s : ↥E) : G) = 2 :=
      (Subgroup.orderOf_coe (s : ↥E)).trans ((Subgroup.orderOf_coe s).trans hs)
    have ht2 : orderOf ((t : ↥E) : G) = 2 :=
      (Subgroup.orderOf_coe (t : ↥E)).trans ((Subgroup.orderOf_coe t).trans ht)
    rw [huniq _ (s : ↥E).2 hs2, huniq _ (t : ↥E).2 ht2]
  rcases CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution S.isPGroup' hatmost with
    hcyc | ⟨n, hn3, ⟨e⟩⟩
  · exfalso
    obtain ⟨-, -, -, ⟨hKn, hKodd, hKidx, -⟩, -⟩ :=
      CFSG.cyclic_sylow_normal_odd_complement S hcyc
    have hEmap' : oTwoRes E ≤ (CFSG.pPrimeCore 2 ↥E).map E.subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hxE, hxodd⟩
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      haveI : (CFSG.pPrimeCore 2 ↥E).Normal := hKn
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      have hcard : Nat.card (↥E ⧸ CFSG.pPrimeCore 2 ↥E) = 2 ^ k :=
        (Subgroup.index_eq_card (H := CFSG.pPrimeCore 2 ↥E)).symm.trans (hKidx.trans hk)
      exact s900_mem_of_odd_orderOf (CFSG.pPrimeCore 2 ↥E) (IsPGroup.of_card hcard)
        (by rw [Subgroup.orderOf_mk]; exact hxodd)
    have hEmap : E ≤ (CFSG.pPrimeCore 2 ↥E).map E.subtype :=
      (le_of_eq hgen.symm).trans hEmap'
    have hEK : E = (CFSG.pPrimeCore 2 ↥E).map E.subtype :=
      le_antisymm hEmap (Subgroup.map_subtype_le _)
    have hcardE : Nat.card E = Nat.card (CFSG.pPrimeCore 2 ↥E) :=
      (congrArg (fun H : Subgroup G => Nat.card H) hEK).trans
        (Subgroup.card_map_of_injective E.subtype_injective)
    exact (Nat.not_even_iff_odd.mpr (hcardE ▸ hKodd)) (even_iff_two_dvd.mpr h2)
  · exact ⟨n, hn3, ⟨e⟩⟩

end CFSG.OddStandard.SmallF3.Omega
