module

public import CFSG.GroupTheory.PResidualLocalFinite
public import CFSG.RankThree.PartOne.FIS.Reduction

import CFSG.RankThree.PartOne.FIS.WidthOne
import CFSG.RankThree.PartOne.FIS.CenterQuotient
import CFSG.CGT.Timmesfeld75.OddCenter
import CFSG.LargeExtraspecial.AS35JThreeT

public section

namespace CFSG.GroupTheory.ThreeTranspositions

open CFSG.Blueprint.Fischer CFSG.Fischer.Classification
open CFSG.Fischer

variable {X : Type} [Group X]

@[expose] def threeResidualJoin (d : X) : Subgroup X :=
  CFSG.Quasithin.pResidualOf 3 (commutator X) ⊔ Subgroup.zpowers d

@[expose] def threeResidualQuot (d : X) : Subgroup (X ⧸ Subgroup.center X) :=
  (threeResidualJoin d).map (QuotientGroup.mk' (Subgroup.center X))

@[expose] def threeResidualClass (d : X) : Set ↥(threeResidualQuot d) :=
  Subtype.val ⁻¹'
    ((fun w : X => (QuotientGroup.mk (w * d * w⁻¹) : X ⧸ Subgroup.center X)) ''
      (threeResidualJoin d : Set X))

theorem map_center_ne_one {E : Set X} (hP : Pair X E)
    (hodd : Odd (Nat.card (Subgroup.center X))) {e : X} (he : e ∈ E) :
    (QuotientGroup.mk' (Subgroup.center X)) e ≠ 1 := by
  intro h1
  have heZ : e ∈ Subgroup.center X := (QuotientGroup.eq_one_iff e).1 h1
  have h2dvd : 2 ∣ Nat.card (Subgroup.center X) := by
    rw [← CFSG.Fischer.Pair.orderOf_eq_two hP he]
    exact Subgroup.orderOf_dvd_natCard _ heZ
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2dvd)

theorem pair_quot_center {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) :
    Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E) := by
  haveI : Finite X := Pair.finite hP
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center h2
  exact CFSG.RankThree.PartOne.FIS.pair_image hP (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (fun e he => map_center_ne_one hP hodd he)

theorem exists_minimalNormal_quotient_center {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X) :
    ∃ N : Subgroup (X ⧸ Subgroup.center X), N.Normal ∧ N ≠ ⊥ ∧
      IsSimpleGroup ↥N ∧ ¬ Group.IsSolvable ↥N ∧
      Subgroup.centralizer (N : Set (X ⧸ Subgroup.center X)) = ⊥ := by
  haveI : Finite X := Pair.finite hP
  have hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E) :=
    pair_quot_center hP h2
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    Pair.center_quotient_center_eq_bot hP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2q : ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hNp
    have hle : N ≤ CFSG.pCore 2 (X ⧸ Subgroup.center X) := le_sSup ⟨hN, hNp⟩
    rw [CFSG.RankThree.PartOne.FIS.pCore_quotient_center_eq_bot 2
      (by rw [h2 _ CFSG.pCore_normal CFSG.pCore_isPGroup]; exact bot_le)] at hle
    exact le_bot_iff.1 hle
  have h3q : ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → IsPGroup 3 N → N = ⊥ := by
    intro N hN hNp
    have hle : N ≤ CFSG.pCore 3 (X ⧸ Subgroup.center X) := le_sSup ⟨hN, hNp⟩
    rw [CFSG.RankThree.PartOne.FIS.pCore_quotient_center_eq_bot 3
      (h3 _ CFSG.pCore_normal CFSG.pCore_isPGroup)] at hle
    exact le_bot_iff.1 hle
  obtain ⟨e, he⟩ := Pair.nonempty hP
  have hodd : Odd (Nat.card (Subgroup.center X)) := CFSG.CGT.Timmesfeld75.odd_card_center h2
  have hne : (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≠ ⊥ := by
    intro hbot
    have hmem : (QuotientGroup.mk' (Subgroup.center X)) e ∈
        (⊤ : Subgroup (X ⧸ Subgroup.center X)) := Subgroup.mem_top _
    rw [hbot] at hmem
    exact map_center_ne_one hP hodd he (by simpa using hmem)
  obtain ⟨N, hNn, -, hNbot, hNmin⟩ :=
    CFSG.exists_minimal_normal_le (⊤ : Subgroup (X ⧸ Subgroup.center X)) inferInstance hne
  exact ⟨N, hNn, hNbot,
    Pair.isSimpleGroup_of_minimal hPq hZ h2q h3q hNn hNbot hNmin,
    Pair.not_isSolvable_of_minimal hPq hZ h2q h3q hNn hNbot hNmin,
    CFSG.RankThree.PartOne.FIS.centralizer_eq_bot_of_minimal hPq hZ h2q h3q hNn hNbot hNmin⟩

theorem commutator_eq_self_of_isSimpleGroup {Y : Type} [Group Y] {N : Subgroup Y}
    (hNs : IsSimpleGroup ↥N) (hNsol : ¬ Group.IsSolvable ↥N) : ⁅N, N⁆ = N := by
  haveI : Group.IsPerfect ↥N :=
    Group.IsPerfect.mk (CFSG.RankThree.PartOne.FIS.commutator_eq_top_of_simple hNs hNsol)
  exact Subgroup.commutator_eq_self

theorem le_commutator_of_isSimpleGroup_of_not_isSolvable {Y : Type} [Group Y] {N : Subgroup Y}
    (hNs : IsSimpleGroup ↥N) (hNsol : ¬ Group.IsSolvable ↥N) : N ≤ commutator Y := by
  calc N = ⁅N, N⁆ := (commutator_eq_self_of_isSimpleGroup hNs hNsol).symm
    _ ≤ commutator Y := Subgroup.commutator_mono le_top le_top

theorem mk'_ne_one_of_notMem {Y : Type} [Group Y] {E : Set Y} (hP : Pair Y E)
    {N : Subgroup Y} (hNn : N.Normal) {d : Y} (hd : d ∈ E) (hdN : d ∉ N)
    {e : Y} (he : e ∈ E) : (QuotientGroup.mk' N) e ≠ 1 := by
  intro h1
  have heN : e ∈ N := (QuotientGroup.eq_one_iff e).1 h1
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP he hd)
  exact hdN (hg ▸ hNn.conj_mem e heN g)

theorem exists_threeNormal_of_pair {Y : Type} [Group Y] {D : Set Y}
    (hP : Pair Y D)
    (hcube : ∀ a ∈ D, ∀ b ∈ D, (a * b) ^ 3 = 1) :
    ∃ P : Subgroup Y, P.Normal ∧ IsPGroup 3 P ∧ commutator Y ≤ P := by
  haveI : Finite Y := Pair.finite hP
  have hnc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a → a = b :=
    fun a ha b hb hab => CFSG.RankThree.PartOne.FIS.WidthOne.eq_of_comm_of_cube
      (Pair.mul_self hP ha) (Pair.mul_self hP hb) hab (hcube a ha b hb)
  have hconj : ∀ e ∈ D, ∀ g : Y, g * e * g⁻¹ ∈ D := fun e he g => Pair.conj_mem hP he g
  let P : Subgroup Y := Subgroup.closure {x | ∃ a ∈ D, ∃ b ∈ D, x = a * b}
  have hPn : P.Normal := CFSG.RankThree.PartOne.FIS.WidthOne.pairClosure_normal hconj
  haveI : P.Normal := hPn
  have hP3 : IsPGroup 3 P :=
    CFSG.RankThree.PartOne.FIS.isPGroup_three_closure_mul D hconj (Pair.closure_eq hP)
      (fun e he => Pair.mul_self hP he) (fun e he => Pair.ne_one hP he) hnc hcube
  refine ⟨P, hPn, hP3, ?_⟩
  refine Pair.commutator_le_of_forall hP ?_
  intro e he f hf
  rw [Pair.inv_eq hP he]
  exact Subgroup.subset_closure ⟨f, hf, e, he, rfl⟩

theorem cube_map_quotient {Y : Type} [Group Y] {E : Set Y} (hP : Pair Y E)
    (hZ : Subgroup.center Y = ⊥) {N : Subgroup Y} (hNn : N.Normal) (hNs : IsSimpleGroup ↥N)
    (hNbot : N ≠ ⊥) :
    ∀ a ∈ (QuotientGroup.mk' N) '' E, ∀ b ∈ (QuotientGroup.mk' N) '' E, (a * b) ^ 3 = 1 := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hmul := Pair.orderOf_mul_mem hP hx hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmul
  rcases hmul with h1 | h2 | h3
  · rw [← map_mul, orderOf_eq_one_iff.1 h1, map_one, one_pow]
  · have hcomm : x * y = y * x :=
      CFSG.LargeExtraspecial.AS35J.commute_of_orderOf_mul_le_two
        (Pair.mul_self hP hx) (Pair.mul_self hP hy) (Or.inr h2)
    have hmem := CFSG.RankThree.PartOne.FIS.mk_eq_of_comm_of_normal hP hZ hNn hNs hNbot
      hx hy hcomm
    have heq : (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) y := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      exact hmem
    rw [heq]
    rw [show (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) y = 1 by
      rw [← map_mul, Pair.mul_self hP hy, map_one], one_pow]
  · rw [← map_mul, ← map_pow, ← h3, pow_orderOf_eq_one, map_one]

theorem pResidualOf_three_commutator_le_of_map_quotient {Y : Type} [Group Y]
    {E : Set Y} (hP : Pair Y E) (hZ : Subgroup.center Y = ⊥) {N : Subgroup Y} (hNn : N.Normal)
    (hNs : IsSimpleGroup ↥N) (hNbot : N ≠ ⊥) (hNle : N ≤ commutator Y)
    (hEne : ∀ e ∈ E, (QuotientGroup.mk' N) e ≠ 1) :
    CFSG.Quasithin.pResidualOf 3 (commutator Y) ≤ N := by
  have hPq : Pair (Y ⧸ N) ((QuotientGroup.mk' N) '' E) :=
    CFSG.RankThree.PartOne.FIS.pair_image hP _ (QuotientGroup.mk'_surjective N) hEne
  obtain ⟨P, hPn, hP3, hPcomm⟩ :=
    exists_threeNormal_of_pair hPq (cube_map_quotient hP hZ hNn hNs hNbot)
  have hmapcomm : (commutator Y).map (QuotientGroup.mk' N) = commutator (Y ⧸ N) :=
    TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective N)
  have hkey : ∀ x ∈ commutator Y, ∃ k : ℕ, x ^ 3 ^ k ∈ N := by
    intro x hx
    have hx' : (QuotientGroup.mk' N) x ∈ commutator (Y ⧸ N) := by
      rw [← hmapcomm]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨k, hk⟩ := hP3 ⟨(QuotientGroup.mk' N) x, hPcomm hx'⟩
    refine ⟨k, ?_⟩
    have hk' : ((QuotientGroup.mk' N) x) ^ 3 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at hk'
    exact (QuotientGroup.eq_one_iff _).1 hk'
  have hres : CFSG.Quasithin.pResidual 3 ↥(commutator Y) ≤ N.subgroupOf (commutator Y) := by
    haveI : (N.subgroupOf (commutator Y)).Normal := hNn.subgroupOf (commutator Y)
    refine CFSG.Quasithin.pResidual_le (fun y => ?_)
    obtain ⟨k, hk⟩ := hkey (y : Y) y.2
    exact ⟨k, by rw [Subgroup.mem_subgroupOf]; simpa using hk⟩
  have hmap := Subgroup.map_mono (f := (commutator Y).subtype) hres
  rwa [Subgroup.map_subgroupOf_eq_of_le hNle] at hmap

theorem pResidualOf_three_commutator_eq {Y : Type} [Group Y] {E : Set Y}
    (hP : Pair Y E) (hZ : Subgroup.center Y = ⊥) {N : Subgroup Y} (hNn : N.Normal)
    (hNbot : N ≠ ⊥) (hNs : IsSimpleGroup ↥N) (hNsol : ¬ Group.IsSolvable ↥N)
    (hNle : N ≤ commutator Y) :
    CFSG.Quasithin.pResidualOf 3 (commutator Y) = N := by
  haveI : Finite Y := Pair.finite hP
  refine le_antisymm ?_
    (le_pResidualOf_of_perfect (commutator_eq_self_of_isSimpleGroup hNs hNsol) hNle)
  by_cases hEN : E ⊆ N
  · have hYeqN : N = ⊤ := by
      rw [eq_top_iff]
      calc (⊤ : Subgroup Y) = Subgroup.closure E := (Pair.closure_eq hP).symm
        _ ≤ N := (Subgroup.closure_le N).mpr hEN
    have hY' : commutator Y = N := by
      rw [commutator_def, ← hYeqN, commutator_eq_self_of_isSimpleGroup hNs hNsol]
    rw [hY']
    exact Subgroup.map_subtype_le (CFSG.Quasithin.pResidual 3 ↥N)
  · obtain ⟨d, hd, hdN⟩ := Set.not_subset.1 hEN
    exact pResidualOf_three_commutator_le_of_map_quotient hP hZ hNn hNs hNbot hNle
      (fun e he => mk'_ne_one_of_notMem hP hNn hd hdN he)

theorem threeResidualQuot_eq_Kgrp [Finite X] {E : Set X}
    (hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E))
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥)
    {N : Subgroup (X ⧸ Subgroup.center X)} (hNn : N.Normal) (hNs : IsSimpleGroup ↥N)
    (hNbot : N ≠ ⊥)
    (hOeq : CFSG.Quasithin.pResidualOf 3 (commutator (X ⧸ Subgroup.center X)) = N)
    {d : X} (hd : d ∈ E) :
    threeResidualQuot d =
      CFSG.RankThree.PartOne.FIS.Kgrp N (QuotientGroup.mk' (Subgroup.center X) d) := by
  have hdπ : (QuotientGroup.mk' (Subgroup.center X)) d ∈
      (QuotientGroup.mk' (Subgroup.center X)) '' E := ⟨d, hd, rfl⟩
  have hKsup : CFSG.RankThree.PartOne.FIS.Kgrp N (QuotientGroup.mk' (Subgroup.center X) d) =
      N ⊔ Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center X) d) :=
    CFSG.RankThree.PartOne.FIS.closure_conjOrbit_eq hPq hZ hNn hNs hNbot hdπ
  unfold threeResidualQuot threeResidualJoin
  rw [Subgroup.map_sup,
    pResidualOf_map_of_surjective (p := 3) _ (QuotientGroup.mk'_surjective _) (commutator X),
    TauCeti.Subgroup.map_commutator_eq_commutator (QuotientGroup.mk'_surjective _),
    MonoidHom.map_zpowers, hOeq, ← hKsup]

theorem image_threeResidualClass {E : Set X}
    (hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E))
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥)
    {N : Subgroup (X ⧸ Subgroup.center X)} (hNn : N.Normal) (hNs : IsSimpleGroup ↥N)
    (hNbot : N ≠ ⊥) {d : X} (hd : d ∈ E)
    (hquot : threeResidualQuot d =
      CFSG.RankThree.PartOne.FIS.Kgrp N (QuotientGroup.mk' (Subgroup.center X) d)) :
    (Subtype.val : ↥(threeResidualQuot d) → X ⧸ Subgroup.center X) '' threeResidualClass d =
      CFSG.RankThree.PartTwo.Sec7.conjOrbit N
        (QuotientGroup.mk' (Subgroup.center X) d) := by
  have hdπ : (QuotientGroup.mk' (Subgroup.center X)) d ∈
      (QuotientGroup.mk' (Subgroup.center X)) '' E := ⟨d, hd, rfl⟩
  have hKsup : CFSG.RankThree.PartOne.FIS.Kgrp N (QuotientGroup.mk' (Subgroup.center X) d) =
      N ⊔ Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center X) d) :=
    CFSG.RankThree.PartOne.FIS.closure_conjOrbit_eq hPq hZ hNn hNs hNbot hdπ
  ext q
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨w, hw, hwq⟩ := ha
    have hwK : (QuotientGroup.mk' (Subgroup.center X)) w ∈
        CFSG.RankThree.PartOne.FIS.Kgrp N
          (QuotientGroup.mk' (Subgroup.center X) d) := by
      rw [← hquot]
      exact Subgroup.mem_map_of_mem _ hw
    rw [hKsup] at hwK
    obtain ⟨n, hn, z, hz, hnz⟩ := Subgroup.mem_sup_of_normal_left.1 hwK
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine ⟨n, hn, ?_⟩
    rw [← hwq]
    change (QuotientGroup.mk' (Subgroup.center X)) (w * d * w⁻¹) = _
    rw [map_mul, map_mul, map_inv, ← hnz]
    group
  · rintro ⟨n, hn, rfl⟩
    have hnK : n ∈ CFSG.RankThree.PartOne.FIS.Kgrp N
        (QuotientGroup.mk' (Subgroup.center X) d) :=
      CFSG.RankThree.PartOne.FIS.normal_le_closure_conjOrbit hPq hZ hNn hNs hNbot hdπ hn
    have hnQ : n ∈ threeResidualQuot d := by rw [hquot]; exact hnK
    obtain ⟨w, hw, hwq⟩ := Subgroup.mem_map.1 hnQ
    refine ⟨⟨n * (QuotientGroup.mk' (Subgroup.center X)) d * n⁻¹, ?_⟩, ?_, rfl⟩
    · rw [hquot]
      exact CFSG.RankThree.PartOne.FIS.conjOrbit_subset_Kgrp N _ ⟨n, hn, rfl⟩
    · refine ⟨w, hw, ?_⟩
      change (QuotientGroup.mk' (Subgroup.center X)) (w * d * w⁻¹) = _
      rw [map_mul, map_mul, map_inv, hwq]

theorem hyp_of_eq_Kgrp {E : Set X}
    (hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E))
    (hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥)
    {N : Subgroup (X ⧸ Subgroup.center X)} (hNn : N.Normal) (hNs : IsSimpleGroup ↥N)
    (hNsol : ¬ Group.IsSolvable ↥N) (hNbot : N ≠ ⊥)
    (hcent : Subgroup.centralizer (N : Set (X ⧸ Subgroup.center X)) = ⊥)
    {d : X} (hd : d ∈ E)
    (hquot : threeResidualQuot d =
      CFSG.RankThree.PartOne.FIS.Kgrp N (QuotientGroup.mk' (Subgroup.center X) d))
    (hclass : (Subtype.val : ↥(threeResidualQuot d) → X ⧸ Subgroup.center X) ''
        threeResidualClass d =
      CFSG.RankThree.PartTwo.Sec7.conjOrbit N
        (QuotientGroup.mk' (Subgroup.center X) d)) :
    Hyp ↥(threeResidualQuot d) (threeResidualClass d) := by
  have hdπ : (QuotientGroup.mk' (Subgroup.center X)) d ∈
      (QuotientGroup.mk' (Subgroup.center X)) '' E := ⟨d, hd, rfl⟩
  have htrans : ∀ (A : Subgroup (X ⧸ Subgroup.center X))
      (hA : A = CFSG.RankThree.PartOne.FIS.Kgrp N
        (QuotientGroup.mk' (Subgroup.center X) d)) (D : Set ↥A),
      (Subtype.val '' D = CFSG.RankThree.PartTwo.Sec7.conjOrbit N
        (QuotientGroup.mk' (Subgroup.center X) d)) → Hyp ↥A D := by
    rintro A rfl D hD
    have hD' : D = Subtype.val ⁻¹' CFSG.RankThree.PartTwo.Sec7.conjOrbit N
        (QuotientGroup.mk' (Subgroup.center X) d) := by
      ext x
      constructor
      · intro hx
        exact hD ▸ Set.mem_image_of_mem Subtype.val hx
      · intro hx
        have hx' : Subtype.val x ∈ Subtype.val '' D := hD.symm ▸ hx
        obtain ⟨y, hy, hxy⟩ := hx'
        rwa [Subtype.val_injective hxy] at hy
    rw [hD']
    exact ⟨CFSG.RankThree.PartOne.FIS.pair_Kgrp hPq hZ hNn hNs hNbot hdπ,
      CFSG.RankThree.PartOne.FIS.center_Kgrp hPq hZ hNn hNs hNbot hdπ hcent,
      (CFSG.RankThree.PartOne.FIS.isSimpleGroup_commutator_Kgrp hPq hZ hNn hNs hNsol hNbot
        hdπ).1⟩
  exact htrans (threeResidualQuot d) hquot (threeResidualClass d) hclass

theorem hyp_threeResidualQuot {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X)
    {d : X} (hd : d ∈ E) :
    Hyp ↥(threeResidualQuot d) (threeResidualClass d) := by
  haveI : Finite X := Pair.finite hP
  obtain ⟨N, hNn, hNbot, hNs, hNsol, hcent⟩ :=
    exists_minimalNormal_quotient_center hP h2 h3
  have hPq : Pair (X ⧸ Subgroup.center X) ((QuotientGroup.mk' (Subgroup.center X)) '' E) :=
    pair_quot_center hP h2
  have hZ : Subgroup.center (X ⧸ Subgroup.center X) = ⊥ :=
    Pair.center_quotient_center_eq_bot hP
  have hNle : N ≤ commutator (X ⧸ Subgroup.center X) :=
    le_commutator_of_isSimpleGroup_of_not_isSolvable hNs hNsol
  have hOeq : CFSG.Quasithin.pResidualOf 3 (commutator (X ⧸ Subgroup.center X)) = N :=
    pResidualOf_three_commutator_eq hPq hZ hNn hNbot hNs hNsol hNle
  have hquot := threeResidualQuot_eq_Kgrp hPq hZ hNn hNs hNbot hOeq hd
  exact hyp_of_eq_Kgrp hPq hZ hNn hNs hNsol hNbot hcent hd hquot
    (image_threeResidualClass hPq hZ hNn hNs hNbot hd hquot)

theorem conclusion_threeResidualQuot (hF : Statement) {E : Set X} (hP : Pair X E)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N ≤ Subgroup.center X)
    {d : X} (hd : d ∈ E) :
    Conclusion ↥(threeResidualQuot d) (threeResidualClass d) :=
  hF _ _ (hyp_threeResidualQuot hP h2 h3 hd)

end CFSG.GroupTheory.ThreeTranspositions
