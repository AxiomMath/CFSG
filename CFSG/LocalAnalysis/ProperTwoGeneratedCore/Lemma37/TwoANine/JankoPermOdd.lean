module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermBasic
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm

open Equiv Subgroup Finset

theorem conj_mem_map_of_mem_normalizer {B : Subgroup (Perm (Fin 9))} {P : Subgroup B} {x : B}
    (hx : x ∈ normalizer (P : Set B)) {r : Perm (Fin 9)} (hr : r ∈ P.map B.subtype) :
    (x : Perm (Fin 9)) * r * (x : Perm (Fin 9))⁻¹ ∈ P.map B.subtype :=
  (mem_normalizer_iff.mp (le_normalizer_map B.subtype ⟨x, hx, rfl⟩) r).mp hr

theorem odd_orderOf_of_odd {G : Type*} [Group G] [Finite G] {B : Subgroup G}
    (hB : Odd (Nat.card B)) (x : B) : Odd (orderOf (x : G)) := by
  rw [Subgroup.orderOf_coe]
  exact Odd.of_dvd_nat hB (orderOf_dvd_natCard x)

theorem false_of_orderOf_five {x : Perm (Fin 9)} (hx : orderOf x = 5)
    {R : Subgroup (Perm (Fin 9))} (hR : Nat.card R = 9 ∨ Nat.card R = 27)
    (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx5 : x ^ 5 ^ 1 = 1 := by rw [pow_one, ← hx, pow_orderOf_eq_one]
  have key := card_modEq_card_inf_centralizer hx5 hxR
  have h1 : Nat.card (R ⊓ centralizer {x} : Subgroup _) ∣ Nat.card R :=
    card_dvd_of_le inf_le_left
  have h2 : Nat.card (R ⊓ centralizer {x} : Subgroup _) ∣ 120 := by
    have := card_dvd_of_le (inf_le_right : R ⊓ centralizer {x} ≤ centralizer {x})
    rwa [card_centralizer_of_orderOf_prime Nat.prime_five le_rfl hx] at this
  generalize Nat.card (R ⊓ centralizer {x} : Subgroup _) = c at key h1 h2
  unfold Nat.ModEq at key
  rcases hR with h | h <;> rw [h] at key h1 <;> have := Nat.le_of_dvd (by norm_num) h1 <;>
    interval_cases c <;> omega

theorem false_of_orderOf_five_of_card_eq_eightyOne {x : Perm (Fin 9)} (hx : orderOf x = 5)
    {R : Subgroup (Perm (Fin 9))} (hR : Nat.card R = 81) (hxR : ∀ r ∈ R, x * r * x⁻¹ ∈ R) :
    False := by
  obtain ⟨a, ha⟩ := exists_apply_eq_of_orderOf_prime Nat.prime_five le_rfl hx
  let Ra := (MulAction.stabilizer R a).map R.subtype
  have hmem : ∀ g, g ∈ Ra ↔ g ∈ R ∧ g a = a := fun g =>
    ⟨fun ⟨g', hg', hgg⟩ => hgg ▸ ⟨g'.2, hg'⟩, fun ⟨hgR, hga⟩ => ⟨⟨g, hgR⟩, hga, rfl⟩⟩
  have h1 : Nat.card Ra ∣ 40320 := card_dvd_of_forall_apply_eq fun g hg => ((hmem g).mp hg).2
  have h2 : Nat.card Ra ∣ 81 := hR ▸ card_dvd_of_le (map_subtype_le _)
  have h3 : 81 ≤ Nat.card Ra * 9 := by
    have h := (MulAction.stabilizer R a).card_mul_index
    rw [MulAction.index_stabilizer, hR] at h
    have horb : Nat.card (MulAction.orbit R a) ≤ 9 := by
      have := Set.ncard_le_ncard (Set.subset_univ (MulAction.orbit R a))
      rwa [Set.ncard_univ, Nat.card_eq_fintype_card (α := Fin 9), Fintype.card_fin,
        ← Nat.card_coe_set_eq] at this
    rw [show Nat.card Ra = Nat.card (MulAction.stabilizer R a) from
      card_map_of_injective R.subtype_injective]
    calc 81 = _ := h.symm
      _ ≤ _ := Nat.mul_le_mul_left _ horb
  have h9 : Nat.card Ra = 9 := by
    generalize Nat.card Ra = c at h1 h2 h3
    have := Nat.le_of_dvd (by norm_num) h2
    interval_cases c <;> omega
  refine false_of_orderOf_five hx (Or.inl h9) fun r hr => ?_
  obtain ⟨hrR, hra⟩ := (hmem r).mp hr
  refine (hmem _).mpr ⟨hxR r hrR, ?_⟩
  have hxa : x⁻¹ a = a := by rw [Perm.inv_eq_iff_eq, ha]
  rw [Perm.mul_apply, Perm.mul_apply, hxa, hra, ha]

theorem exists_fix_of_seven_dvd {B : Subgroup (Perm (Fin 9))} (hodd : Odd (Nat.card B))
    (h7 : 7 ∣ Nat.card B) :
    ∃ (N : Subgroup (Perm (Fin 9))) (a : Fin 9) (n : ℕ), N ≤ B ∧ (∀ g ∈ N, g a = a) ∧
      n ≡ 1 [MOD 7] ∧ Nat.card N * n = Nat.card B := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 7 B))
  have hQ : Nat.card Q = 7 ^ 1 :=
    card_sylow_eq Q (by simpa using h7) ((card_dvd_of_odd hodd).trans (by norm_num)) (m := 405)
      (by norm_num)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 7 (hQ ▸ (by norm_num : 7 ∣ 7 ^ 1))
  have hqB : orderOf (q : B) = 7 := by rw [Subgroup.orderOf_coe, hq]
  have hq9 : orderOf ((q : B) : Perm (Fin 9)) = 7 := by rw [Subgroup.orderOf_coe, hqB]
  have hQeq : (Q : Subgroup B) = zpowers (q : B) := by
    refine (Subgroup.eq_of_le_of_card_ge ((zpowers_le (H := (Q : Subgroup B))).mpr q.2) ?_).symm
    rw [Nat.card_zpowers, hqB, hQ, pow_one]
  obtain ⟨a, ha⟩ := exists_apply_eq_of_orderOf_prime Nat.prime_seven (by norm_num) hq9
  refine ⟨(normalizer (Q : Set B)).map B.subtype, a, (normalizer (Q : Set B)).index,
    map_subtype_le _, ?_, index_normalizer_modEq_one Q, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    have hgn : (g : Perm (Fin 9)) ∈ normalizer ((Q : Subgroup B).map B.subtype : Set _) :=
      le_normalizer_map B.subtype ⟨g, hg, rfl⟩
    rw [hQeq, MonoidHom.map_zpowers] at hgn
    exact apply_eq_of_mem_normalizer hq9 (odd_orderOf_of_odd hodd g) hgn ha
  · rw [card_map_of_injective B.subtype_injective, card_mul_index]

theorem card_eq_eightyOne_of_odd {B : Subgroup (Perm (Fin 9))} (hodd : Odd (Nat.card B))
    (h81 : 81 ∣ Nat.card B) : Nat.card B = 81 := by
  have hB := card_dvd_of_odd hodd
  have h7 : ¬ 7 ∣ Nat.card B := by
    intro h7
    obtain ⟨N, a, n, -, hNa, hn, hcard⟩ := exists_fix_of_seven_dvd hodd h7
    have hN := card_dvd_of_forall_apply_eq hNa
    unfold Nat.ModEq at hn
    have hn1 : n ∣ 405 := by
      have h2835 : n ∣ 405 * 7 := (Dvd.intro_left _ hcard).trans hB
      exact Nat.Coprime.dvd_of_dvd_mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr (by omega)).symm h2835
    have hn' : n = 1 ∨ n = 15 := by
      have hle := Nat.le_of_dvd (by norm_num) hn1
      have key : ∀ m < 406, m ∣ 405 → m % 7 = 1 → m = 1 ∨ m = 15 := by decide +kernel
      exact key n (by omega) hn1 hn
    rw [← hcard] at h81
    have h27 : 27 ∣ Nat.card N := by rcases hn' with rfl | rfl <;> omega
    exact absurd (h27.trans hN) (by norm_num)
  have h405 : Nat.card B ∣ 405 :=
    (Nat.Coprime.dvd_of_dvd_mul_right ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr h7
      ).symm (hB.trans (by norm_num : 2835 ∣ 405 * 7)))
  have hcases : Nat.card B = 81 ∨ Nat.card B = 405 := by
    obtain ⟨k, hk⟩ := h81
    rw [hk] at h405 ⊢
    have hk5 : k ∣ 5 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 81) h405
    rcases (Nat.dvd_prime Nat.prime_five).mp hk5 with rfl | rfl <;> omega
  refine hcases.resolve_right fun h => ?_
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 B))
  have hP : Nat.card P = 3 ^ 4 :=
    card_sylow_eq P (by rw [h]; norm_num) (by rw [h]; norm_num) (m := 5) (by norm_num)
  have hidx : (P : Subgroup B).index = 5 := by
    have := (P : Subgroup B).card_mul_index
    rw [hP, h] at this
    omega
  have hn : (normalizer (P : Set B)).index = 1 := by
    have h5 : (normalizer (P : Set B)).index ∣ 5 := hidx ▸ index_dvd_of_le le_normalizer
    have h1 := index_normalizer_modEq_one P
    unfold Nat.ModEq at h1
    rcases (Nat.dvd_prime Nat.prime_five).mp h5 with h' | h' <;> omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 (by rw [h]; norm_num : 5 ∣ Nat.card B)
  have hxP : x ∈ normalizer (P : Set B) := (index_eq_one.mp hn).symm ▸ mem_top x
  refine false_of_orderOf_five_of_card_eq_eightyOne (x := x) (R := (P : Subgroup B).map B.subtype)
    (by rw [Subgroup.orderOf_coe, hx]) ?_ fun r hr => conj_mem_map_of_mem_normalizer hxP hr
  rw [card_map_of_injective B.subtype_injective, hP]
  norm_num

theorem card_eq_eightyOne_of_odd_alt {B : Subgroup (alternatingGroup (Fin 9))}
    (hodd : Odd (Nat.card B)) (h81 : 81 ∣ Nat.card B) : Nat.card B = 81 := by
  have hc : Nat.card (B.map (alternatingGroup (Fin 9)).subtype) = Nat.card B :=
    card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective
  rw [← hc] at hodd h81 ⊢
  exact card_eq_eightyOne_of_odd hodd h81

theorem card_support_le_six {g : Perm (Fin 9)} (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) :
    #g.support ≤ 6 := by
  have hsub : g.support ⊆ (univ : Finset (Fin 9)) \ {0, 1, 2} := by
    intro i hi
    rw [Perm.mem_support] at hi
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
    rintro (rfl | rfl | rfl) <;> contradiction
  exact (card_le_card hsub).trans (by decide)

theorem card_dvd_nine_or_eq_five_of_odd {B : Subgroup (Perm (Fin 9))}
    (hB : ∀ g ∈ B, g 0 = 0 ∧ g 1 = 1 ∧ g 2 = 2) (hodd : Odd (Nat.card B)) :
    Nat.card B ∣ 9 ∨ Nat.card B = 5 := by
  have hsupp : ∀ g ∈ B, #g.support ≤ 6 := fun g hg =>
    card_support_le_six (hB g hg).1 (hB g hg).2.1 (hB g hg).2.2
  have h315 := card_dvd_of_odd_of_forall_apply_eq hodd fun g hg => (hB g hg).1
  have h7 : ¬ 7 ∣ Nat.card B := by
    intro h7
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 7 h7
    have h1 := card_support_of_orderOf_prime Nat.prime_seven (by norm_num)
      (by rw [Subgroup.orderOf_coe, hq] : orderOf (q : Perm (Fin 9)) = 7)
    have h2 := hsupp q q.2
    omega
  have h45 : Nat.card B ∣ 45 :=
    Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr h7).symm
      (h315.trans (by norm_num : 315 ∣ 45 * 7))
  have h15 : ¬ (3 ∣ Nat.card B ∧ 5 ∣ Nat.card B) := by
    rintro ⟨h3, h5⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow 5 B))
    have hQ : Nat.card Q = 5 ^ 1 :=
      card_sylow_eq Q (by simpa using h5) (h45.trans (by norm_num)) (m := 9) (by norm_num)
    have hn : (normalizer (Q : Set B)).index = 1 := by
      have hidx : (Q : Subgroup B).index ∣ 9 := by
        have h := (Q : Subgroup B).card_mul_index
        rw [hQ, pow_one] at h
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) (h ▸ h45)
      have h9 := (index_dvd_of_le (le_normalizer (H := (Q : Subgroup B)))).trans hidx
      have h1 := index_normalizer_modEq_one Q
      unfold Nat.ModEq at h1
      have hle := Nat.le_of_dvd (by norm_num) h9
      generalize (normalizer (Q : Set B)).index = c at h9 h1 hle ⊢
      interval_cases c <;> omega
    obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hr' : orderOf (r : Perm (Fin 9)) = 3 := by rw [Subgroup.orderOf_coe, hr]
    have hrQ : r ∈ normalizer (Q : Set B) := (index_eq_one.mp hn).symm ▸ mem_top r
    have hr3 : (r : Perm (Fin 9)) ^ 3 ^ 1 = 1 := by rw [pow_one, ← hr', pow_orderOf_eq_one]
    have hQ' : Nat.card ((Q : Subgroup B).map B.subtype) = 5 := by
      rw [card_map_of_injective B.subtype_injective, hQ, pow_one]
    have key := card_modEq_card_inf_centralizer hr3 (R := (Q : Subgroup B).map B.subtype)
      fun s hs => conj_mem_map_of_mem_normalizer hrQ hs
    rw [hQ'] at key
    have hc : Nat.card ((Q : Subgroup B).map B.subtype ⊓ centralizer {(r : Perm (Fin 9))} :
        Subgroup _) = 5 := by
      have hd := hQ' ▸ card_dvd_of_le (inf_le_left (a := (Q : Subgroup B).map B.subtype)
        (b := centralizer {(r : Perm (Fin 9))}))
      unfold Nat.ModEq at key
      rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h <;> omega
    have hle : (Q : Subgroup B).map B.subtype ≤ centralizer {(r : Perm (Fin 9))} :=
      inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hQ']))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 (hQ'.symm ▸ dvd_rfl :
      5 ∣ Nat.card ((Q : Subgroup B).map B.subtype))
    have hx' : orderOf (x : Perm (Fin 9)) = 5 := by rw [Subgroup.orderOf_coe, hx]
    have hcomm : Commute (r : Perm (Fin 9)) x := (mem_centralizer_singleton_iff.mp (hle x.2)).symm
    have hord : orderOf ((r : Perm (Fin 9)) * x) = 15 := by
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hr', hx']; norm_num), hr', hx']
    have h1 := eight_le_card_support_of_orderOf_eq_fifteen hord
    have h2 := hsupp _ (mul_mem r.2 (map_subtype_le _ x.2))
    omega
  have hle := Nat.le_of_dvd (by norm_num) h45
  generalize Nat.card B = c at h45 h15 hle ⊢
  interval_cases c <;> omega

theorem card_dvd_nine_or_eq_five_of_odd_alt {B : Subgroup (alternatingGroup (Fin 9))}
    (hB : B ≤ fixingSubgroup (alternatingGroup (Fin 9)) ({0, 1, 2} : Set (Fin 9)))
    (hodd : Odd (Nat.card B)) : Nat.card B ∣ 9 ∨ Nat.card B = 5 := by
  have hc : Nat.card (B.map (alternatingGroup (Fin 9)).subtype) = Nat.card B :=
    card_map_of_injective (alternatingGroup (Fin 9)).subtype_injective
  rw [← hc] at hodd ⊢
  refine card_dvd_nine_or_eq_five_of_odd ?_ hodd
  rintro _ ⟨g, hg, rfl⟩
  have h := (mem_fixingSubgroup_iff _).mp (hB hg)
  exact ⟨h 0 (by simp), h 1 (by simp), h 2 (by simp)⟩

theorem card_le_nine_of_odd_alt {B : Subgroup (alternatingGroup (Fin 9))}
    (hB : B ≤ fixingSubgroup (alternatingGroup (Fin 9)) ({0, 1, 2} : Set (Fin 9)))
    (hodd : Odd (Nat.card B)) : Nat.card B ≤ 9 := by
  rcases card_dvd_nine_or_eq_five_of_odd_alt hB hodd with h | h
  · exact Nat.le_of_dvd (by norm_num) h
  · omega

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm
