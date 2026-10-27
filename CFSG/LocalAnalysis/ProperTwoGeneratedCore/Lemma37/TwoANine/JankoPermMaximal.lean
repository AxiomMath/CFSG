module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPermOdd

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm

open Equiv Subgroup

theorem minFac_eightyOne : Nat.minFac 81 = 3 := by
  have h1 : Nat.minFac 81 ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) (by norm_num)
  have h2 : Nat.minFac 81 ≠ 2 := by
    rw [Ne, Nat.minFac_eq_two_iff]
    norm_num
  have h3 := (Nat.minFac_prime (by norm_num : 81 ≠ 1)).two_le
  omega

theorem le_normalizer_of_odd {E Y : Subgroup (Perm (Fin 9))} (hE : Nat.card E = 27)
    (hEfix : ∀ i : Fin 9, ∃ g ∈ E, g i ≠ i) (hY : Odd (Nat.card Y)) (hEY : E ≤ Y) :
    Y ≤ normalizer (E : Set (Perm (Fin 9))) := by
  have hYd := card_dvd_of_odd hY
  have hE' : Nat.card (E.subgroupOf Y) = 27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEY).toEquiv).trans hE
  have hidx : Nat.card Y = 27 * (E.subgroupOf Y).index := by
    rw [← (E.subgroupOf Y).card_mul_index, hE']
  rw [← normal_subgroupOf_iff_le_normalizer hEY]
  by_cases h81 : 81 ∣ Nat.card Y
  · have hY81 := card_eq_eightyOne_of_odd hY h81
    refine normal_of_index_eq_minFac_card ?_
    rw [hY81, minFac_eightyOne]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set m := (E.subgroupOf Y).index with hm
  have hm3 : ¬ 3 ∣ m := fun h => h81 (by rw [hidx]; exact Nat.mul_dvd_mul_left 27 h)
  have hm35 : m ∣ 35 := by
    have h105 : m ∣ 105 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 27)
      (hidx ▸ hYd.trans (by norm_num : 2835 ∣ 27 * 105))
    exact Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm (h105.trans (by norm_num))
  have hn : (normalizer (E.subgroupOf Y : Set Y)).index ≡ 1 [MOD 3] :=
    index_normalizer_modEq_one
      ((IsPGroup.of_card (show Nat.card (E.subgroupOf Y) = 3 ^ 3 by rw [hE']; norm_num)).toSylow
        (show ¬ 3 ∣ (E.subgroupOf Y).index from hm3))
  unfold Nat.ModEq at hn
  have hnm : (normalizer (E.subgroupOf Y : Set Y)).index ∣ m := index_dvd_of_le le_normalizer
  have hn17 : (normalizer (E.subgroupOf Y : Set Y)).index = 1 ∨
      (normalizer (E.subgroupOf Y : Set Y)).index = 7 := by
    have hle := Nat.le_of_dvd (by norm_num) (hnm.trans hm35)
    have hd := hnm.trans hm35
    generalize (normalizer (E.subgroupOf Y : Set Y)).index = c at hn hle hd ⊢
    interval_cases c <;> omega
  rcases hn17 with h1 | h7
  · rw [index_eq_one, normalizer_eq_top_iff] at h1
    exact h1
  exfalso
  have h7Y : 7 ∣ Nat.card Y := by
    rw [hidx]
    exact Dvd.dvd.mul_left (h7 ▸ hnm) 27
  obtain ⟨N, a, n, hNY, hNa, hn7, hcard⟩ := exists_fix_of_seven_dvd hY h7Y
  unfold Nat.ModEq at hn7
  have hn135 : n ∣ 135 := by
    have h945 : n ∣ 135 * 7 :=
      (Dvd.intro_left _ hcard).trans (hidx ▸ Nat.mul_dvd_mul_left 27 hm35)
    exact Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).mpr (by omega)).symm h945
  have hn' : n = 1 ∨ n = 15 := by
    have hle := Nat.le_of_dvd (by norm_num) hn135
    have key : ∀ k < 136, k ∣ 135 → k % 7 = 1 → k = 1 ∨ k = 15 := by decide +kernel
    exact key n (by omega) hn135 hn7
  rcases hn' with rfl | rfl
  · have hNY' : N = Y := Subgroup.eq_of_le_of_card_ge hNY (by omega)
    obtain ⟨g, hg, hga⟩ := hEfix a
    exact hga (hNa g (hNY' ▸ hEY hg))
  · have hcardN := (normalizer (E.subgroupOf Y : Set Y)).card_mul_index
    rw [h7] at hcardN
    have h5 : 5 ∣ Nat.card (normalizer (E.subgroupOf Y : Set Y)) := by
      have h5Y : 5 ∣ Nat.card Y := ⟨Nat.card N * 3, by rw [← hcard]; ring⟩
      rw [← hcardN] at h5Y
      exact (Nat.Coprime.dvd_mul_right (by norm_num)).mp h5Y
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
    have hxE : ((x : Y) : Perm (Fin 9)) ∈ normalizer (E : Set (Perm (Fin 9))) := by
      have hx2 : (x : Y) ∈ (normalizer (E : Set (Perm (Fin 9)))).subgroupOf Y := by
        rw [subgroupOf_normalizer_eq hEY]
        exact x.2
      exact mem_subgroupOf.mp hx2
    refine false_of_orderOf_five (x := ((x : Y) : Perm (Fin 9)))
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]) (Or.inr hE)
      fun r hr => (mem_normalizer_iff.mp hxE r).mp hr

theorem le_normalizer_of_odd_alt {E Y : Subgroup (alternatingGroup (Fin 9))}
    (hE : Nat.card E = 27) (hEfix : ∀ i : Fin 9, ∃ g ∈ E, (g : Perm (Fin 9)) i ≠ i)
    (hY : Odd (Nat.card Y)) (hEY : E ≤ Y) :
    Y ≤ normalizer (E : Set (alternatingGroup (Fin 9))) := by
  let f := (alternatingGroup (Fin 9)).subtype
  have hinj : Function.Injective f := (alternatingGroup (Fin 9)).subtype_injective
  have key := le_normalizer_of_odd (E := E.map f) (Y := Y.map f)
    (by rwa [card_map_of_injective hinj])
    (fun i => by
      obtain ⟨g, hg, hgi⟩ := hEfix i
      exact ⟨f g, ⟨g, hg, rfl⟩, hgi⟩)
    (by rwa [card_map_of_injective hinj]) (map_mono hEY)
  intro y hy
  have h : y ∈ (normalizer ((E.map f : Subgroup _) : Set (Perm (Fin 9)))).comap f :=
    key ⟨y, hy, rfl⟩
  rwa [comap_normalizer_eq_of_le_range (by rintro _ ⟨g, -, rfl⟩; exact ⟨g, rfl⟩),
    comap_map_eq_self_of_injective hinj] at h

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPerm
