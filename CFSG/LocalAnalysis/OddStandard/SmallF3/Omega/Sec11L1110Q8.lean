module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L1110Defs
public import Mathlib.Tactic.Group
public import Mathlib.Data.ZMod.QuotientGroup


public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {E : Type} [Group E] {z : E} {Q1 Q2 : Subgroup E}

theorem Sec11Q8Pair.symm (P : Sec11Q8Pair z Q1 Q2) : Sec11Q8Pair z Q2 Q1 where
  z_sq := P.z_sq
  z_ne := P.z_ne
  z_mem1 := P.z_mem2
  z_mem2 := P.z_mem1
  comm a ha b hb := (P.comm b hb a ha).symm
  inf x h2 h1 := P.inf x h1 h2
  elem1 := P.elem2
  elem2 := P.elem1
  center1 := P.center2
  center2 := P.center1
  invol1 := P.invol2
  invol2 := P.invol1
  card1 := P.card2
  card2 := P.card1

theorem Sec11Q8Pair.exists_mul_of_mem_sup (P : Sec11Q8Pair z Q1 Q2) {x : E} (hx : x ∈ Q1 ⊔ Q2) :
    ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b := by
  let S : Subgroup E :=
    { carrier := {x | ∃ a ∈ Q1, ∃ b ∈ Q2, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [P.comm a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← P.comm a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : Q1 ⊔ Q2 ≤ S := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

theorem Sec11Q8Pair.mem_zpowers_iff (P : Sec11Q8Pair z Q1 Q2) {x : E} :
    x ∈ zpowers z ↔ x = 1 ∨ x = z := by
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← hk]
    have h2 : z ^ (2 : ℤ) = 1 := by
      have h2' : z ^ ((2 : ℕ) : ℤ) = 1 := by rw [zpow_natCast, pow_two, P.z_sq]
      exact h2'
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left; rw [h]; exact zpow_zero z
    · right; rw [h]; exact zpow_one z
  · rintro (hx | hx)
    · rw [hx]; exact one_mem _
    · rw [hx]; exact Subgroup.mem_zpowers z

theorem Sec11Q8Pair.z_central1 (P : Sec11Q8Pair z Q1 Q2) {x : E} (hx : x ∈ Q1) :
    x * z = z * x := by
  have hmem : x * z * x⁻¹ * z⁻¹ ∈ zpowers z := (P.elem1 x hx z P.z_mem1).1
  have hz : x * z * x⁻¹ = z := by
    rcases P.mem_zpowers_iff.mp hmem with h | h
    · calc x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
        _ = 1 * z := by rw [h]
        _ = z := by simp
    · exfalso
      apply P.z_ne
      have h1 : x * z * x⁻¹ = 1 := by
        calc x * z * x⁻¹ = (x * z * x⁻¹ * z⁻¹) * z := by group
          _ = z * z := by rw [h]
          _ = 1 := P.z_sq
      calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
        _ = x⁻¹ * 1 * x := by rw [h1]
        _ = 1 := by group
  calc x * z = x * z * x⁻¹ * x := by group
    _ = z * x := by rw [hz]

theorem Sec11Q8Pair.zpowers_central1 (P : Sec11Q8Pair z Q1 Q2) {w x : E}
    (hw : w ∈ zpowers z) (hx : x ∈ Q1) : w * x = x * w := by
  rcases P.mem_zpowers_iff.mp hw with h | h
  · rw [h]; simp
  · rw [h]; exact (P.z_central1 hx).symm

theorem Sec11Q8Pair.comm_ne_of_commutator_eq_z (P : Sec11Q8Pair z Q1 Q2) {u v : E}
    (hu : u ∈ Q1) (hv : v ∈ Q1) (h : u * v * u⁻¹ * v⁻¹ = z) : u * v ≠ v * u := by
  intro hc
  apply P.z_ne
  rw [← h, hc]
  group

theorem Sec11Q8Pair.not_mem_zpowers_of_comm_ne (P : Sec11Q8Pair z Q1 Q2) {u v : E}
    (hu : u ∈ Q1) (hv : v ∈ Q1) (hne : u * v ≠ v * u) :
    u ∉ zpowers z ∧ v ∉ zpowers z := by
  constructor
  · intro hu'
    exact hne (P.zpowers_central1 hu' hv)
  · intro hv'
    exact hne (P.zpowers_central1 hv' hu).symm

theorem Sec11Q8Pair.exists_outside1 (P : Sec11Q8Pair z Q1 Q2) : ∃ a ∈ Q1, a ∉ zpowers z := by
  by_contra h
  push Not at h
  have hcardz : Nat.card ↥(zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (p := 2) (by rw [pow_two, P.z_sq]) P.z_ne
  haveI : Finite ↥(zpowers z) := Nat.finite_of_card_ne_zero (by rw [hcardz]; norm_num)
  have hle : Q1 ≤ zpowers z := fun a ha => h a ha
  have hcard := Subgroup.card_le_of_le hle
  rw [P.card1, hcardz] at hcard
  omega

theorem Sec11Q8Pair.sq_eq1 (P : Sec11Q8Pair z Q1 Q2) {a : E} (ha : a ∈ Q1) (hna : a ∉ zpowers z) :
    a * a = z := by
  have hmem : a * a ∈ zpowers z := (P.elem1 a ha a ha).2
  rcases P.mem_zpowers_iff.mp hmem with h | h
  · exact absurd (P.invol1 a ha h) hna
  · exact h

theorem Sec11Q8Pair.exists_gen1 (P : Sec11Q8Pair z Q1 Q2) :
    ∃ a ∈ Q1, ∃ b ∈ Q1, a * b * a⁻¹ * b⁻¹ = z ∧ Q1 = Subgroup.closure {a, b} := by
  obtain ⟨b, hb, hbz⟩ := P.exists_outside1
  have hnotc : ¬ ∀ y ∈ Q1, b * y = y * b := fun hc => hbz (P.center1 b hb hc)
  obtain ⟨a, ha, hab⟩ : ∃ a ∈ Q1, b * a ≠ a * b := by
    by_contra h
    push Not at h
    exact hnotc h
  have hab' : a * b ≠ b * a := fun h => hab h.symm
  have hc_mem : a * b * a⁻¹ * b⁻¹ ∈ zpowers z := (P.elem1 a ha b hb).1
  have hc_eq : a * b * a⁻¹ * b⁻¹ = z := by
    rcases P.mem_zpowers_iff.mp hc_mem with h | h
    · exfalso
      apply hab
      have habc : a * b = b * a := by
        calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
          _ = 1 * (b * a) := by rw [h]
          _ = b * a := by simp
      exact habc.symm
    · exact h
  have ha_z : a ∉ zpowers z := by
    intro h
    exact hab' (P.zpowers_central1 h hb)
  have haa : a * a = z := P.sq_eq1 ha ha_z
  have h2 : a ^ 2 = z := by rw [pow_two]; exact haa
  have h4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a ^ 2) * (a ^ 2) := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
      _ = z * z := by rw [h2]
      _ = 1 := P.z_sq
  have hne2 : a ^ 2 ≠ 1 := by rw [h2]; exact P.z_ne
  have horder : orderOf a = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a)
      (by simpa using hne2) (by simpa using h4)
    norm_num at h
    exact h
  have hcard_a : Nat.card ↥(Subgroup.closure ({a} : Set E)) = 4 := by
    rw [← Subgroup.zpowers_eq_closure a, Nat.card_zpowers]
    exact horder
  have hle_ab : Subgroup.closure ({a, b} : Set E) ≤ Q1 := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  haveI hQ1fin : Finite ↥Q1 := Nat.finite_of_card_ne_zero (by rw [P.card1]; norm_num)
  haveI hfinab : Finite ↥(Subgroup.closure ({a, b} : Set E)) :=
    Finite.of_injective (Subgroup.inclusion hle_ab) (Subgroup.inclusion_injective hle_ab)
  have hcard_ab_dvd : Nat.card ↥(Subgroup.closure ({a, b} : Set E)) ∣ 8 := by
    have h := Subgroup.card_dvd_of_le hle_ab
    rw [P.card1] at h
    exact h
  have hcard_ab_le : Nat.card ↥(Subgroup.closure ({a, b} : Set E)) ≤ 8 :=
    Nat.le_of_dvd (by norm_num) hcard_ab_dvd
  have hb_not_mem_a : b ∉ Subgroup.closure ({a} : Set E) := by
    intro hbcl
    rw [← Subgroup.zpowers_eq_closure a] at hbcl
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbcl
    apply hab
    rw [← hk]
    simpa using zpow_mul_comm a k 1
  have hle_a_ab : Subgroup.closure ({a} : Set E) ≤ Subgroup.closure ({a, b} : Set E) :=
    Subgroup.closure_mono (by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Set.mem_insert a {b})
  have hne_a_ab : Subgroup.closure ({a} : Set E) ≠ Subgroup.closure ({a, b} : Set E) := by
    intro heq
    apply hb_not_mem_a
    rw [heq]
    exact Subgroup.subset_closure (by simp)
  have hlt : Subgroup.closure ({a} : Set E) < Subgroup.closure ({a, b} : Set E) :=
    lt_of_le_of_ne hle_a_ab hne_a_ab
  have hcard_gt : 4 < Nat.card ↥(Subgroup.closure ({a, b} : Set E)) := by
    have h := Subgroup.card_lt_of_lt hlt
    rw [hcard_a] at h
    exact h
  have h4_dvd : 4 ∣ Nat.card ↥(Subgroup.closure ({a, b} : Set E)) := by
    have h := Subgroup.card_dvd_of_le hle_a_ab
    rw [hcard_a] at h
    exact h
  have hcard_eq : Nat.card ↥(Subgroup.closure ({a, b} : Set E)) = 8 := by
    obtain ⟨m, hm⟩ := h4_dvd
    omega
  have hcard_ge : Nat.card ↥Q1 ≤ Nat.card ↥(Subgroup.closure ({a, b} : Set E)) := by
    rw [P.card1, hcard_eq]
  have hQ1_eq : Q1 = Subgroup.closure ({a, b} : Set E) :=
    (Subgroup.eq_of_le_of_card_ge hle_ab hcard_ge).symm
  exact ⟨a, ha, b, hb, hc_eq, hQ1_eq⟩

end CFSG.OddStandard.SmallF3.Omega
