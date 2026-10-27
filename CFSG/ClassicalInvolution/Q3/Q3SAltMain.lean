module

public import CFSG.ClassicalInvolution.Q3.Q3SAltWit
public import CFSG.ClassicalInvolution.Q3.Q3SCriteria
public import CFSG.ClassicalInvolution.Q3.Q3SAlt

public section

namespace CFSG.ClassicalInvolution.Q3

open Equiv

section Standard

variable {n : ℕ}

@[expose] def zStd (n : ℕ) (h : 8 ≤ n) : alternatingGroup (Fin n) :=
  ⟨ext8 n h z0, Perm.mem_alternatingGroup.2 (by rw [sign_ext8, z0_sign])⟩

@[expose] def wit1A (n : ℕ) (h : 8 ≤ n) : alternatingGroup (Fin n) :=
  ⟨ext8 n h wit1, Perm.mem_alternatingGroup.2 (by
    rw [sign_ext8]
    have h3 : Perm.sign wit1 ^ 3 = 1 := by rw [← map_pow, wit1_cube, map_one]
    rcases Int.units_eq_one_or (Perm.sign wit1) with h1 | h1
    · exact h1
    · rw [h1] at h3; exact absurd h3 (by decide))⟩

@[expose] def wit2A (n : ℕ) (h : 8 ≤ n) : alternatingGroup (Fin n) :=
  ⟨ext8 n h wit2, Perm.mem_alternatingGroup.2 (by
    rw [sign_ext8]
    have h3 : Perm.sign wit2 ^ 3 = 1 := by rw [← map_pow, wit2_cube, map_one]
    rcases Int.units_eq_one_or (Perm.sign wit2) with h1 | h1
    · exact h1
    · rw [h1] at h3; exact absurd h3 (by decide))⟩

theorem wit1A_mem (h : 8 ≤ n) :
    wit1A n h ∈ Subgroup.centralizer ({zStd n h} : Set (alternatingGroup (Fin n))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  change ext8 n h wit1 * ext8 n h z0 = ext8 n h z0 * ext8 n h wit1
  rw [← map_mul, ← map_mul, wit1_comm]

theorem wit2A_mem (h : 8 ≤ n) :
    wit2A n h ∈ Subgroup.centralizer ({zStd n h} : Set (alternatingGroup (Fin n))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Subtype.ext ?_
  change ext8 n h wit2 * ext8 n h z0 = ext8 n h z0 * ext8 n h wit2
  rw [← map_mul, ← map_mul, wit2_comm]

theorem wit1A_cube (h : 8 ≤ n) : wit1A n h ^ 3 = 1 := Subtype.ext (by
  change (ext8 n h wit1) ^ 3 = 1
  rw [← map_pow, wit1_cube, map_one])

theorem wit2A_cube (h : 8 ≤ n) : wit2A n h ^ 3 = 1 := Subtype.ext (by
  change (ext8 n h wit2) ^ 3 = 1
  rw [← map_pow, wit2_cube, map_one])

theorem witA_prod_sq (h : 8 ≤ n) : (wit1A n h * wit2A n h) ^ 2 = 1 := Subtype.ext (by
  change (ext8 n h wit1 * ext8 n h wit2) ^ 2 = 1
  rw [← map_mul, ← map_pow, wit_prod_sq, map_one])

theorem witA_prod_ne_one (h : 8 ≤ n) : wit1A n h * wit2A n h ≠ 1 := fun h1 =>
  wit_prod_ne_one (ext8_injective n h (by
    have := congrArg Subtype.val h1
    change ext8 n h wit1 * ext8 n h wit2 = 1 at this
    rw [← map_mul] at this
    rw [this, map_one]))

theorem witA_prod_ne_z (h : 8 ≤ n) : wit1A n h * wit2A n h ≠ zStd n h := fun h1 =>
  wit_prod_ne_z0 (ext8_injective n h (by
    have := congrArg Subtype.val h1
    change ext8 n h wit1 * ext8 n h wit2 = ext8 n h z0 at this
    rw [← map_mul] at this
    exact this))

theorem cycleType_zStd (h : 8 ≤ n) :
    ((zStd n h : alternatingGroup (Fin n)) : Perm (Fin n)).cycleType = Multiset.replicate 4 2 := by
  have h2 : orderOf z0 = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact z0_sq) z0_ne_one
  obtain ⟨m, hm, hc⟩ := cycleType_eq_replicate_two h2
  have : m = 4 := by rw [z0_support_card] at hc; omega
  change (ext8 n h z0).cycleType = _
  rw [cycleType_ext8, hm, this]

theorem card_centralizer_zStd_dvd (h8 : 8 ≤ n) :
    Nat.card (Subgroup.centralizer ({zStd n h8} : Set (alternatingGroup (Fin n)))) ∣
      (n - 8).factorial * 384 := by
  classical
  have hcard := Perm.nat_card_centralizer
    ((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n))
  rw [cycleType_zStd h8] at hcard
  have hS : Nat.card (Subgroup.centralizer
      ({((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n))} : Set (Perm (Fin n)))) =
        (n - 8).factorial * 384 := by
    rw [hcard]
    simp
    ring
  let f : Subgroup.centralizer ({zStd n h8} : Set (alternatingGroup (Fin n))) →*
      Subgroup.centralizer
        ({((zStd n h8 : alternatingGroup (Fin n)) : Perm (Fin n))} : Set (Perm (Fin n))) :=
    (((alternatingGroup (Fin n)).subtype.comp (Subgroup.centralizer _).subtype).codRestrict _
      (fun g => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := Subgroup.mem_centralizer_singleton_iff.mp g.2
        exact congrArg Subtype.val this))
  have hf : Function.Injective f := fun a b hab => by
    have h0 := congrArg Subtype.val hab
    have h1 : (((a : alternatingGroup (Fin n)) : Perm (Fin n))) =
        (((b : alternatingGroup (Fin n)) : Perm (Fin n))) := h0
    exact Subtype.ext (Subtype.ext h1)
  have hdvd := Subgroup.card_dvd_of_injective f hf
  rwa [hS] at hdvd

theorem not_nine_dvd_card_centralizer_zStd (h8 : 8 ≤ n) (h10 : n ≤ 10) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer ({zStd n h8} : Set (alternatingGroup (Fin n)))) := by
  intro h9
  have := h9.trans (card_centralizer_zStd_dvd h8)
  interval_cases n <;> simp at this

theorem exists_conj_zStd (h : 8 ≤ n) {z : alternatingGroup (Fin n)} (hz : orderOf z = 2)
    (hs : ((z : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 8) :
    ∃ c : Perm (Fin n), c * (z : Perm (Fin n)) * c⁻¹ = ((zStd n h : alternatingGroup (Fin n)) :
      Perm (Fin n)) := by
  have hZ : orderOf ((z : alternatingGroup (Fin n)) : Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hz
  obtain ⟨m, hm, hc⟩ := cycleType_eq_replicate_two hZ
  have : m = 4 := by omega
  have hconj : IsConj ((z : alternatingGroup (Fin n)) : Perm (Fin n))
      ((zStd n h : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_zStd h, hm, this]
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  exact ⟨c, hc⟩

theorem noWeakClassical3At_alternating_of_support {z : alternatingGroup (Fin n)} (h8 : 8 ≤ n)
    (h10 : n ≤ 10) (hz : orderOf z = 2)
    (hs : ((z : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 8) :
    NoWeakClassical3At z := by
  obtain ⟨c, hc⟩ := exists_conj_zStd h8 hz hs
  have hez : MulAut.conjNormal (H := alternatingGroup (Fin n)) c z = zStd n h8 :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hc)
  refine NoWeakClassical3At.of_map (MulAut.conjNormal (H := alternatingGroup (Fin n)) c) ?_
  rw [hez]
  exact NoWeakClassical3At.of_witness (not_nine_dvd_card_centralizer_zStd h8 h10)
    (wit1A_mem h8) (wit2A_mem h8) (wit1A_cube h8) (wit2A_cube h8) (witA_prod_sq h8)
    (witA_prod_ne_one h8) (witA_prod_ne_z h8)

theorem IsClassicalMember3.card_support_eq_eight (hn : n ≤ 11)
    {z : alternatingGroup (Fin n)} {L : Subgroup (alternatingGroup (Fin n))}
    (hL : IsClassicalMember3 L z) :
    ((z : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = 8 := by
  have hZ : orderOf ((z : alternatingGroup (Fin n)) : Perm (Fin n)) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hL.orderOf_eq_two
  have hsign : Perm.sign ((z : alternatingGroup (Fin n)) : Perm (Fin n)) = 1 :=
    Perm.mem_alternatingGroup.mp z.2
  obtain ⟨m, -, hc⟩ := even_of_sign_eq_one hZ hsign
  have h8 := hL.eight_le_card_support
  have hle : ((z : alternatingGroup (Fin n)) : Perm (Fin n)).support.card ≤ n := by
    simpa using Finset.card_le_univ ((z : alternatingGroup (Fin n)) : Perm (Fin n)).support
  omega

theorem noWeakClassical3_alternating_of_le_ten (h8 : 8 ≤ n) (h10 : n ≤ 10) :
    NoWeakClassical3 (alternatingGroup (Fin n)) := fun L z hL =>
  noWeakClassical3At_alternating_of_support h8 h10 hL.orderOf_eq_two
    (hL.card_support_eq_eight (by omega)) L hL

end Standard

end CFSG.ClassicalInvolution.Q3
