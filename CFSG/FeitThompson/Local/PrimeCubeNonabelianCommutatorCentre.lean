module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement

variable {p : ℕ} {B : Type*} [Group B] {T : Subgroup B}

private theorem finite_of_card_eq_prime_pow {A : Type*} {n : ℕ} (hp : p.Prime)
    (hA : Nat.card A = p ^ n) : Finite A :=
  Nat.finite_of_card_ne_zero (by rw [hA]; exact pow_ne_zero _ hp.ne_zero)

private theorem pow_eq_one_of_card_eq_prime_sq {A : Type*} [Group A] (hp : p.Prime)
    (hA : Nat.card A = p ^ 2) (hcyc : ¬ IsCyclic A) (x : A) : x ^ p = 1 := by
  have : Finite A := finite_of_card_eq_prime_pow hp hA
  obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow hp).mp (hA ▸ orderOf_dvd_natCard x)
  interval_cases k
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hkx]; simp)
  · exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hkx, pow_one])
  · exact absurd (isCyclic_of_orderOf_eq_card x (by rw [hkx, hA])) hcyc

private theorem isMulCommutative_of_two_le_center (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    {k : ℕ} (hk : 2 ≤ k) (hkc : Nat.card (center B) = p ^ k) : IsMulCommutative B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  have hmul : Nat.card B = Nat.card (B ⧸ center B) * Nat.card (center B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  set m := Nat.card (B ⧸ center B) with hm
  have hpk : m * p ^ k = p ^ 3 := by rw [← hkc, ← hmul, hB]
  have hdvd : m * p ^ 2 ∣ p * p ^ 2 := by
    refine ⟨p ^ (k - 2), ?_⟩
    have h2 : p ^ k = p ^ 2 * p ^ (k - 2) := by rw [← pow_add]; congr 1; omega
    calc p * p ^ 2 = p ^ 3 := by ring
      _ = m * p ^ k := hpk.symm
      _ = m * p ^ 2 * p ^ (k - 2) := by rw [h2]; ring
  have hmp : m ∣ p := (Nat.mul_dvd_mul_iff_right (pow_pos hp.pos 2)).mp hdvd
  have : IsCyclic (B ⧸ center B) := by
    rcases (Nat.dvd_prime hp).mp hmp with h | h
    · have : Subsingleton (B ⧸ center B) := (Nat.card_eq_one_iff_unique.mp h).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card h
  exact isMulCommutative_of_isCyclic_quotient_center_self B

theorem card_center_of_card_eq_prime_cube (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) : Nat.card (center B) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  obtain ⟨k, hk0, hkc⟩ := exists_natCard_center_eq_pow hp hB (by norm_num)
  have hdvd : p ^ k ∣ p ^ 3 := by rw [← hkc, ← hB]; exact (center B).card_subgroup_dvd_card
  have hk3 : k ≤ 3 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  rcases Nat.lt_or_ge k 2 with h | h
  · have hk1 : k = 1 := by omega
    rw [hkc, hk1, pow_one]
  · exact absurd (isMulCommutative_of_two_le_center hp hB h hkc) hnab

theorem card_quotient_center_of_card_eq_prime_cube (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) : Nat.card (B ⧸ center B) = p ^ 2 := by
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  have hmul : Nat.card B = Nat.card (B ⧸ center B) * Nat.card (center B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hB, card_center_of_card_eq_prime_cube hp hB hnab,
    show p ^ 3 = p ^ 2 * p from by ring] at hmul
  exact (Nat.eq_of_mul_eq_mul_right hp.pos hmul).symm

theorem commutator_eq_center_of_card_eq_prime_cube (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) : commutator B = center B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  have hcomm : IsMulCommutative (B ⧸ center B) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
      (card_quotient_center_of_card_eq_prime_cube hp hB hnab)
  have hle : commutator B ≤ center B :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcomm
  have hne : commutator B ≠ ⊥ := fun h => hnab ((commutator_eq_bot_iff B).mp h)
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hdvd : Nat.card (commutator B) ∣ p := by
    rw [← card_center_of_card_eq_prime_cube hp hB hnab]; exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.mp h) hne
  · rw [h, card_center_of_card_eq_prime_cube hp hB hnab]

theorem card_commutator_of_card_eq_prime_cube (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) : Nat.card (commutator B) = p := by
  rw [commutator_eq_center_of_card_eq_prime_cube hp hB hnab,
    card_center_of_card_eq_prime_cube hp hB hnab]

theorem pow_eq_one_quotient_center_of_card_eq_prime_cube (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (x : B ⧸ center B) : x ^ p = 1 :=
  pow_eq_one_of_card_eq_prime_sq hp (card_quotient_center_of_card_eq_prime_cube hp hB hnab)
    (fun _ => hnab (isMulCommutative_of_isCyclic_quotient_center_self B)) x

theorem nonempty_mulEquiv_quotient_center_of_card_eq_prime_cube (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hnab : ¬ IsMulCommutative B) :
    Nonempty ((B ⧸ center B) ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : IsMulCommutative (B ⧸ center B) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p)
      (card_quotient_center_of_card_eq_prime_cube hp hB hnab)
  let _ : CommGroup (B ⧸ center B) := IsMulCommutative.instCommGroup
  exact nonempty_mulEquiv_pi_of_exponent hp
    (pow_eq_one_quotient_center_of_card_eq_prime_cube hp hB hnab)
    (card_quotient_center_of_card_eq_prime_cube hp hB hnab)

theorem card_eq_prime_sq_of_mulEquiv (e : T ≃* (Fin 2 → Multiplicative (ZMod p))) :
    Nat.card T = p ^ 2 := by
  rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]

theorem centralizer_eq_self_of_card_eq_prime_sq (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (hT : Nat.card T = p ^ 2) : centralizer (T : Set B) = T := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  have hcommT : IsMulCommutative T := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hT
  have hle : T ≤ centralizer (T : Set B) := le_centralizer_iff_isMulCommutative.mpr hcommT
  obtain ⟨k, hk3, hkc⟩ :=
    (Nat.dvd_prime_pow hp).mp (hB ▸ Subgroup.card_subgroup_dvd_card (centralizer (T : Set B)))
  have h2k : 2 ≤ k := by
    have : p ^ 2 ∣ p ^ k := by rw [← hT, ← hkc]; exact Subgroup.card_dvd_of_le hle
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this
  interval_cases k
  · exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hkc, hT])).symm
  · exfalso
    have htop : centralizer (T : Set B) = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hkc, hB])
    have hsub : T ≤ center B := centralizer_eq_top_iff_subset.mp htop
    have hdvd2 : p ^ 2 ∣ p ^ 1 := by
      rw [pow_one, ← hT, ← card_center_of_card_eq_prime_cube hp hB hnab]
      exact Subgroup.card_dvd_of_le hsub
    have := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd2
    omega

theorem center_le_of_card_eq_prime_sq (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (hT : Nat.card T = p ^ 2) : center B ≤ T := by
  rw [← centralizer_eq_self_of_card_eq_prime_sq hp hB hnab hT]
  exact Subgroup.center_le_centralizer _

theorem centralizer_eq_self_of_isElementaryAbelianPlane (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (e : T ≃* (Fin 2 → Multiplicative (ZMod p))) :
    centralizer (T : Set B) = T :=
  centralizer_eq_self_of_card_eq_prime_sq hp hB hnab (card_eq_prime_sq_of_mulEquiv e)

theorem center_le_of_isElementaryAbelianPlane (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (e : T ≃* (Fin 2 → Multiplicative (ZMod p))) :
    center B ≤ T :=
  center_le_of_card_eq_prime_sq hp hB hnab (card_eq_prime_sq_of_mulEquiv e)

theorem zpowers_sup_center_eq_of_card_eq_prime_sq (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (hT : Nat.card T = p ^ 2) {z : B} (hzT : z ∈ T)
    (hzZ : z ∉ center B) : zpowers z ⊔ center B = T := by
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  set S : Subgroup B := zpowers z ⊔ center B with hS
  have hSle : S ≤ T :=
    sup_le (zpowers_le.mpr hzT) (center_le_of_card_eq_prime_sq hp hB hnab hT)
  have hZS : center B ≤ S := le_sup_right
  have hne : center B ≠ S :=
    fun h => hzZ (h ▸ (le_sup_left : zpowers z ≤ S) (Subgroup.mem_zpowers z))
  obtain ⟨j, hj2, hjc⟩ := (Nat.dvd_prime_pow hp).mp (hT ▸ Subgroup.card_dvd_of_le hSle)
  have hZcard : Nat.card (center B) = p := card_center_of_card_eq_prime_cube hp hB hnab
  have h1j : 1 ≤ j := by
    have : p ^ 1 ∣ p ^ j := by rw [← hjc, ← hZcard, pow_one]; exact Subgroup.card_dvd_of_le hZS
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp this
  have hj1 : j ≠ 1 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hZS (by rw [hjc, h, pow_one, hZcard]))
  have hj : j = 2 := by omega
  exact Subgroup.eq_of_le_of_card_ge hSle (by rw [hT, hjc, hj])

theorem zpowers_commutatorElement_eq_center (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (hT : Nat.card T = p ^ 2) {y z : B} (hy : y ∉ T)
    (hzT : z ∈ T) (hzZ : z ∉ center B) : zpowers ⁅y, z⁆ = center B := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite B := finite_of_card_eq_prime_pow hp hB
  have hZcard : Nat.card (center B) = p := card_center_of_card_eq_prime_cube hp hB hnab
  have hmem : ⁅y, z⁆ ∈ center B := by
    rw [← commutator_eq_center_of_card_eq_prime_cube hp hB hnab, commutator_def]
    exact Subgroup.commutator_mem_commutator (mem_top y) (mem_top z)
  have hne : ⁅y, z⁆ ≠ 1 := by
    intro h
    have hcz : Commute y z := commutatorElement_eq_one_iff_commute.mp h
    have hcl : Subgroup.closure ({z} ∪ (center B : Set B)) = T := by
      rw [Subgroup.closure_union, ← zpowers_eq_closure, Subgroup.closure_eq,
        zpowers_sup_center_eq_of_card_eq_prime_sq hp hB hnab hT hzT hzZ]
    have hyc : y ∈ centralizer (T : Set B) := by
      rw [← hcl, Subgroup.centralizer_closure]
      refine mem_centralizer_iff.mpr ?_
      rintro g (hg | hg)
      · rw [Set.mem_singleton_iff] at hg; rw [hg]; exact hcz.symm.eq
      · exact (Subgroup.mem_center_iff.mp hg y).symm
    exact hy (centralizer_eq_self_of_card_eq_prime_sq hp hB hnab hT ▸ hyc)
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) ?_
  rcases (Nat.dvd_prime hp).mp
      (hZcard ▸ Subgroup.card_dvd_of_le (zpowers_le.mpr hmem)) with h | h
  · exact absurd (by simpa using Subgroup.card_eq_one.mp h) hne
  · rw [h, hZcard]

theorem zpowers_inv_mul_inv_mul_mul_eq_center (hp : p.Prime) (hB : Nat.card B = p ^ 3)
    (hnab : ¬ IsMulCommutative B) (hT : Nat.card T = p ^ 2) {y z : B} (hy : y ∉ T)
    (hzT : z ∈ T) (hzZ : z ∉ center B) : zpowers (y⁻¹ * z⁻¹ * y * z) = center B := by
  have hyz : y⁻¹ * z⁻¹ * y * z = ⁅y⁻¹, z⁻¹⁆ := by rw [commutatorElement_def]; group
  rw [hyz]
  exact zpowers_commutatorElement_eq_center hp hB hnab hT
    (fun h => hy (by simpa using T.inv_mem h)) (T.inv_mem hzT)
    (fun h => hzZ (by simpa using (center B).inv_mem h))

theorem zpowers_commutatorElement_eq_center_of_isElementaryAbelianPlane (hp : p.Prime)
    (hB : Nat.card B = p ^ 3) (hnab : ¬ IsMulCommutative B)
    (e : T ≃* (Fin 2 → Multiplicative (ZMod p))) {y z : B} (hy : y ∉ T) (hzT : z ∈ T)
    (hzZ : z ∉ center B) : zpowers ⁅y, z⁆ = center B :=
  zpowers_commutatorElement_eq_center hp hB hnab (card_eq_prime_sq_of_mulEquiv e) hy hzT hzZ

end

end CFSG.FeitThompson
