module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84TS4Idx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open Certificates.T84P (Elt mulE oneE M0l Jl)
open Certificates.T84S4 (elt Ml mulT invT jT pow44 gy)

variable {Y : Type} [Group Y] {J : Subgroup Y} {rr : Y → Elt}
  (S : Certificates.T84S4.Facts) (C : Sec8T84TS4Coord J rr)

include S C

noncomputable def sec8t84ts4_Msub : Subgroup Y where
  carrier := {y | rr y ∈ Ml ()}
  mul_mem' {x y} hx hy := by
    obtain ⟨i, hi, rfl⟩ := sec8t84ts4_exists_el S C hx
    obtain ⟨j, hj, rfl⟩ := sec8t84ts4_exists_el S C hy
    obtain ⟨hlt, heq⟩ := sec8t84ts4_el_mul S C hi hj
    show rr (sec8t84ts4_el S C i * sec8t84ts4_el S C j) ∈ Ml ()
    rw [← heq]
    exact sec8t84ts4_rr_mem_Ml S C hlt
  one_mem' := by
    show rr 1 ∈ Ml ()
    rw [← sec8t84ts4_el_zero S C]
    exact sec8t84ts4_rr_mem_Ml S C (by norm_num)
  inv_mem' {x} hx := by
    obtain ⟨i, hi, rfl⟩ := sec8t84ts4_exists_el S C hx
    obtain ⟨hlt, heq⟩ := sec8t84ts4_el_inv S C hi
    show rr (sec8t84ts4_el S C i)⁻¹ ∈ Ml ()
    rw [heq]
    exact sec8t84ts4_rr_mem_Ml S C hlt

private theorem sec8t84ts4_conj_fwd {i : ℕ} (hi : i < 192) {h : Y} (hh : h ∈ J) :
    sec8t84ts4_el S C i * h * (sec8t84ts4_el S C i)⁻¹ ∈ J := by
  obtain ⟨j, hj, rfl⟩ := sec8t84ts4_exists_el S C (sec8t84ts4_J_rr S C hh)
  have hjT : jT j = true := (sec8t84ts4_el_J S C hj).mp hh
  have h1 := S.norm i hi j hj hjT
  obtain ⟨hij, heij⟩ := sec8t84ts4_el_mul S C hi hj
  obtain ⟨hinv, hinvEq⟩ := sec8t84ts4_el_inv S C hi
  obtain ⟨hk, hkEq⟩ := sec8t84ts4_el_mul S C hij hinv
  rw [hinvEq, ← heij, ← hkEq]
  exact (sec8t84ts4_el_J S C hk).mpr h1

theorem sec8t84ts4_el_normalizer {i : ℕ} (hi : i < 192) :
    sec8t84ts4_el S C i ∈ normalizer (J : Set Y) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro h
  refine ⟨fun hh => sec8t84ts4_conj_fwd S C hi hh, fun hh => ?_⟩
  obtain ⟨hinv, hinvEq⟩ := sec8t84ts4_el_inv S C hi
  have h1 := sec8t84ts4_conj_fwd S C hinv hh
  rw [← hinvEq, inv_inv] at h1
  have h2 : (sec8t84ts4_el S C i)⁻¹ * (sec8t84ts4_el S C i * h * (sec8t84ts4_el S C i)⁻¹) *
      sec8t84ts4_el S C i = h := by group
  rwa [h2] at h1

theorem sec8t84ts4_odd_rr {g : Y} (hg : g ∈ normalizer (J : Set Y)) (hodd : Odd (orderOf g)) :
    rr g ∈ Ml () := by
  have h5760 : orderOf g ∣ 128 * 45 := by
    have h := orderOf_dvd_natCard g
    rw [C.card] at h
    exact h
  have hcop : Nat.Coprime (orderOf g) 128 := by
    have h2 : Nat.Coprime (orderOf g) 2 := Nat.coprime_two_right.mpr hodd
    simpa using Nat.Coprime.pow_right 7 h2
  have hdvd : orderOf g ∣ 45 := Nat.Coprime.dvd_of_dvd_mul_left hcop h5760
  have hg45 : g ^ 45 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hg44 : g ^ 44 = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hg45)
  have hp : pow44 (rr g) = rr (g ^ 44) := by
    have key : ∀ a b : ℕ, mulE (rr (g ^ a)) (rr (g ^ b)) = rr (g ^ (a + b)) := by
      intro a b
      rw [← C.mul, ← pow_add]
    have h1 : rr g = rr (g ^ 1) := by rw [pow_one]
    simp only [pow44]
    rw [h1]
    simp only [key]
  refine S.odd (rr g) (C.mem g) ?_ ?_
  · have h1 : g * g ^ 44 = 1 := by rw [← pow_succ']; exact hg45
    rw [hp, ← C.mul, h1, C.one]
  · intro i hi
    obtain ⟨hi192, hiJ⟩ := S.jg i hi
    have hJi : sec8t84ts4_el S C i ∈ J :=
      (C.J_iff _).mpr (by rw [sec8t84ts4_rr_el S C hi192]; exact hiJ)
    have hconj : g * sec8t84ts4_el S C i * g⁻¹ ∈ J :=
      ((Subgroup.mem_set_normalizer_iff.mp hg) _).mp hJi
    rw [hp, ← sec8t84ts4_rr_el S C hi192, ← C.mul, ← C.mul, hg44]
    exact (C.J_iff _).mp hconj

theorem sec8t84ts4_twoRes_iff (y : Y) :
    y ∈ twoRes (normalizer (J : Set Y)) ↔ rr y ∈ Ml () := by
  constructor
  · intro hy
    have hle : twoRes (normalizer (J : Set Y)) ≤ sec8t84ts4_Msub S C := by
      rw [twoRes]
      refine (Subgroup.closure_le _).mpr ?_
      rintro g ⟨hg, hodd⟩
      exact sec8t84ts4_odd_rr S C hg hodd
    exact hle hy
  · intro hy
    obtain ⟨i, hi, rfl⟩ := sec8t84ts4_exists_el S C hy
    have hgen : ∀ k, k < 192 → mulT (mulT k k) k = 0 →
        sec8t84ts4_el S C k ∈ twoRes (normalizer (J : Set Y)) := by
      intro k hk h0
      refine Subgroup.subset_closure ⟨sec8t84ts4_el_normalizer S C hk, ?_⟩
      obtain ⟨h1, e1⟩ := sec8t84ts4_el_mul S C hk hk
      obtain ⟨h2, e2⟩ := sec8t84ts4_el_mul S C h1 hk
      rw [h0, sec8t84ts4_el_zero S C, e1] at e2
      have h3 : sec8t84ts4_el S C k ^ 3 = 1 := by
        rw [pow_three']
        exact e2.symm
      exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)
    obtain ⟨hgy, hgy3, hall⟩ := S.gen3
    rcases hall i hi with h | h
    · exact hgen i hi h
    · obtain ⟨hig, eig⟩ := sec8t84ts4_el_mul S C hi hgy
      have h1 := hgen (mulT i gy) hig h
      have h2 := hgen gy hgy hgy3
      have h3 : sec8t84ts4_el S C i =
          sec8t84ts4_el S C (mulT i gy) * (sec8t84ts4_el S C gy)⁻¹ := by
        rw [eig]
        group
      rw [h3]
      exact mul_mem h1 (inv_mem h2)

theorem sec8t84ts4_card_of {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) :
    Nat.card ↥M = 192 := by
  have hb : Function.Bijective (fun i : Fin 192 =>
      (⟨sec8t84ts4_el S C i.val, (hM _).mpr (sec8t84ts4_rr_mem_Ml S C i.2)⟩ : ↥M)) := by
    constructor
    · intro i j hij
      exact Fin.ext (sec8t84ts4_el_inj S C i.2 j.2 (congrArg Subtype.val hij))
    · intro x
      obtain ⟨i, hi, hix⟩ := sec8t84ts4_exists_el S C ((hM _).mp x.2)
      exact ⟨⟨i, hi⟩, Subtype.ext hix⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hb), Nat.card_fin]

theorem sec8t84ts4_clause1 : J ≤ twoRes (normalizer (J : Set Y)) :=
  fun _ hx => (sec8t84ts4_twoRes_iff S C _).mpr (sec8t84ts4_J_rr S C hx)

theorem sec8t84ts4_clause2 {M : Subgroup Y} (hM : ∀ y, y ∈ M ↔ rr y ∈ Ml ()) :
    ∀ y ∈ M, (∃ k : ℕ, orderOf y = 3 ^ k) → y ≠ 1 →
      orderOf y = 3 ∧ ∀ u ∈ J, y * u = u * y → u = 1 := by
  rintro y hy ⟨k, hk⟩ hy1
  have hdvd : orderOf y ∣ 192 := by
    have h := Subgroup.orderOf_dvd_natCard M hy
    rwa [sec8t84ts4_card_of S C hM] at h
  have hord : orderOf y = 3 := by
    obtain rfl | rfl | hge : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
    · exact absurd (orderOf_eq_one_iff.mp hk) hy1
    · simpa using hk
    · exfalso
      rw [hk] at hdvd
      have h9 : 9 ∣ 192 := (pow_dvd_pow 3 hge).trans hdvd
      omega
  refine ⟨hord, ?_⟩
  obtain ⟨i, hi, rfl⟩ := sec8t84ts4_exists_el S C ((hM y).mp hy)
  have h3 : sec8t84ts4_el S C i ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hy1 (sec8t84ts4_el_zero S C)
  have hcube : mulT (mulT i i) i = 0 := by
    obtain ⟨h1, e1⟩ := sec8t84ts4_el_mul S C hi hi
    obtain ⟨h2, e2⟩ := sec8t84ts4_el_mul S C h1 hi
    apply sec8t84ts4_el_inj S C h2 (by norm_num)
    rw [e2, e1, sec8t84ts4_el_zero S C]
    rw [← pow_three']
    exact h3
  intro u hu hcomm
  obtain ⟨j, hj, rfl⟩ := sec8t84ts4_exists_el S C (sec8t84ts4_J_rr S C hu)
  have hjT : jT j = true := (sec8t84ts4_el_J S C hj).mp hu
  have hmm : mulT i j = mulT j i := by
    obtain ⟨h1, e1⟩ := sec8t84ts4_el_mul S C hi hj
    obtain ⟨h2, e2⟩ := sec8t84ts4_el_mul S C hj hi
    exact sec8t84ts4_el_inj S C h1 h2 (by rw [e1, e2, hcomm])
  rw [S.fpf i hi hi0 hcube j hj hjT hmm, sec8t84ts4_el_zero S C]

end CFSG.OddStandard.SmallF3.Omega
