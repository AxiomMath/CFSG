module

public import CFSG.LargeExtraspecial.S14SMEDefs
public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.LargeExtraspecial.S14C12SmDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

namespace SME

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem mem_Qa_iff (S : Setting G) (h x : G) : x ∈ S.Qa h ↔ h⁻¹ * x * h ∈ S.QG := by
  rw [Setting.Qa_eq_map, mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    convert hy using 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro hx
    refine ⟨h⁻¹ * x * h, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem inv_eq_of_isConj (S : Setting G) {x : G} (hx : IsConj S.z x) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (SmithQ.mul_self_eq_one_of_isConj S hx)

theorem ne_one_of_isConj (S : Setting G) {x : G} (hx : IsConj S.z x) : x ≠ 1 := by
  rintro rfl
  exact S.z_ne_one (isConj_one_left.mp hx)

theorem exists_conj_eq_mul_z [Finite G] (S : Setting G) {c : G} (hc : c ∈ S.QG) (h1 : c ≠ 1)
    (hz : c ≠ S.z) : ∃ q ∈ S.QG, q * c * q⁻¹ = c * S.z := by
  by_contra hno
  push Not at hno
  have hcomm : ∀ y ∈ S.QG, c * y = y * c := by
    intro y hy
    rcases S.commutator_eq_one_or_z hy hc with h | h
    · calc c * y = (y * c * y⁻¹ * c⁻¹)⁻¹ * y * c := by group
        _ = y * c := by rw [h, inv_one, one_mul]
    · exfalso
      apply hno y hy
      calc y * c * y⁻¹ = (y * c * y⁻¹ * c⁻¹) * c := by group
        _ = S.z * c := by rw [h]
        _ = c * S.z := (S.z_comm (S.QG_le_M hc)).symm
  rcases S.eq_one_or_z_of_commute hc hcomm with h | h
  · exact h1 h
  · exact hz h

theorem isConj_of_cl_eq [Finite G] (S : Setting G) {c e : G} (hc : IsConj S.z c)
    (hcQ : c ∈ S.QG) (heQ : e ∈ S.QG) (he1 : e ≠ 1) (hcl : S.cl c = S.cl e) :
    IsConj S.z e := by
  rcases (S.cl_eq_cl_iff hcQ heQ).mp hcl with rfl | rfl
  · exact hc
  · by_cases hcz : c = S.z
    · exact absurd (by rw [hcz, S.z_mul_z]) he1
    · obtain ⟨q, -, hqc⟩ := exists_conj_eq_mul_z S hcQ (ne_one_of_isConj S hc) hcz
      rw [← hqc]
      exact hc.trans (isConj_iff.mpr ⟨q, rfl⟩)

theorem commutator_mem (S : Setting G) (x : G) {q : G} (hq : q ∈ S.QG) :
    x * q * x⁻¹ * q⁻¹ ∈ (⁅zpowers x, S.QG⁆ : Subgroup G) := by
  have h := Subgroup.commutator_mem_commutator (mem_zpowers x) hq
  rwa [commutatorElement_def] at h

theorem sq_eq_one_of_mem_commutator (h34a : SmithE34a) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x : G}
    (hx : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) {g : G}
    (hg : g ∈ (⁅zpowers x, S.QG⁆ : Subgroup G)) : g ^ 2 = 1 := by
  have hx2 : x ^ 2 = 1 := by
    rw [_root_.sq]
    exact SmithQ.mul_self_eq_one_of_isConj S hx
  have hfix : S.fixQt x = S.clSub (S.QG ⊓ centralizer ({x} : Set G)) := by
    by_contra hne
    obtain ⟨y, -, hy⟩ := S.lemma_3_2_1 hxM hne
    apply h34a G S hw hU x hx hxM hxQ
    rw [← hy]
    exact hx.trans (isConj_iff.mpr ⟨y, rfl⟩)
  obtain ⟨hel, -⟩ := S.aschbacher_3_6 hxM hxQ hx2 hfix (S.index_fixQt x hxM)
  have := hel
  exact CFSG.elemPow_eq_one_of_isElementaryAbelian g hg

theorem exists_commutator_of_coset (h34b : SmithE34b) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x x' : G}
    (hx : IsConj S.z x) (hx' : IsConj S.z x') (hxM : x ∈ S.M) (hxQ : x ∉ S.QG)
    (hQ : x⁻¹ * x' ∈ S.QG) : ∃ q ∈ S.QG, x⁻¹ * x' = x * q * x⁻¹ * q⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := h34b G S hw hU x x' hx hx' hxM hxQ hQ
  refine ⟨q⁻¹, S.QG.inv_mem hq, ?_⟩
  rw [inv_inv, inv_eq_of_isConj S hx]
  group

theorem orderOf_mem_of_sq_sq {g : G} (h : (g ^ 2) ^ 2 = 1) :
    orderOf g ∈ ({1, 2, 3, 4} : Set ℕ) := by
  have hd : orderOf g ∣ 4 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul] at h; exact h)
  have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf g := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hd
    norm_num at hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases (orderOf g) <;> simp_all

theorem orderOf_mem_of_pow_two {g : G} (h : g ^ 2 = 1) :
    orderOf g ∈ ({1, 2, 3, 4} : Set ℕ) ∧ orderOf g ≠ 4 := by
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf g := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hd
    norm_num at hd
  refine ⟨?_, by omega⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem orderOf_mem_of_pow_three {g : G} (h : g ^ 3 = 1) :
    orderOf g ∈ ({1, 2, 3, 4} : Set ℕ) ∧ orderOf g ≠ 4 := by
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h
  have hle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf g := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hd
    norm_num at hd
  refine ⟨?_, by omega⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem sq_ne_one_of_orderOf_eq_four {g : G} (h : orderOf g = 4) : g ^ 2 ≠ 1 := by
  intro h2
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h] at this
  norm_num at this

theorem local_of_mem_QG (h34a : SmithE34a) (h24 : SmithE24) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x y : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG) (hyQ : y ∈ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := inv_eq_of_isConj S hx
  have hyi := inv_eq_of_isConj S hy
  have he : (x * y) ^ 2 = x * y * x⁻¹ * y⁻¹ := by
    rw [hxi, hyi, sq]
    simp only [mul_assoc]
  have hsq : ((x * y) ^ 2) ^ 2 = 1 := by
    rw [he]
    exact sq_eq_one_of_mem_commutator h34a S hw hU hx hxM hxQ (commutator_mem S x hyQ)
  refine ⟨orderOf_mem_of_sq_sq hsq, fun h4 => ?_⟩
  have hne := sq_ne_one_of_orderOf_eq_four h4
  obtain ⟨h, rfl⟩ := isConj_iff.mp hy
  have hy' := (mem_Qa_iff S h _).mp (h24 G S hw hU x h hx hxM hxQ hyQ)
  obtain ⟨y', hy'd⟩ : ∃ y', y' = x * (h * S.z * h⁻¹) * x⁻¹ := ⟨_, rfl⟩
  rw [← hy'd] at hy'
  have hy'c : IsConj S.z y' := hy.trans (isConj_iff.mpr ⟨x, hy'd.symm⟩)
  have he' : (x * (h * S.z * h⁻¹)) ^ 2 = y' * (h * S.z * h⁻¹) := by
    rw [he, hy'd, hyi]
  have hy'ne : y' ≠ h * S.z * h⁻¹ := by
    intro heq
    apply hne
    rw [he', heq]
    exact SmithQ.mul_self_eq_one_of_isConj S hy
  have hback : y' = h * (h⁻¹ * y' * h) * h⁻¹ := by group
  have hy''1 : h⁻¹ * y' * h ≠ 1 := by
    intro h1
    apply ne_one_of_isConj S hy'c
    rw [hback, h1]
    group
  have hy''z : h⁻¹ * y' * h ≠ S.z := by
    intro h1
    apply hy'ne
    rw [hback, h1]
  obtain ⟨q, -, hq⟩ := exists_conj_eq_mul_z S hy' hy''1 hy''z
  have hconj : (h * q * h⁻¹) * y' * (h * q * h⁻¹)⁻¹ = y' * (h * S.z * h⁻¹) := by
    have h1 : h * (q * (h⁻¹ * y' * h) * q⁻¹) * h⁻¹ = h * ((h⁻¹ * y' * h) * S.z) * h⁻¹ := by
      rw [hq]
    calc (h * q * h⁻¹) * y' * (h * q * h⁻¹)⁻¹ = h * (q * (h⁻¹ * y' * h) * q⁻¹) * h⁻¹ := by
          group
      _ = h * ((h⁻¹ * y' * h) * S.z) * h⁻¹ := h1
      _ = y' * (h * S.z * h⁻¹) := by group
  rw [he', ← hconj]
  exact hy'c.trans (isConj_iff.mpr ⟨_, rfl⟩)

theorem local_of_not_mem_QG (h34a : SmithE34a) (h34b : SmithE34b) (h23 : SmithE23)
    (h25 : SmithE25) [Finite G] [IsSimpleGroup G] (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {x y : G} (hx : IsConj S.z x)
    (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hxQ : x ∉ S.QG) (hyQ : y ∉ S.QG) :
    orderOf (x * y) ∈ ({1, 2, 3, 4} : Set ℕ) ∧
      (orderOf (x * y) = 4 → IsConj S.z ((x * y) ^ 2)) := by
  have hxi := inv_eq_of_isConj S hx
  have hyi := inv_eq_of_isConj S hy
  by_cases h1 : x * y ∈ S.QG
  · obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset h34b S hw hU hx hy hxM hxQ
      (by rw [hxi]; exact h1)
    have h2 : (x * y) ^ 2 = 1 := by
      rw [show x * y = x⁻¹ * y by rw [hxi], hqe]
      exact sq_eq_one_of_mem_commutator h34a S hw hU hx hxM hxQ (commutator_mem S x hq)
    obtain ⟨hmem, h4⟩ := orderOf_mem_of_pow_two h2
    exact ⟨hmem, fun h => absurd h h4⟩
  rcases h23 G S hw hU x y hx hy hxM hyM hxQ hyQ with h1' | h2 | h3
  · exact absurd h1' h1
  · have hx'c : IsConj S.z (y⁻¹ * x * y) := hx.trans (isConj_iff.mpr ⟨y⁻¹, by group⟩)
    have hx'e : x⁻¹ * (y⁻¹ * x * y) = (x * y) ^ 2 := by
      rw [hxi, hyi, sq]
      simp only [mul_assoc]
    obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset h34b S hw hU hx hx'c hxM hxQ
      (by rw [hx'e]; exact h2)
    rw [hx'e] at hqe
    have hy'c : IsConj S.z (x⁻¹ * y * x) := hy.trans (isConj_iff.mpr ⟨x⁻¹, by group⟩)
    have hy'e : y⁻¹ * (x⁻¹ * y * x) = ((x * y) ^ 2)⁻¹ := by
      rw [sq, mul_inv_rev, mul_inv_rev, hxi, hyi]
      simp only [mul_assoc]
    obtain ⟨q', hq', hqe'⟩ := exists_commutator_of_coset h34b S hw hU hy hy'c hyM hyQ
      (by rw [hy'e]; exact S.QG.inv_mem h2)
    rw [hy'e] at hqe'
    have hcl : S.cl ((x * y) ^ 2) ∈ S.commQt x ⊓ S.commQt y := by
      refine Submodule.mem_inf.mpr ⟨(S.mem_commQt_iff hxM).mpr ⟨q, hq, by rw [hqe]⟩, ?_⟩
      rw [← S.cl_inv h2, hqe']
      exact (S.mem_commQt_iff hyM).mpr ⟨q', hq', rfl⟩
    have hsq : ((x * y) ^ 2) ^ 2 = 1 := by
      rw [hqe]
      exact sq_eq_one_of_mem_commutator h34a S hw hU hx hxM hxQ (commutator_mem S x hq)
    refine ⟨orderOf_mem_of_sq_sq hsq, fun h4 => ?_⟩
    obtain ⟨c, hc, hcQ, hcl'⟩ := (h25 G S hw hU x y hx hy hxM hyM hxQ hyQ h1).1 h2 _ hcl
    exact isConj_of_cl_eq S hc hcQ h2 (sq_ne_one_of_orderOf_eq_four h4) hcl'
  · have hxx := SmithQ.mul_self_eq_one_of_isConj S hx
    have hc1 : IsConj S.z (x * (x * y) ^ 3) := by
      have h : (y * x) * y * (y * x)⁻¹ = x * (x * y) ^ 3 := by
        rw [mul_inv_rev, hxi, hyi, pow_succ, pow_succ, pow_one]
        simp only [← mul_assoc, hxx, one_mul]
      rw [← h]
      exact hy.trans (isConj_iff.mpr ⟨_, rfl⟩)
    have hc2 : IsConj S.z (y * (x * y) ^ 3) := by
      have h : (y * x * y) * x * (y * x * y)⁻¹ = y * (x * y) ^ 3 := by
        rw [mul_inv_rev, mul_inv_rev, hxi, hyi, pow_succ, pow_succ, pow_one]
        simp only [← mul_assoc]
      rw [← h]
      exact hx.trans (isConj_iff.mpr ⟨_, rfl⟩)
    obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset h34b S hw hU hx hc1 hxM hxQ
      (by rw [inv_mul_cancel_left]; exact h3)
    obtain ⟨q', hq', hqe'⟩ := exists_commutator_of_coset h34b S hw hU hy hc2 hyM hyQ
      (by rw [inv_mul_cancel_left]; exact h3)
    rw [inv_mul_cancel_left] at hqe hqe'
    have hbot := (h25 G S hw hU x y hx hy hxM hyM hxQ hyQ h1).2 h3
    have hmem : S.cl ((x * y) ^ 3) ∈ S.commQt x ⊓ S.commQt y :=
      Submodule.mem_inf.mpr ⟨(S.mem_commQt_iff hxM).mpr ⟨q, hq, by rw [hqe]⟩,
        (S.mem_commQt_iff hyM).mpr ⟨q', hq', by rw [hqe']⟩⟩
    rw [hbot] at hmem
    rcases (S.cl_eq_zero_iff h3).mp ((Submodule.mem_bot _).mp hmem) with h31 | h3z
    · obtain ⟨hm, h4⟩ := orderOf_mem_of_pow_three h31
      exact ⟨hm, fun h => absurd h h4⟩
    · refine (h34a G S hw hU x hx hxM hxQ ?_).elim
      have h : x * S.z = x * (x * y) ^ 3 := by rw [h3z]
      rw [h]
      exact hc1

end SME

theorem smithU62LocalInput_of (h34a : SmithE34a) (h34b : SmithE34b) (h23 : SmithE23)
    (h24 : SmithE24) (h25 : SmithE25) : SmithU62LocalInput := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ
  by_cases hyQ : y ∈ S.QG
  · exact SME.local_of_mem_QG h34a h24 S hw hU hx hy hxM hxQ hyQ
  · exact SME.local_of_not_mem_QG h34a h34b h23 h25 S hw hU hx hy hxM hyM hxQ hyQ

end CFSG.LargeExtraspecial.S14
