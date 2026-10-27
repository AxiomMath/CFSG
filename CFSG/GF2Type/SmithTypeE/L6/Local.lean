module

public import CFSG.GF2Type.SmithTypeE.L6.Defs
public import CFSG.GF2Type.SmithTypeE.E6Defs
public import CFSG.LargeExtraspecial.S14SMELocal

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SME (inv_eq_of_isConj commutator_mem orderOf_mem_of_sq_sq
  sq_ne_one_of_orderOf_eq_four mem_Qa_iff ne_one_of_isConj exists_conj_eq_mul_z isConj_of_cl_eq
  orderOf_mem_of_pow_two orderOf_mem_of_pow_three)
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem sq_eq_one_of_mem_commutator (h34a : SmithL6E34a) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {x : G}
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

theorem exists_commutator_of_coset (h34b : SmithL6E34b) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {x x' : G}
    (hx : IsConj S.z x) (hx' : IsConj S.z x') (hxM : x ∈ S.M) (hxQ : x ∉ S.QG)
    (hQ : x⁻¹ * x' ∈ S.QG) : ∃ q ∈ S.QG, x⁻¹ * x' = x * q * x⁻¹ * q⁻¹ := by
  obtain ⟨q, hq, rfl⟩ := h34b G S hw hU x x' hx hx' hxM hxQ hQ
  refine ⟨q⁻¹, S.QG.inv_mem hq, ?_⟩
  rw [inv_inv, inv_eq_of_isConj S hx]
  group

theorem local_of_mem_QG (h34a : SmithL6E34a) (h24 : SmithL6E24) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {x y : G}
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

theorem dihedral_pow_four (S : Setting G) {x y : G} (hx : IsConj S.z x) (hy : IsConj S.z y) :
    (x * y) ^ 2 * x * ((x * y) ^ 2)⁻¹ = x * ((x * y) ^ 4)⁻¹ := by
  have hxi := inv_eq_of_isConj S hx
  have hyi := inv_eq_of_isConj S hy
  have h1 : (x * y) ^ 2 * x = x * ((x * y)⁻¹) ^ 2 := by
    rw [sq, sq, mul_inv_rev, hxi, hyi]
    simp only [mul_assoc]
  rw [h1]
  generalize x * y = r
  group

theorem local_of_not_mem_QG (h34a : SmithL6E34a) (h34b : SmithL6E34b) (h23 : SmithL6E23)
    (h25 : SmithL6E25) (h23f : SmithL6E23Four) [Finite G] [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* PSL(6, ZMod 2))) {x y : G}
    (hx : IsConj S.z x) (hy : IsConj S.z y) (hxM : x ∈ S.M) (hyM : y ∈ S.M) (hxQ : x ∉ S.QG)
    (hyQ : y ∉ S.QG) :
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
  have h25' := h25 G S hw hU x y hx hy hxM hyM hxQ hyQ h1
  by_cases h2 : (x * y) ^ 2 ∈ S.QG
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
    obtain ⟨c, hc, hcQ, hcl'⟩ := h25'.1 h2 _ hcl
    exact isConj_of_cl_eq S hc hcQ h2 (sq_ne_one_of_orderOf_eq_four h4) hcl'
  by_cases h3 : (x * y) ^ 3 ∈ S.QG
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
    have hbot := h25'.2.1 h3
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
  have h4 : (x * y) ^ 4 ∈ S.QG := by
    rcases h23 G S hw hU x y hx hy hxM hyM hxQ hyQ with h | h | h | h
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h
  have hbot := h25'.2.2 h2 h4
  have hcx : IsConj S.z (x * ((x * y) ^ 4)⁻¹) := by
    rw [← dihedral_pow_four S hx hy]
    exact hx.trans (isConj_iff.mpr ⟨_, rfl⟩)
  have hcy : IsConj S.z (y * (x * y) ^ 4) := by
    have e : y * (x * y) ^ 4 = y * ((y * x) ^ 4)⁻¹ := by
      have : (y * x) = (x * y)⁻¹ := by rw [mul_inv_rev, hxi, hyi]
      rw [this, inv_pow, inv_inv]
    rw [e, ← dihedral_pow_four S hy hx]
    exact hy.trans (isConj_iff.mpr ⟨_, rfl⟩)
  obtain ⟨q, hq, hqe⟩ := exists_commutator_of_coset h34b S hw hU hx hcx hxM hxQ
    (by rw [inv_mul_cancel_left]; exact S.QG.inv_mem h4)
  obtain ⟨q', hq', hqe'⟩ := exists_commutator_of_coset h34b S hw hU hy hcy hyM hyQ
    (by rw [inv_mul_cancel_left]; exact h4)
  rw [inv_mul_cancel_left] at hqe hqe'
  have hmem : S.cl ((x * y) ^ 4) ∈ S.commQt x ⊓ S.commQt y := by
    refine Submodule.mem_inf.mpr ⟨(S.mem_commQt_iff hxM).mpr ⟨q, hq, ?_⟩,
      (S.mem_commQt_iff hyM).mpr ⟨q', hq', by rw [hqe']⟩⟩
    rw [← S.cl_inv h4, hqe]
  rw [hbot] at hmem
  have hc1 : (x * y) ^ 4 = 1 := by
    rcases (S.cl_eq_zero_iff h4).mp ((Submodule.mem_bot _).mp hmem) with h41 | h4z
    · exact h41
    · refine (h34a G S hw hU x hx hxM hxQ ?_).elim
      rw [h4z, inv_eq_of_isConj S (IsConj.refl _)] at hcx
      exact hcx
  have hd : orderOf (x * y) ∣ 4 := orderOf_dvd_of_pow_eq_one hc1
  have hn2 : ¬ orderOf (x * y) ∣ 2 := fun hd2 =>
    h2 (by rw [orderOf_dvd_iff_pow_eq_one.mp hd2]; exact S.QG.one_mem)
  have hle : orderOf (x * y) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  have h4o : orderOf (x * y) = 4 := by
    interval_cases h : orderOf (x * y) <;> simp_all
  exact ⟨by rw [h4o]; simp, fun _ => h23f G S hw hU x y hx hy hxM hyM hxQ hyQ h1 h2 h4⟩

theorem smithL62LocalInput_of (h34a : SmithL6E34a) (h34b : SmithL6E34b) (h23 : SmithL6E23)
    (h24 : SmithL6E24) (h25 : SmithL6E25) (h23f : SmithL6E23Four) : SmithL62LocalInput := by
  intro G _ _ _ S hw hU x y hx hy hxM hyM hxQ
  by_cases hyQ : y ∈ S.QG
  · exact local_of_mem_QG h34a h24 S hw hU hx hy hxM hxQ hyQ
  · exact local_of_not_mem_QG h34a h34b h23 h25 h23f S hw hU hx hy hxM hyM hxQ hyQ

end CFSG.GF2Type.SmithTypeE.L6
