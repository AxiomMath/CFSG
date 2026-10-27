module

public import CFSG.Sporadic.Fi22.InvFix

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Sporadic.Fi22

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem mul_comm_of_sq_eq_one_mul {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hy)
  have hxy' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hxy)
  calc x * y = (x * y)⁻¹ := hxy'.symm
    _ = y * x := by rw [mul_inv_rev, hx', hy']

section Pair


@[expose] noncomputable def fixD (g : J) : ℕ :=
  (Finset.univ.filter fun i : Fin 3510 => g • i = i).card

theorem fixD_conj (c g : J) : fixD (c * g * c⁻¹) = fixD g := card_fixed_conj c g

theorem subLab_eq_two_of_comm {p : Fin 3510} (hne : conjPt p.val ≠ a)
    (hc : a * conjPt p.val = conjPt p.val * a) : subLab p = 2 := by
  have hcases : subLab p = 0 ∨ subLab p = 1 ∨ subLab p = 2 := by
    rcases subLab p with ⟨_ | _ | _ | n, hn⟩
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    have hp : p = root := subLab_eq_zero.1 h0
    apply hne
    have hk0 : p.val = 0 := congrArg Fin.val hp
    rw [hk0, conjPt_zero]
  · exfalso
    obtain ⟨⟨h, hh⟩, hr⟩ := subLab_eq_one.1 h1
    have e1 : conjPt p.val = h * conjPt 1 * h⁻¹ := by
      have := conjPt_smul h (⟨1, treeFacts_one.r_lt⟩ : Fin 3510)
      rw [show h • (⟨1, treeFacts_one.r_lt⟩ : Fin 3510) = p from hr] at this
      exact this
    have e2 : h * a * h⁻¹ = a := conj_a_of_fix (lvl_one_fix hh)
    apply a_mul_conjPt_one_ne
    have key : h * (a * conjPt 1) * h⁻¹ = h * (conjPt 1 * a) * h⁻¹ := by
      calc h * (a * conjPt 1) * h⁻¹ = (h * a * h⁻¹) * (h * conjPt 1 * h⁻¹) := by group
        _ = a * conjPt p.val := by rw [e2, ← e1]
        _ = conjPt p.val * a := hc
        _ = (h * conjPt 1 * h⁻¹) * (h * a * h⁻¹) := by rw [e2, ← e1]
        _ = h * (conjPt 1 * a) * h⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel key)
  · exact h2

theorem exists_lvl_one_smul_eq {p q : Fin 3510} (hp : conjPt p.val ≠ a)
    (hpc : a * conjPt p.val = conjPt p.val * a) (hq : conjPt q.val ≠ a)
    (hqc : a * conjPt q.val = conjPt q.val * a) : ∃ h ∈ lvl 1, h • p = q :=
  subLab_orb p q ((subLab_eq_two_of_comm hp hpc).trans (subLab_eq_two_of_comm hq hqc).symm)

end Pair

section Fixed


theorem fixD_a_mul_conjPt_eight :
    (a * conjPt 8) ^ 2 = 1 ∧ a * conjPt 8 ≠ 1 ∧ fixD (a * conjPt 8) = 182 := by
  have key := inv_parts.2.1 ([0, 8], 182) (by simp [CFSG.Sporadic.Fi22.Native.fixWords])
  have h := fixExact_spec (rep_wordTab [0, 8] key.1) key.2
  simpa [fixD, conjPt_zero] using h

theorem conjPt_eight_comm : conjPt 8 ≠ a ∧ a * conjPt 8 = conjPt 8 * a := by
  obtain ⟨h2, h1, -⟩ := fixD_a_mul_conjPt_eight
  have hD8 : conjPt 8 ∈ D := mem_D_iff.2 ⟨8, by norm_num, rfl⟩
  have hc8 : conjPt 8 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (conjPt 8)
    rwa [orderOf_of_mem_D hD8] at h
  have hcomm : a * conjPt 8 = conjPt 8 * a :=
    mul_comm_of_sq_eq_one_mul (G := ↥J) (x := a) (y := conjPt 8) a_sq hc8 h2
  have hne : conjPt 8 ≠ a := by
    intro h
    apply h1
    rw [h, ← sq]
    exact a_sq
  exact ⟨hne, hcomm⟩

theorem exists_conj_pair {x y : J} (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y)
    (hc : x * y = y * x) : ∃ g : J, g * x * g⁻¹ = a ∧ g * y * g⁻¹ = conjPt 8 := by
  obtain ⟨c, hcx⟩ := isConj_iff.1 hx
  have hy' : c⁻¹ * y * c ∈ D := by
    obtain ⟨u, hu⟩ := isConj_iff.1 hy
    exact isConj_iff.2 ⟨c⁻¹ * u, by rw [← hu]; group⟩
  obtain ⟨k, hk, hke⟩ := mem_D_iff.1 hy'
  have hne' : conjPt k ≠ a := by
    intro h
    apply hne
    rw [← hcx, ← h, ← hke]
    group
  have hc' : a * conjPt k = conjPt k * a := by
    rw [← hke]
    have : x * y = y * x := hc
    calc a * (c⁻¹ * y * c) = c⁻¹ * (c * a * c⁻¹) * y * c := by group
      _ = c⁻¹ * (x * y) * c := by rw [hcx]; group
      _ = c⁻¹ * (y * x) * c := by rw [this]
      _ = (c⁻¹ * y * c) * a := by rw [← hcx]; group
  obtain ⟨hne8, hc8⟩ := conjPt_eight_comm
  obtain ⟨h, hh, hhp⟩ := exists_lvl_one_smul_eq (p := ⟨k, hk⟩) (q := ⟨8, by norm_num⟩) hne' hc'
    hne8 hc8
  have e1 : conjPt 8 = h * conjPt k * h⁻¹ := by
    have := conjPt_smul h (⟨k, hk⟩ : Fin 3510)
    rw [hhp] at this
    exact this
  have e2 : h * a * h⁻¹ = a := conj_a_of_fix (lvl_one_fix hh)
  refine ⟨h * c⁻¹, ?_, ?_⟩
  · calc h * c⁻¹ * x * (h * c⁻¹)⁻¹ = h * (c⁻¹ * x * c) * h⁻¹ := by group
      _ = h * a * h⁻¹ := by rw [← hcx]; group
      _ = a := e2
  · calc h * c⁻¹ * y * (h * c⁻¹)⁻¹ = h * (c⁻¹ * y * c) * h⁻¹ := by group
      _ = h * conjPt k * h⁻¹ := by rw [hke]
      _ = conjPt 8 := e1.symm

theorem fixD_mul_of_comm {x y : J} (hx : x ∈ D) (hy : y ∈ D) (hne : x ≠ y)
    (hc : x * y = y * x) : fixD (x * y) = 182 := by
  obtain ⟨g, hgx, hgy⟩ := exists_conj_pair hx hy hne hc
  rw [← fixD_conj g (x * y)]
  have : g * (x * y) * g⁻¹ = a * conjPt 8 := by
    rw [← hgx, ← hgy]
    group
  rw [this]
  exact fixD_a_mul_conjPt_eight.2.2

end Fixed

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
