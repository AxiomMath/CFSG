module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Model28

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup

theorem exists_coset_hom {C : Type*} [Group C] (N : Subgroup C) [N.Normal] {t g : C}
    (ht : ∀ c : C, c * t = t * c) (ht2 : t * t = 1) (hgg : g * g = 1 ∨ g * g = t)
    (htN : t ∉ N) (hgN : g ∉ N) (hgtN : g * t ∉ N) (hcard : Nat.card (C ⧸ N) = 4) :
    ∃ τ : C →* Perm (Fin 4), (∀ n ∈ N, τ n = 1) ∧ τ t = tFour ∧
      (g * g = 1 → τ g = hOne) ∧ (g * g = t → τ g = hTwo) := by
  classical
  let Q := C ⧸ N
  have hgtN' : g⁻¹ * t ∉ N := by
    rcases hgg with hgg1 | hgg2
    · have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg1
      rwa [hginv]
    · have hginv : g⁻¹ = g * t := by
        apply inv_eq_of_mul_eq_one_right
        calc g * (g * t) = (g * g) * t := by rw [mul_assoc]
          _ = t * t := by rw [hgg2]
          _ = 1 := ht2
      rw [hginv]
      have hmul : (g * t) * t = g := by rw [mul_assoc, ht2, mul_one]
      rwa [hmul]
  let e : Fin 4 → Q := ![1, (g : Q), (t : Q), ((g * t : C) : Q)]
  have he0 : e 0 = ((1 : C) : Q) := by simp [e]
  have he1 : e 1 = (g : Q) := by simp [e]
  have he2 : e 2 = (t : Q) := by simp [e]
  have he3 : e 3 = ((g * t : C) : Q) := by simp [e]
  have h01 : e 0 ≠ e 1 := by
    intro h
    rw [he0, he1] at h
    exact hgN ((QuotientGroup.eq_one_iff g).mp h.symm)
  have h02 : e 0 ≠ e 2 := by
    intro h
    rw [he0, he2] at h
    exact htN ((QuotientGroup.eq_one_iff t).mp h.symm)
  have h03 : e 0 ≠ e 3 := by
    intro h
    rw [he0, he3] at h
    exact hgtN ((QuotientGroup.eq_one_iff (g * t)).mp h.symm)
  have h12 : e 1 ≠ e 2 := by
    intro h
    rw [he1, he2] at h
    exact hgtN' (QuotientGroup.eq.mp h)
  have h13 : e 1 ≠ e 3 := by
    intro h
    rw [he1, he3] at h
    have h' := QuotientGroup.eq.mp h
    have hmul : g⁻¹ * (g * t) = t := by group
    rw [hmul] at h'
    exact htN h'
  have h23 : e 2 ≠ e 3 := by
    intro h
    rw [he2, he3] at h
    have h' := QuotientGroup.eq.mp h
    have hmul : t⁻¹ * (g * t) = g := by
      rw [ht g, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hmul] at h'
    exact hgN h'
  have he_inj : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  haveI : Finite Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcard_le : Nat.card Q ≤ Nat.card (Fin 4) := by
    rw [hcard, Nat.card_fin]
  have he_bij : Function.Bijective e := he_inj.bijective_of_nat_card_le hcard_le
  let ε : Fin 4 ≃ Q := Equiv.ofBijective e he_bij
  have hε0 : ε 0 = ((1 : C) : Q) := by simp [ε, e]
  have hε1 : ε 1 = (g : Q) := by simp [ε, e]
  have hε2 : ε 2 = (t : Q) := by simp [ε, e]
  have hε3 : ε 3 = ((g * t : C) : Q) := by simp [ε, e]
  let τ : C →* Perm (Fin 4) :=
    (Equiv.permCongrHom ε.symm).toMonoidHom.comp (MulAction.toPermHom C Q)
  have hτ : ∀ (c : C) (i : Fin 4), τ c i = ε.symm (c • ε i) := by
    intro c i
    rfl
  have hN : ∀ n ∈ N, τ n = 1 := by
    intro n hn
    ext i
    rw [hτ n i]
    have hfix : n • ε i = ε i := by
      obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ε i)
      rw [← ha]
      have hn1 : (n : Q) = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, QuotientGroup.mk_mul, hn1, one_mul]
    rw [hfix]
    simp
  have htv0 : τ t 0 = 2 := by
    rw [hτ t 0, hε0]
    have h : t • ((1 : C) : Q) = ε 2 := by
      rw [hε2, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    rw [h, Equiv.symm_apply_apply]
  have htv1 : τ t 1 = 3 := by
    rw [hτ t 1, hε1]
    have h : t • (g : Q) = ε 3 := by
      rw [hε3, MulAction.Quotient.smul_coe, smul_eq_mul, ht g]
    rw [h, Equiv.symm_apply_apply]
  have htv2 : τ t 2 = 0 := by
    rw [hτ t 2, hε2]
    have h : t • (t : Q) = ε 0 := by
      rw [hε0, MulAction.Quotient.smul_coe, smul_eq_mul, ht2]
    rw [h, Equiv.symm_apply_apply]
  have htv3 : τ t 3 = 1 := by
    rw [hτ t 3, hε3]
    have hmul : t * (g * t) = g := by
      rw [ht g, ← mul_assoc, ht2, one_mul]
    have h : t • ((g * t : C) : Q) = ε 1 := by
      rw [hε1, MulAction.Quotient.smul_coe, smul_eq_mul, hmul]
    rw [h, Equiv.symm_apply_apply]
  have htFour0 : tFour 0 = 2 := by decide
  have htFour1 : tFour 1 = 3 := by decide
  have htFour2 : tFour 2 = 0 := by decide
  have htFour3 : tFour 3 = 1 := by decide
  have htτ : τ t = tFour := by
    ext i
    fin_cases i <;>
      simp [htv0, htv1, htv2, htv3, htFour0, htFour1, htFour2, htFour3]
  have hgv0 : τ g 0 = 1 := by
    rw [hτ g 0, hε0]
    have h : g • ((1 : C) : Q) = ε 1 := by
      rw [hε1, MulAction.Quotient.smul_coe, smul_eq_mul, mul_one]
    rw [h, Equiv.symm_apply_apply]
  have hgv2 : τ g 2 = 3 := by
    rw [hτ g 2, hε2]
    have h : g • (t : Q) = ε 3 := by
      rw [hε3, MulAction.Quotient.smul_coe, smul_eq_mul]
    rw [h, Equiv.symm_apply_apply]
  have hgv1_one : g * g = 1 → τ g 1 = 0 := by
    intro hgg1
    rw [hτ g 1, hε1]
    have h : g • (g : Q) = ε 0 := by
      rw [hε0, MulAction.Quotient.smul_coe, smul_eq_mul, hgg1]
    rw [h, Equiv.symm_apply_apply]
  have hgv3_one : g * g = 1 → τ g 3 = 2 := by
    intro hgg1
    rw [hτ g 3, hε3]
    have hmul : g * (g * t) = t := by rw [← mul_assoc, hgg1, one_mul]
    have h : g • ((g * t : C) : Q) = ε 2 := by
      rw [hε2, MulAction.Quotient.smul_coe, smul_eq_mul, hmul]
    rw [h, Equiv.symm_apply_apply]
  have hgv1_two : g * g = t → τ g 1 = 2 := by
    intro hgg2
    rw [hτ g 1, hε1]
    have h : g • (g : Q) = ε 2 := by
      rw [hε2, MulAction.Quotient.smul_coe, smul_eq_mul, hgg2]
    rw [h, Equiv.symm_apply_apply]
  have hgv3_two : g * g = t → τ g 3 = 0 := by
    intro hgg2
    rw [hτ g 3, hε3]
    have hmul : g * (g * t) = 1 := by rw [← mul_assoc, hgg2, ht2]
    have h : g • ((g * t : C) : Q) = ε 0 := by
      rw [hε0, MulAction.Quotient.smul_coe, smul_eq_mul, hmul]
    rw [h, Equiv.symm_apply_apply]
  have hOne0 : hOne 0 = 1 := by decide
  have hOne1 : hOne 1 = 0 := by decide
  have hOne2 : hOne 2 = 3 := by decide
  have hOne3 : hOne 3 = 2 := by decide
  have hTwo0 : hTwo 0 = 1 := by decide
  have hTwo1 : hTwo 1 = 2 := by decide
  have hTwo2 : hTwo 2 = 3 := by decide
  have hTwo3 : hTwo 3 = 0 := by decide
  have hgOne : g * g = 1 → τ g = hOne := by
    intro hgg1
    ext i
    fin_cases i <;>
      simp [hgv0, hgv1_one hgg1, hgv2, hgv3_one hgg1,
        hOne0, hOne1, hOne2, hOne3]
  have hgTwo : g * g = t → τ g = hTwo := by
    intro hgg2
    ext i
    fin_cases i <;>
      simp [hgv0, hgv1_two hgg2, hgv2, hgv3_two hgg2,
        hTwo0, hTwo1, hTwo2, hTwo3]
  exact ⟨τ, hN, htτ, hgOne, hgTwo⟩

end CFSG.EvenSporadicStandard.M12Std.PropA
