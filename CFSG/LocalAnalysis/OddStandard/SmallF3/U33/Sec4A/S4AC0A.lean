module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxData

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private lemma four_mul {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) :
    ∀ a ∈ ({g : G | g = 1 ∨ g = t ∨ g = z ∨ g = t * z} : Set G),
      ∀ b ∈ ({g : G | g = 1 ∨ g = t ∨ g = z ∨ g = t * z} : Set G),
      a * b ∈ ({g : G | g = 1 ∨ g = t ∨ g = z ∨ g = t * z} : Set G) := by
  have hzt : z * t = t * z := htz.symm
  have h1 : t * (t * z) = z := by rw [← mul_assoc, ht2, one_mul]
  have h2 : (t * z) * t = z := by rw [mul_assoc, ← htz, h1]
  have h3 : (t * z) * z = t := by rw [mul_assoc, hz2, mul_one]
  have h4 : z * (t * z) = t := by rw [← mul_assoc, hzt, h3]
  have h5 : (t * z) * (t * z) = 1 := by rw [← mul_assoc, h2, hz2]
  intro a ha b hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_setOf_eq, one_mul, mul_one, ht2, hz2, h1, h2, h3, h4, h5, hzt,
      eq_self_iff_true, or_true, true_or, or_false, false_or]

private lemma four_inv {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1)
    (htz : t * z = z * t) :
    ∀ a ∈ ({g : G | g = 1 ∨ g = t ∨ g = z ∨ g = t * z} : Set G),
      a⁻¹ ∈ ({g : G | g = 1 ∨ g = t ∨ g = z ∨ g = t * z} : Set G) := by
  have h1 : t * (t * z) = z := by rw [← mul_assoc, ht2, one_mul]
  have h2 : (t * z) * t = z := by rw [mul_assoc, ← htz, h1]
  have h5 : (t * z) * (t * z) = 1 := by rw [← mul_assoc, h2, hz2]
  intro a ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp only [Set.mem_setOf_eq, inv_one, inv_eq_of_mul_eq_one_right ht2,
      inv_eq_of_mul_eq_one_right hz2, inv_eq_of_mul_eq_one_right h5,
      eq_self_iff_true, or_true, true_or, or_false, false_or]

private lemma mul_self_mem_of_relIndex_two {M K : Subgroup G} (hidx : K.relIndex M = 2)
    (a : M) : (a : G) * (a : G) ∈ K := by
  have h2 : (K.subgroupOf M).index = 2 := hidx
  have h := Subgroup.mul_self_mem_of_index_two h2 a
  rwa [Subgroup.mem_subgroupOf] at h

theorem mem_invCent_iff {g : G} : g ∈ invCent t ↔ g * t = t * g := by
  rw [invCent]
  exact Subgroup.mem_centralizer_singleton_iff

theorem twoCore_isPGroup (t : G) : IsPGroup 2 (twoCore t) := by
  rw [twoCore, CFSG.Open.pCoreOf]
  exact CFSG.pCore_isPGroup.map _

theorem twoCore_le_invCent (t : G) : twoCore t ≤ invCent t := by
  rw [twoCore, CFSG.Open.pCoreOf]
  exact Subgroup.map_subtype_le _

theorem twoCore_conj_mem (t : G) {g : G} (hg : g ∈ invCent t) {r : G} (hr : r ∈ twoCore t) :
    g * r * g⁻¹ ∈ twoCore t := by
  rw [twoCore, CFSG.Open.pCoreOf] at hr ⊢
  obtain ⟨o', ho', rfl⟩ := hr
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹, CFSG.pCore_normal.conj_mem o' ho' _, rfl⟩

theorem t_mul_self (h : Hyp G t L) : t * t = 1 := by
  have h1 := pow_orderOf_eq_one t
  rw [h.ord_t] at h1
  simpa [pow_two] using h1

theorem t_ne_one (h : Hyp G t L) : t ≠ 1 := by
  intro ht
  have h2 : orderOf t = 1 := by rw [ht, orderOf_one]
  rw [h.ord_t] at h2
  omega

theorem L_le_invCent (h : Hyp G t L) : L ≤ invCent t := by
  intro l hl
  rw [mem_invCent_iff]
  exact Subgroup.mem_centralizer_iff.mp h.mem_centralizer l hl

theorem twoCore_commute (h : Hyp G t L) : ∀ a ∈ twoCore t, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  have ha' : a ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : a ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
      rw [h.centralizer_eq]
      exact ha
    exact (Subgroup.mem_inf.mp hmem).1
  exact (Subgroup.mem_centralizer_iff.mp ha' b hb).symm

theorem t_not_mem_L (h : Hyp G t L) : t ∉ L := by
  intro htL
  have hmem : t ∈ twoCore t ⊓ L := ⟨h.mem_twoCore, htL⟩
  rw [h.twoCore_inf, Subgroup.mem_bot] at hmem
  exact t_ne_one h hmem

theorem generators_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) : x₁ ∈ L ∧ x₂ ∈ L ∧ lam ∈ L := by
  have hmem : ∀ g ∈ ({x₁, x₂, lam} : Set G), g ∈ L := by
    intro g hg
    have hg' : g ∈ S ⊓ L := by
      rw [h.inf_eq]
      exact Subgroup.subset_closure hg
    exact hg'.2
  exact ⟨hmem x₁ (by simp), hmem x₂ (by simp), hmem lam (by simp)⟩

theorem y_z_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) : x₁ ^ 2 ∈ L ∧ (x₁ * x₂) ^ 2 ∈ L := by
  obtain ⟨hx₁, hx₂, -⟩ := generators_mem_L h
  exact ⟨Subgroup.pow_mem L hx₁ 2, Subgroup.pow_mem L (Subgroup.mul_mem L hx₁ hx₂) 2⟩

theorem z_mul_self_ne_one (h : Ctx0 t L S x₁ x₂ lam rho) :
    (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 ∧ (x₁ * x₂) ^ 2 ≠ 1 :=
  ⟨h.wreath.sq_x₁x₂_mul_self, h.wreath.sq_x₁x₂_ne_one⟩

theorem t_commute_z (h : Ctx0 t L S x₁ x₂ lam rho) : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t := by
  have hzH : (x₁ * x₂) ^ 2 ∈ invCent t := L_le_invCent h.hyp (y_z_mem_L h).2
  rw [mem_invCent_iff] at hzH
  exact hzH.symm

theorem mem_closure_t_z (h : Ctx0 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ closure {t, (x₁ * x₂) ^ 2}) :
    g = 1 ∨ g = t ∨ g = (x₁ * x₂) ^ 2 ∨ g = t * (x₁ * x₂) ^ 2 := by
  have ht2 : t * t = 1 := t_mul_self h.hyp
  have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h).1
  have htz : t * (x₁ * x₂) ^ 2 = (x₁ * x₂) ^ 2 * t := t_commute_z h
  let E : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = t ∨ g = (x₁ * x₂) ^ 2 ∨ g = t * (x₁ * x₂) ^ 2}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        exact four_mul ht2 hz2 htz a ha b hb
      inv_mem' := by
        intro a ha
        exact four_inv ht2 hz2 htz a ha }
  have hEsub : ({t, (x₁ * x₂) ^ 2} : Set G) ⊆ E := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  exact (Subgroup.closure_le (K := E)).mpr hEsub hg

theorem eq_one_or_z_of_mem_closure_t_z_of_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) {g : G}
    (hg : g ∈ closure {t, (x₁ * x₂) ^ 2}) (hgL : g ∈ L) : g = 1 ∨ g = (x₁ * x₂) ^ 2 := by
  rcases mem_closure_t_z h hg with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · exact absurd (h1 ▸ hgL) (t_not_mem_L h.hyp)
  · exact Or.inr h1
  · exfalso
    have hzL : (x₁ * x₂) ^ 2 ∈ L := (y_z_mem_L h).2
    have hz2 : (x₁ * x₂) ^ 2 * (x₁ * x₂) ^ 2 = 1 := (z_mul_self_ne_one h).1
    have hmem : (t * (x₁ * x₂) ^ 2) * (x₁ * x₂) ^ 2 ∈ L :=
      Subgroup.mul_mem L (h1 ▸ hgL) hzL
    rw [mul_assoc, hz2, mul_one] at hmem
    exact t_not_mem_L h.hyp hmem

theorem odd_mem_L (h : Ctx0 t L S x₁ x₂ lam rho) {g : G} (hg : g ∈ invCent t)
    (hodd : ¬ 2 ∣ orderOf g) : g ∈ L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFH : twoCore t ⊔ L ≤ invCent t :=
    sup_le (twoCore_le_invCent t) (L_le_invCent h.hyp)
  have hrel : (twoCore t ⊔ L).relIndex (invCent t) ≤ 2 := h.hyp.relIndex_le
  haveI : (twoCore t ⊔ L).IsFiniteRelIndex (invCent t) :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr Subgroup.finiteIndex_of_finite
  have hrelne : (twoCore t ⊔ L).relIndex (invCent t) ≠ 0 := Subgroup.relIndex_ne_zero
  have hrelcases : (twoCore t ⊔ L).relIndex (invCent t) = 1 ∨
      (twoCore t ⊔ L).relIndex (invCent t) = 2 := by
    have hpos : 0 < (twoCore t ⊔ L).relIndex (invCent t) := Nat.pos_of_ne_zero hrelne
    omega
  have hgF : g ∈ twoCore t ⊔ L := by
    rcases hrelcases with h1 | h2
    · exact (Subgroup.relIndex_eq_one.mp h1) hg
    · have hggF : g * g ∈ twoCore t ⊔ L :=
        mul_self_mem_of_relIndex_two (M := invCent t) (K := twoCore t ⊔ L) h2 ⟨g, hg⟩
      have hodd' : Odd (orderOf g) := by
        rw [← Nat.not_even_iff_odd]
        rwa [even_iff_two_dvd]
      obtain ⟨k, hk⟩ := hodd'
      have hg_eq : g = (g * g) ^ (k + 1) := by
        have h2' : (g * g) ^ (k + 1) = g ^ (2 * (k + 1)) := by
          rw [← pow_two, ← pow_mul g 2]
        rw [h2', show 2 * (k + 1) = orderOf g + 1 by omega, pow_succ,
          pow_orderOf_eq_one, one_mul]
      have hmem := Subgroup.pow_mem (twoCore t ⊔ L) hggF (k + 1)
      rwa [← hg_eq] at hmem
  obtain ⟨p, hp, l, hl, hgl⟩ :=
    (mem_sup_iff_of_commute (twoCore_commute h.hyp)).mp hgF
  have hcomm : Commute p l := twoCore_commute h.hyp p hp l hl
  have hpmlm : p ^ orderOf g * l ^ orderOf g = 1 := by
    rw [← hcomm.mul_pow (orderOf g), ← hgl, pow_orderOf_eq_one]
  have hp_eq : p ^ orderOf g = (l ^ orderOf g)⁻¹ := eq_inv_of_mul_eq_one_left hpmlm
  have hpm_mem_P : p ^ orderOf g ∈ twoCore t := Subgroup.pow_mem (twoCore t) hp (orderOf g)
  have hpm_mem_L : p ^ orderOf g ∈ L := by
    rw [hp_eq]
    exact Subgroup.inv_mem L (Subgroup.pow_mem L hl (orderOf g))
  have hpm1 : p ^ orderOf g = 1 := by
    have hmem : p ^ orderOf g ∈ twoCore t ⊓ L := ⟨hpm_mem_P, hpm_mem_L⟩
    rw [h.hyp.twoCore_inf, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : orderOf p ∣ orderOf g := orderOf_dvd_iff_pow_eq_one.mpr hpm1
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (twoCore_isPGroup t)) ⟨p, hp⟩
  have hj' : orderOf p = 2 ^ j := (Subgroup.orderOf_coe ⟨p, hp⟩).trans hj
  have hp1 : p = 1 := by
    have hdvd2 : 2 ^ j ∣ orderOf g := hj' ▸ hdvd
    have hj0 : j = 0 := by
      by_contra hjne
      have h2dvd : 2 ∣ 2 ^ j := by
        obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hjne
        simpa [pow_succ] using dvd_mul_right 2 (2 ^ i)
      exact hodd (h2dvd.trans hdvd2)
    rw [hj0, pow_zero] at hj'
    exact orderOf_eq_one_iff.mp hj'
  rw [hgl, hp1, one_mul]
  exact hl

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
