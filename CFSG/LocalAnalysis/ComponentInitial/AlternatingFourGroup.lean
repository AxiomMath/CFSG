module

public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Equiv Equiv.Perm Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace AlternatingFourGroup

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
theorem swap_mul_swap_comm {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : swap a b * swap c d = swap c d * swap a b := by
  ext i
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem eq_one_of_forall_commute_alternating (hα : 4 ≤ Fintype.card α) {τ : Perm α}
    (hτ : ∀ g ∈ alternatingGroup α, τ * g = g * τ) : τ = 1 := by
  ext i
  by_contra hne
  have hij : i ≠ τ i := fun h => hne (by rw [Perm.one_apply, ← h])
  obtain ⟨k, hk, l, hl, hkl⟩ : ∃ k ∈ Finset.univ \ {i, τ i}, ∃ l ∈ Finset.univ \ {i, τ i},
      k ≠ l := by
    apply Finset.one_lt_card.1
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Finset.card_pair hij]
    omega
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hk hl
  have hg : swap i k * swap k l ∈ alternatingGroup α := by
    rw [mem_alternatingGroup, map_mul, sign_swap (Ne.symm hk.1), sign_swap hkl]
    decide
  have h := congrArg (· i) (hτ _ hg)
  simp only [Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hk.1) (Ne.symm hl.1),
    swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm hk.2) (Ne.symm hl.2),
    swap_apply_of_ne_of_ne (Ne.symm hij) (Ne.symm hk.2)] at h
  exact hk.1 (τ.injective h)

end Perm

theorem exists_elementary_four_of_commute {H : Type*} [Group H] [Finite H] {x y : H}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    ∃ V : Subgroup H, V ≤ Subgroup.closure {x, y} ∧ CFSG.IsElementaryAbelian 2 V ∧
      Nat.card V = 4 := by
  classical
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; exact absurd hy (by decide)
  have hyX : y ∉ zpowers x := by
    rw [mem_zpowers_iff_mem_range_orderOf, hx, Finset.mem_image]
    rintro ⟨k, hk, hky⟩
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hky
      exact hy1 hky.symm
    · rw [pow_one] at hky
      exact hne hky
  have hcomm : zpowers x ≤ centralizer (zpowers y : Set H) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_left (Commute.symm hxy) k)).eq
  obtain ⟨E, -, -, hE, hEcard, hEle⟩ :=
    CFSG.LargeEvenClassification.Helpers.commuting_disjoint_elementary_product
      (firstRank := 1) (secondRank := 1) (zpowers x) (zpowers y)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary x hx)
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_elementary y hy)
      (by rw [Nat.card_zpowers, hx, pow_one]) (by rw [Nat.card_zpowers, hy, pow_one]) hcomm
      (CFSG.ProperTwoGeneratedCore.involution_zpowers_disjoint (zpowers x) y hy hyX)
  refine ⟨E, hEle.trans (sup_le ?_ ?_),
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 E).2 hE, by rw [hEcard]; norm_num⟩
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  · exact Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))

end AlternatingFourGroup

open AlternatingFourGroup

theorem alternating_at_least_seven_involution_fixed_four_group {n : ℕ} (hn : 7 ≤ n)
    (α : MulAut (alternatingGroup (Fin n))) (hα : orderOf α = 2) :
    (∃ V : Subgroup (alternatingGroup (Fin n)), V ≤ fixedSubgroup α ∧
        CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      2 ≤ CFSG.pRank 2 (fixedSubgroup α) := by
  classical
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inr hn) α
  have hα2 : α * α = 1 := by rw [← sq, ← hα, pow_orderOf_eq_one]
  have hσσ : σ * σ = 1 := by
    refine eq_one_of_forall_commute_alternating (by rw [Fintype.card_fin]; omega) fun g hg => ?_
    have h := congrArg (fun β : MulAut (alternatingGroup (Fin n)) =>
      ((β ⟨g, hg⟩ : alternatingGroup (Fin n)) : Perm (Fin n))) hα2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [hσ, hσ] at h
    calc σ * σ * g = (σ * (σ * g * σ⁻¹) * σ⁻¹) * (σ * σ) := by group
      _ = g * (σ * σ) := by rw [h]
  have hσσi : ∀ i, σ (σ i) = i := fun i => by rw [← Perm.mul_apply, hσσ, Perm.one_apply]
  have hfix : ∀ g : alternatingGroup (Fin n), σ * (g : Perm (Fin n)) * σ⁻¹ = g →
      g ∈ fixedSubgroup α := fun g hg => Subtype.ext ((hσ g).trans hg)
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hcase⟩ : ∃ a b c d : Fin n,
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      ((σ a = a ∧ σ b = b ∧ σ c = c ∧ σ d = d) ∨ (σ a = b ∧ σ b = a ∧ σ c = d ∧ σ d = c)) := by
    by_cases hsupp : σ.support.card ≤ 2
    · set Fx := Finset.univ \ σ.support with hFxdef
      have hFx : 4 ≤ Fx.card := by
        rw [hFxdef, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
          Fintype.card_fin]
        omega
      have hmemFx : ∀ x ∈ Fx, σ x = x := fun x hx => by
        simpa [hFxdef, Perm.mem_support] using hx
      obtain ⟨a, ha⟩ : Fx.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨b, hb, hba⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a}) (t := Fx)
        (by rw [Finset.card_singleton]; omega)
      obtain ⟨c, hc, hcab⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b}) (t := Fx)
        (by have := Finset.card_le_two (a := a) (b := b); omega)
      obtain ⟨d, hd, hdabc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, b, c})
        (t := Fx) (by have := Finset.card_le_three (a := a) (b := b) (c := c); omega)
      simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at hba hcab hdabc
      exact ⟨a, b, c, d, Ne.symm hba, Ne.symm hcab.1, Ne.symm hdabc.1, Ne.symm hcab.2,
        Ne.symm hdabc.2.1, Ne.symm hdabc.2.2,
        Or.inl ⟨hmemFx a ha, hmemFx b hb, hmemFx c hc, hmemFx d hd⟩⟩
    · push Not at hsupp
      obtain ⟨a, ha⟩ : σ.support.Nonempty := Finset.card_pos.1 (by omega)
      have hσa : σ a ≠ a := Perm.mem_support.1 ha
      obtain ⟨c, hc, hcab⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := {a, σ a})
        (t := σ.support) (by have := Finset.card_le_two (a := a) (b := σ a); omega)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcab
      have hσc : σ c ≠ c := Perm.mem_support.1 hc
      refine ⟨a, σ a, c, σ c, Ne.symm hσa, Ne.symm hcab.1, fun h => hcab.2 ?_,
        Ne.symm hcab.2, fun h => hcab.1 (σ.injective h).symm, Ne.symm hσc,
        Or.inr ⟨rfl, hσσi a, rfl, hσσi c⟩⟩
      rw [← hσσi c, ← h]
  have hconj : ∀ (τ : Perm (Fin n)) (p q : Fin n), τ * swap p q * τ⁻¹ = swap (τ p) (τ q) :=
    fun τ p q => (swap_apply_apply τ p q).symm
  have hxy2 : ∀ {p q r s : Fin n}, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      σ * (swap p q * swap r s) * σ⁻¹ = swap (σ p) (σ q) * swap (σ r) (σ s) := by
    intro p q r s _ _ _ _ _ _
    rw [← hconj, ← hconj]
    group
  let x : Perm (Fin n) := swap a b * swap c d
  let y : Perm (Fin n) := swap a c * swap b d
  have hxA : x ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap hab, sign_swap hcd]
    decide
  have hyA : y ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, map_mul, sign_swap hac, sign_swap hbd]
    decide
  have hσx : σ * x * σ⁻¹ = x := by
    rw [hxy2 hab hac had hbc hbd hcd]
    rcases hcase with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    · rw [ha, hb, hc, hd]
    · rw [ha, hb, hc, hd, swap_comm b a, swap_comm d c]
  have hσy : σ * y * σ⁻¹ = y := by
    rw [hxy2 hac hab had (Ne.symm hbc) hcd hbd]
    rcases hcase with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
    · rw [ha, hb, hc, hd]
    · rw [ha, hb, hc, hd]
      exact swap_mul_swap_comm (Ne.symm hab) hbc (Ne.symm had) (Ne.symm hcd)
  have hxa : x a = b := by
    change (swap a b * swap c d) a = b
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
  have hxb : x b = a := by
    change (swap a b * swap c d) b = a
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
  have hxc : x c = d := by
    change (swap a b * swap c d) c = d
    rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
  have hxd : x d = c := by
    change (swap a b * swap c d) d = c
    rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  have hya : y a = c := by
    change (swap a c * swap b d) a = c
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left]
  have hxyc : x * y = y * x := by
    have hxyx : x * y * x⁻¹ = y := by
      rw [show x * y * x⁻¹ = (x * swap a c * x⁻¹) * (x * swap b d * x⁻¹) by simp only [y]; group,
        hconj, hconj, hxa, hxb, hxc, hxd]
      exact swap_mul_swap_comm (Ne.symm hab) hbc (Ne.symm had) (Ne.symm hcd)
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [hxyx]
  have hx2 : x * x = 1 := by
    have hcomm := swap_mul_swap_comm hac had hbc hbd
    calc x * x = swap a b * (swap c d * swap a b) * swap c d := by simp only [x]; group
      _ = 1 := by rw [← hcomm]; simp
  have hy2 : y * y = 1 := by
    have hcomm := swap_mul_swap_comm hab had (Ne.symm hbc) hcd
    calc y * y = swap a c * (swap b d * swap a c) * swap b d := by simp only [y]; group
      _ = 1 := by rw [← hcomm]; simp
  have hx1 : x ≠ 1 := fun h => hab (by rw [← hxa, h, Perm.one_apply])
  have hy1 : y ≠ 1 := fun h => hac (by rw [← hya, h, Perm.one_apply])
  have hxne : x ≠ y := fun h => hbc (by rw [← hxa, ← hya, h])
  let x' : alternatingGroup (Fin n) := ⟨x, hxA⟩
  let y' : alternatingGroup (Fin n) := ⟨y, hyA⟩
  have hx'o : orderOf x' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hy'o : orderOf y' = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  obtain ⟨V, hVcl, hV, hVcard⟩ := exists_elementary_four_of_commute hx'o hy'o
    (Subtype.ext hxyc) (fun h => hxne (congrArg Subtype.val h))
  have hVC : V ≤ fixedSubgroup α := hVcl.trans ((Subgroup.closure_le _).2 (by
    rintro _ (rfl | rfl)
    · exact hfix x' hσx
    · exact hfix y' hσy))
  refine ⟨⟨V, hVC, hV, hVcard⟩, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hpow : ∀ v : V, v ^ 2 = 1 := fun v =>
    Subtype.ext (by
      simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V)
        (v : alternatingGroup (Fin n)) v.2)
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun u v => mul_comm' u v) hpow
    (by rw [hVcard]; norm_num) (Subgroup.inclusion hVC) (Subgroup.inclusion_injective hVC)
    le_top

end CFSG.LocalAnalysis.ComponentInitial
