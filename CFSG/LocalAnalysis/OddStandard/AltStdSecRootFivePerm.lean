module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootSupp

public section

namespace CFSG.OddStandard.AltStdSec

open Equiv Subgroup

theorem rootFive_orderOf {n : ℕ} {c : Perm (Fin n)} (hc : c.IsCycle) (h5 : c.support.card = 5) :
    orderOf c = 5 := by
  rw [hc.orderOf, h5]

theorem rootFive_sign {n : ℕ} {c : Perm (Fin n)} (hc : c.IsCycle) (h5 : c.support.card = 5) :
    Perm.sign c = 1 := by
  rw [hc.sign, h5]
  decide

theorem rootFive_mem_zpowers_of_commute {n : ℕ} {c g : Perm (Fin n)} (hc : c.IsCycle)
    (hg : g * c = c * g) (hfix : ∀ i, i ∉ c.support → g i = i) : g ∈ zpowers c := by
  obtain ⟨hinv, hmem⟩ := (hc.commute_iff).1 hg
  have h1 : Perm.ofSubtype (g.subtypePerm hinv) = g :=
    Perm.ofSubtype_subtypePerm hinv fun x hx => by_contra fun hxs => hx (hfix x hxs)
  rwa [h1] at hmem

theorem rootFive_isCycle_of_orderOf {n : ℕ} {σ : Perm (Fin n)} {F : Finset (Fin n)}
    (hF : F.card = 6) (hσ : orderOf σ = 5) (hs : σ.support ⊆ F) :
    σ.IsCycle ∧ σ.support.card = 5 := by
  have hdvd : 5 ∣ σ.support.card :=
    rootSupp_dvd_support_card_of_orderOf_prime (by norm_num) hσ
  have hne : σ ≠ 1 := by
    rintro rfl
    simp at hσ
  have hpos : σ.support.card ≠ 0 := fun h => hne (Perm.card_support_eq_zero.1 h)
  have hle : σ.support.card ≤ 6 := hF ▸ Finset.card_le_card hs
  have h5 : σ.support.card = 5 := by omega
  refine ⟨Perm.isCycle_of_prime_order (by rw [hσ]; norm_num) ?_, h5⟩
  omega

theorem rootFive_swap_comm {n : ℕ} {c : Perm (Fin n)} {u v : Fin n} (hu : u ∉ c.support)
    (hv : v ∉ c.support) : swap u v * c = c * swap u v := by
  refine (Perm.Disjoint.commute fun x => ?_)
  by_cases hxu : x = u
  · right
    rw [hxu]
    exact Perm.notMem_support.1 hu
  by_cases hxv : x = v
  · right
    rw [hxv]
    exact Perm.notMem_support.1 hv
  · left
    exact swap_apply_of_ne_of_ne hxu hxv

theorem rootFive_exists_even_conj {n : ℕ} (hn : 12 ≤ n) {c c' : Perm (Fin n)}
    (hc : c.IsCycle) (hc5 : c.support.card = 5) (hc' : c'.IsCycle) (hc'5 : c'.support.card = 5) :
    ∃ σ : Perm (Fin n), Perm.sign σ = 1 ∧ σ * c * σ⁻¹ = c' := by
  have hct : c.cycleType = c'.cycleType := by
    rw [hc.cycleType, hc'.cycleType, hc5, hc'5]
  obtain ⟨σ₀, hσ₀⟩ := isConj_iff.1 (Perm.isConj_iff_cycleType_eq.2 hct)
  rcases Int.units_eq_one_or (Perm.sign σ₀) with h | h
  · exact ⟨σ₀, h, hσ₀⟩
  · have hcard : 1 < (c'.support)ᶜ.card := by
      rw [Finset.card_compl, Fintype.card_fin, hc'5]
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcard
    rw [Finset.mem_compl] at hu hv
    have hcomm := rootFive_swap_comm hu hv
    refine ⟨swap u v * σ₀, ?_, ?_⟩
    · rw [Perm.sign_mul, Perm.sign_swap huv, h]
      decide
    · calc swap u v * σ₀ * c * (swap u v * σ₀)⁻¹
          = swap u v * (σ₀ * c * σ₀⁻¹) * (swap u v)⁻¹ := by group
        _ = swap u v * c' * (swap u v)⁻¹ := by rw [hσ₀]
        _ = c' := by rw [hcomm, mul_inv_cancel_right]

theorem rootFive_exists_cycle_in {n : ℕ} {F : Finset (Fin n)} (hF : 5 ≤ F.card) :
    ∃ c : Perm (Fin n), c.IsCycle ∧ c.support.card = 5 ∧ c.support ⊆ F := by
  obtain ⟨T, hTF, hT⟩ := Finset.exists_subset_card_eq hF
  have hnd : T.toList.Nodup := T.nodup_toList
  have hlen : T.toList.length = 5 := by rw [Finset.length_toList, hT]
  have hsupp : (T.toList.formPerm).support = T := by
    rw [List.support_formPerm_of_nodup _ hnd (fun x h => by rw [h] at hlen; simp at hlen),
      Finset.toList_toFinset]
  refine ⟨T.toList.formPerm, List.isCycle_formPerm hnd (by omega), ?_, ?_⟩
  · rw [hsupp, hT]
  · rw [hsupp]
    exact hTF

theorem rootFive_exists_involution_gen {n : ℕ} {S : Finset (Fin n)} (hS : S.card + 4 ≤ n) :
    ∃ b : Perm (Fin n), b * b = 1 ∧ Perm.sign b = 1 ∧ b ≠ 1 ∧ (∀ i ∈ S, b i = i) ∧
      n - 4 ≤ (Finset.univ.filter fun i => b i = i).card := by
  have hcard : 4 ≤ (Sᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨a₁, a₂, a₃, a₄, h12, h13, h14, h23, h24, h34, rfl⟩ := Finset.card_eq_four.1 hT
  have ha : ∀ i ∈ ({a₁, a₂, a₃, a₄} : Finset (Fin n)), i ∉ S := fun i hi hiS =>
    (Finset.mem_compl.1 (hTS hi)) hiS
  have hdisj : Perm.Disjoint (swap a₁ a₂) (swap a₃ a₄) := by
    intro x
    by_cases hx : x = a₁ ∨ x = a₂
    · right
      rcases hx with rfl | rfl
      · exact swap_apply_of_ne_of_ne h13 h14
      · exact swap_apply_of_ne_of_ne h23 h24
    · left
      push Not at hx
      exact swap_apply_of_ne_of_ne hx.1 hx.2
  have hfix : ∀ i, i ∉ ({a₁, a₂, a₃, a₄} : Finset (Fin n)) →
      (swap a₁ a₂ * swap a₃ a₄) i = i := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi3 hi4, swap_apply_of_ne_of_ne hi1 hi2]
  refine ⟨swap a₁ a₂ * swap a₃ a₄, ?_, ?_, ?_, fun i hi => hfix i fun h => ha i h hi, ?_⟩
  · rw [hdisj.commute.symm.mul_mul_mul_comm, swap_mul_self, swap_mul_self, mul_one]
  · rw [Perm.sign_mul, Perm.sign_swap h12, Perm.sign_swap h34]
    decide
  · intro h
    have h1 : (swap a₁ a₂ * swap a₃ a₄) a₁ = a₂ := by
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne h13 h14, swap_apply_left]
    rw [h] at h1
    exact h12 (by simpa using h1)
  · have hsub : ({a₁, a₂, a₃, a₄} : Finset (Fin n))ᶜ ⊆
        Finset.univ.filter fun i => (swap a₁ a₂ * swap a₃ a₄) i = i := fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ i, hfix i (Finset.mem_compl.1 hi)⟩
    refine le_trans ?_ (Finset.card_le_card hsub)
    rw [Finset.card_compl, Fintype.card_fin, hT]

theorem rootFive_exists_involution {n : ℕ} (hn : 14 ≤ n) {S : Finset (Fin n)}
    (hS : S.card = 5) :
    ∃ b : Perm (Fin n), b * b = 1 ∧ Perm.sign b = 1 ∧ b ≠ 1 ∧ (∀ i ∈ S, b i = i) ∧
      10 ≤ (Finset.univ.filter fun i => b i = i).card := by
  obtain ⟨b, h1, h2, h3, h4, h5⟩ := rootFive_exists_involution_gen (S := S) (by omega)
  exact ⟨b, h1, h2, h3, h4, by omega⟩

end CFSG.OddStandard.AltStdSec
