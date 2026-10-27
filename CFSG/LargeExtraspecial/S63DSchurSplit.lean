module

public import CFSG.LargeExtraspecial.S63DSchurAdm
public import CFSG.LargeExtraspecial.S63DSchurModel
public import CFSG.LargeExtraspecial.S63CD4Iso

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin

theorem odd_index_d4U :
    Odd d4U.index := by
  have h1 := d4U.card_mul_index
  rw [card_d4U, card_trialityGroup8] at h1
  have h2 : d4U.index = 51597 := by omega
  rw [h2]
  decide

theorem d42SplitAt_d4z : D42SplitAt trialityGroup8 d4z := by
  intro N hN
  rw [eq_d4Q_of_admAt_d4z hN]
  obtain ⟨hyz, h0z, c01, c02, c12, r1, r2, r3, h6Q⟩ := d4Split
  have hy : d4y ∈ centralizer ({d4z} : Set trialityGroup8) :=
    mem_centralizer_singleton_iff.mpr hyz
  have h0 : d4GenG 0 ∈ centralizer ({d4z} : Set trialityGroup8) :=
    mem_centralizer_singleton_iff.mpr h0z
  have h2 : d4GenG 2 ∈ centralizer ({d4z} : Set trialityGroup8) := by
    rw [← r1]
    exact mul_mem (mul_mem hy h0) (inv_mem hy)
  have h21 : d4GenG 2 * d4GenG 1 ∈ centralizer ({d4z} : Set trialityGroup8) := by
    rw [← r2]
    exact mul_mem (mul_mem hy h2) (inv_mem hy)
  refine ⟨d4GenG 0, d4GenG 2, d4GenG 2 * d4GenG 1, d4y, h0, h2, h21, c02, c02.mul_right c01,
    (Commute.refl _).mul_right c12.symm, r1, r2, r3, ?_⟩
  set T := d4Q ⊔ closure ({d4GenG 0, d4GenG 2, d4GenG 2 * d4GenG 1} : Set trialityGroup8)
  have hcl : ∀ x ∈ ({d4GenG 0, d4GenG 2, d4GenG 2 * d4GenG 1} : Set trialityGroup8), x ∈ T :=
    fun x hx => mem_sup_right (subset_closure hx)
  have hUT : d4U ≤ T := by
    rw [d4U, closure_le]
    rintro _ ⟨k, hk, rfl⟩
    change k < uGens.size at hk
    rw [uGens_size] at hk
    interval_cases k
    · exact hcl _ (by simp [uGH, uIdx])
    · have hg2 : d4GenG 2 * d4GenG 2 = 1 := (d4Gens_hyp 2 (by decide)).2
      have e : uGH 1 = d4GenG 2 * (d4GenG 2 * d4GenG 1) := by
        rw [← mul_assoc, hg2, one_mul]
        rfl
      rw [SetLike.mem_coe, e]
      exact mul_mem (hcl _ (by simp)) (hcl _ (by simp))
    · exact hcl _ (by simp [uGH, uIdx])
    · exact mem_sup_left h6Q
  exact Odd.of_dvd_nat odd_index_d4U (index_dvd_of_le hUT)

theorem d42SplitAt_d4t : D42SplitAt trialityGroup8 d4t :=
  fun _ hN => (false_of_admAt_d4t hN).elim

theorem d42SplitInput : D42SplitInput := by
  intro Y _ hY s hs
  obtain ⟨e⟩ := nonempty_equiv_trialityGroup8 Y hY
  refine D42SplitAt.of_mulEquiv e ?_
  have hes : orderOf (e s) = 2 := by rw [MulEquiv.orderOf_eq]; exact hs
  obtain ⟨c, hc | hc⟩ := exists_conj_of_orderOf_eq_two hes
  · rw [hc]
    exact d42SplitAt_d4z.conj c
  · rw [hc]
    exact d42SplitAt_d4t.conj c

end CFSG.LargeExtraspecial.S63
