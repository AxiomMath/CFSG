module

public import CFSG.ClassicalGroups.Unitary.Generation

public section

namespace CFSG.ClassicalGroups.Unitary

open Matrix CFSG.LieType.Universal.Unitary
open scoped commutatorElement

variable {K : Type*} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem tv_mem_commutator_of_perp (hσ : IsUnitaryInvolution σ) {e w : Fin n → K}
    (he : herm σ e e = 0) (hw : herm σ w w = 1) (hew : herm σ e w = 0) {t : K}
    (ht : t + σ t = 0) : tv hσ.invol he ht ∈ commutator (SUid σ n) := by
  obtain ⟨r, hr⟩ := hσ.exists_sub_eq ht
  obtain ⟨c₁, hc₁⟩ := hσ.trace_surj (-herm σ w w)
    (by rw [map_neg, herm_self_fixed σ hσ.invol])
  obtain ⟨c₂, hc₂⟩ := hσ.trace_surj (-herm σ (r • w) (r • w))
    (by rw [map_neg, herm_self_fixed σ hσ.invol])
  have hew' : herm σ e (r • w) = 0 := by rw [herm_smul_right, hew, mul_zero]
  have hcoef : herm σ (r • w) w - herm σ w (r • w) = t := by
    rw [herm_smul_left, herm_smul_right, hw]
    linear_combination hr
  have ht' : (herm σ (r • w) w - herm σ w (r • w)) +
      σ (herm σ (r • w) w - herm σ w (r • w)) = 0 := by
    rw [hcoef]; exact ht
  have hkey := eichler_mul_eichler hσ.invol he hew hew' hc₁ hc₂ ht'
  have htv : tv hσ.invol he ht' = tv hσ.invol he ht := by
    apply ext_smul
    intro v
    rw [tv_smul, tv_smul, hcoef]
  have hcomm : ⁅eichler hσ.invol he hew hc₁, eichler hσ.invol he hew' hc₂⁆ =
      tv hσ.invol he ht := by
    rw [commutatorElement_def, hkey, htv]
    group
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem commutator_SUid_eq_top (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) : commutator (SUid σ n) = ⊤ := by
  obtain ⟨W⟩ := hσ.nonempty_wittData
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 2 := ⟨n - 3, by omega⟩
  set a₀ := W.hypA (m + 1) with ha₀def
  set w : Fin (m + 1 + 2) → K := Pi.single ((0 : Fin (m + 1)).succ.succ) 1 with hwdef
  have ha₀ : herm σ a₀ a₀ = 0 := W.herm_hypA_hypA
  have hw : herm σ w w = 1 := by
    rw [hwdef, herm_single_left, Pi.single_eq_same, map_one, one_mul]
  have ha₀w : herm σ a₀ w = 0 := by
    rw [ha₀def, W.herm_hypA_left, hwdef, Pi.single_eq_of_ne (Fin.succ_ne_zero _).symm,
      Pi.single_eq_of_ne (WittData.succ_succ_ne_one 0).symm]
    simp
  rw [eq_top_iff, ← T_eq_top hσ (by omega) h3, T, Subgroup.closure_le]
  rintro g ⟨a, c, ha, hc, hg⟩
  by_cases ha0 : a = 0
  · have : g = 1 := by
      apply ext_smul
      intro v
      rw [hg, ha0, herm_zero_left, mul_zero, zero_smul, add_zero, one_smul]
    rw [this]
    exact (commutator (SUid σ (m + 1 + 2))).one_mem
  · obtain ⟨h, -, hh⟩ := exists_mem_T_smul_eq_of_iso hσ (by omega) W.hypA_ne_zero ha₀ ha0 ha
    have : g = h * tv hσ.invol ha₀ hc * h⁻¹ := by
      apply ext_smul
      intro v
      rw [conj_smul_of_tv h _ (tv_smul hσ.invol ha₀ hc), hh, hg]
    rw [this]
    exact (Subgroup.commutator_normal ⊤ ⊤).conj_mem _
      (tv_mem_commutator_of_perp hσ ha₀ hw ha₀w hc) h

theorem isPerfect_SUid (hσ : IsUnitaryInvolution σ) (hn : 3 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) : Group.IsPerfect (SUid σ n) :=
  ⟨commutator_SUid_eq_top hσ hn h3⟩

end CFSG.ClassicalGroups.Unitary
