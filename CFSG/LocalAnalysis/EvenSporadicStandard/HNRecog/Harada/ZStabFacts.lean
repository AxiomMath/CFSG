module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaData.LinearAlgebra.OrthData

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

set_option maxRecDepth 100000
set_option synthInstance.maxSize 256

theorem exists_nonsing_perp (x : V6) : ∃ c : V6, qm c = 1 ∧ bil c x = 0 := by
  have key : ∀ x : V6, ∃ c : V6, qm c = 1 ∧ bil c x = 0 := by decide +kernel
  exact key x

theorem exists_common_neighbor {u v : V6} (hu : qm u = 0) (hv : qm v = 0) (hu0 : u ≠ 0)
    (hv0 : v ≠ 0) (huv : bil u v = 0) (hne : u ≠ v) :
    ∃ x : V6, qm x = 0 ∧ x ≠ 0 ∧ bil u x = 1 ∧ bil x v = 1 := by
  have key : ∀ u v : V6, qm u = 0 → qm v = 0 → u ≠ 0 → v ≠ 0 → bil u v = 0 → u ≠ v →
      ∃ x : V6, qm x = 0 ∧ x ≠ 0 ∧ bil u x = 1 ∧ bil x v = 1 := by decide +kernel
  exact key u v hu hv hu0 hv0 huv hne

def wZero : V6 := Pi.single 0 1

theorem qm_wZero : qm wZero = 0 := by decide

theorem wZero_ne_zero : wZero ≠ 0 := by decide

private theorem pair_wZero : ∀ u u' : V6, bil u wZero = 0 → bil u' wZero = 0 →
    ∃ t' : V6, qm t' = 1 ∧ bil t' wZero = 0 ∧ bil t' u = 0 ∧ bil t' u' = 0 := by
  decide +kernel

private theorem nbr_wZero : ∀ t₁ : V6, bil t₁ wZero = 0 → qm t₁ = 1 → ∀ t₂ : V6,
    bil t₂ wZero = 0 → qm t₂ = 1 → bil t₁ t₂ = 0 → t₁ ≠ t₂ →
    ∃ x : V6, bil x wZero = 0 ∧ qm x = 1 ∧ bil t₁ x = 1 ∧ bil x t₂ = 1 := by
  decide +kernel

private theorem add_add_self_V6 (x y : V6) : x + (x + y) = y := by
  funext i
  simp only [Pi.add_apply]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem omegaMinus_le_orthMinus : OmegaMinus ≤ OrthMinus := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨u, v, hu, hv, rfl⟩
  exact mul_mem (transv_mem_orthOf isQF_qm hu) (transv_mem_orthOf isQF_qm hv)

theorem bil_apply_of_mem_omegaMinus {g : Equiv.Perm V6} (hg : g ∈ OmegaMinus) (x y : V6) :
    bil (g x) (g y) = bil x y :=
  bil_apply_of_mem_orthOf isQF_qm (omegaMinus_le_orthMinus hg) x y

theorem qm_apply_of_mem_omegaMinus {g : Equiv.Perm V6} (hg : g ∈ OmegaMinus) (x : V6) :
    qm (g x) = qm x :=
  (omegaMinus_le_orthMinus hg).2 x

private theorem exists_omega_map_of_bil_one {w w' : V6} (hw : qm w = 0) (hw' : qm w' = 0)
    (h : bil w w' = 1) : ∃ g ∈ OmegaMinus, g w = w' := by
  obtain ⟨c, hc1, hc0⟩ := exists_nonsing_perp w'
  have ha : qm (w + w') = 1 := by
    rw [qm_add, hw, hw', h]
    decide
  refine ⟨transv c * transv (w + w'), Subgroup.subset_closure ⟨c, w + w', hc1, ha, rfl⟩, ?_⟩
  have h1 : transv (w + w') w = w' := by
    rw [transv_apply, bil_add_right, bil_self, h, zero_add, one_smul, add_add_self_V6]
  rw [Equiv.Perm.mul_apply, h1, transv_apply_of_bil_eq_zero (by rw [bil_comm]; exact hc0)]

theorem exists_omegaMinus_singular_map {w w' : V6} (hw : qm w = 0) (hw0 : w ≠ 0)
    (hw' : qm w' = 0) (hw0' : w' ≠ 0) : ∃ g ∈ OmegaMinus, g w = w' := by
  by_cases hee : w = w'
  · exact ⟨1, one_mem _, by rw [hee]; rfl⟩
  · by_cases h1 : bil w w' = 1
    · exact exists_omega_map_of_bil_one hw hw' h1
    · have h0 : bil w w' = 0 := by
        revert h1
        generalize bil w w' = c
        revert c
        decide
      obtain ⟨x, hxq, -, hwx, hxw'⟩ := exists_common_neighbor hw hw' hw0 hw0' h0 hee
      obtain ⟨g₁, hg₁, hg₁w⟩ := exists_omega_map_of_bil_one hw hxq hwx
      obtain ⟨g₂, hg₂, hg₂x⟩ := exists_omega_map_of_bil_one hxq hw' hxw'
      exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [Equiv.Perm.mul_apply, hg₁w, hg₂x]⟩

theorem exists_nonsing_perp_pair {w : V6} (hw : qm w = 0) (hw0 : w ≠ 0) {u u' : V6}
    (hu : bil u w = 0) (hu' : bil u' w = 0) :
    ∃ t' : V6, qm t' = 1 ∧ bil t' w = 0 ∧ bil t' u = 0 ∧ bil t' u' = 0 := by
  obtain ⟨g, hg, hgw⟩ := exists_omegaMinus_singular_map hw hw0 qm_wZero wZero_ne_zero
  have hb := bil_apply_of_mem_omegaMinus hg
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := pair_wZero (g u) (g u') (by rw [← hgw, hb]; exact hu)
    (by rw [← hgw, hb]; exact hu')
  have hs : g (g⁻¹ s) = s := by simp
  refine ⟨g⁻¹ s, ?_, ?_, ?_, ?_⟩
  · rw [← qm_apply_of_mem_omegaMinus hg, hs]; exact hs1
  · rw [← hb (g⁻¹ s) w, hs, hgw]; exact hs2
  · rw [← hb (g⁻¹ s) u, hs]; exact hs3
  · rw [← hb (g⁻¹ s) u', hs]; exact hs4

theorem exists_nonsing_nbr {w t₁ t₂ : V6} (hw : qm w = 0) (hw0 : w ≠ 0) (h₁ : bil t₁ w = 0)
    (h₂ : bil t₂ w = 0) (q₁ : qm t₁ = 1) (q₂ : qm t₂ = 1) (h12 : bil t₁ t₂ = 0) (hne : t₁ ≠ t₂) :
    ∃ x : V6, bil x w = 0 ∧ qm x = 1 ∧ bil t₁ x = 1 ∧ bil x t₂ = 1 := by
  obtain ⟨g, hg, hgw⟩ := exists_omegaMinus_singular_map hw hw0 qm_wZero wZero_ne_zero
  have hb := bil_apply_of_mem_omegaMinus hg
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := nbr_wZero (g t₁) (by rw [← hgw, hb]; exact h₁)
    (by rw [qm_apply_of_mem_omegaMinus hg]; exact q₁) (g t₂) (by rw [← hgw, hb]; exact h₂)
    (by rw [qm_apply_of_mem_omegaMinus hg]; exact q₂) (by rw [hb]; exact h12)
    (fun h => hne (g.injective h))
  have hs : g (g⁻¹ s) = s := by simp
  refine ⟨g⁻¹ s, ?_, ?_, ?_, ?_⟩
  · rw [← hb (g⁻¹ s) w, hs, hgw]; exact hs1
  · rw [← qm_apply_of_mem_omegaMinus hg, hs]; exact hs2
  · rw [← hb t₁ (g⁻¹ s), hs]; exact hs3
  · rw [← hb (g⁻¹ s) t₂, hs]; exact hs4

theorem eq_zero_or_eq_of_perp_perp {w v : V6} (hw : qm w = 0) (hw0 : w ≠ 0) (hv : bil v w = 0)
    (h : ∀ u, bil u w = 0 → bil v u = 0) : v = 0 ∨ v = w := by
  have key : ∀ w : V6, qm w = 0 → w ≠ 0 → ∀ v : V6, bil v w = 0 →
      (∀ u : V6, bil u w = 0 → bil v u = 0) → v = 0 ∨ v = w := by decide +kernel
  exact key w hw hw0 v hv h

theorem card_singular : (Finset.univ.filter fun x : V6 => qm x = 0 ∧ x ≠ 0).card = 27 := by
  decide +kernel

theorem card_perp {w : V6} (hw0 : w ≠ 0) :
    (Finset.univ.filter fun x : V6 => bil x w = 0).card = 32 := by
  have key : ∀ w : V6, w ≠ 0 → (Finset.univ.filter fun x : V6 => bil x w = 0).card = 32 := by
    decide +kernel
  exact key w hw0

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
