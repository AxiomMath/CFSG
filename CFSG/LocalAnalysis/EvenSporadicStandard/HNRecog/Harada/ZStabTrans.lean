module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.ZStabFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaLA

open Subgroup

private theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  have hval : c.val ≠ 0 := fun hv => h ((ZMod.val_eq_zero c).1 hv)
  have h1 : c.val = 1 := by have := ZMod.val_lt c; omega
  exact (ZMod.val_eq_one (by norm_num : 1 < 2) c).1 h1

private theorem zmod2_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  by_cases h : c = 0
  · exact Or.inl h
  · exact Or.inr (zmod2_eq_one_of_ne_zero h)

private theorem add_self_eq_zero_V6 (x : V6) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

private theorem add_add_self_V6 (x y : V6) : x + (x + y) = y := by
  rw [← add_assoc, add_self_eq_zero_V6, zero_add]

private theorem qm_zero : qm (0 : V6) = 0 := by decide

private theorem exists_omega_fix_nonsing_bil_one {w a a' : V6} (hw : qm w = 0) (hw0 : w ≠ 0)
    (ha : qm a = 1) (haw : bil a w = 0) (ha' : qm a' = 1) (ha'w : bil a' w = 0)
    (h1 : bil a a' = 1) : ∃ g ∈ OmegaMinus, g w = w ∧ g a = a' := by
  have hdq : qm (a + a') = 1 := by rw [qm_add, ha, ha', h1]; decide
  have hdw : bil (a + a') w = 0 := by rw [bil_add_left, haw, ha'w, add_zero]
  obtain ⟨c, hcq, hcw, hca'_u, hca'_u'⟩ :=
    exists_nonsing_perp_pair hw hw0 (u := a') (u' := a') ha'w ha'w
  have hwd : bil w (a + a') = 0 := by rw [bil_comm]; exact hdw
  have hwc : bil w c = 0 := by rw [bil_comm]; exact hcw
  have ha'c : bil a' c = 0 := by rw [bil_comm]; exact hca'_u
  have hda : transv (a + a') a = a' := by
    rw [transv_apply, show bil a (a + a') = 1 by rw [bil_add_right, bil_self, h1, zero_add],
      one_smul, add_add_self_V6]
  refine ⟨transv c * transv (a + a'), Subgroup.subset_closure ⟨c, a + a', hcq, hdq, rfl⟩,
    ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, transv_apply_of_bil_eq_zero hwd, transv_apply_of_bil_eq_zero hwc]
  · rw [Equiv.Perm.mul_apply, hda, transv_apply_of_bil_eq_zero ha'c]

theorem exists_omega_fix_nonsing {w a a' : V6} (hw : qm w = 0) (hw0 : w ≠ 0) (ha : qm a = 1)
    (haw : bil a w = 0) (ha' : qm a' = 1) (ha'w : bil a' w = 0) :
    ∃ g ∈ OmegaMinus, g w = w ∧ g a = a' := by
  by_cases heq : a = a'
  · exact ⟨1, one_mem _, rfl, by rw [heq, Equiv.Perm.one_apply]⟩
  · by_cases h1 : bil a a' = 1
    · exact exists_omega_fix_nonsing_bil_one hw hw0 ha haw ha' ha'w h1
    · have h0 : bil a a' = 0 := by
        rcases zmod2_eq_zero_or_one (bil a a') with h | h
        · exact h
        · exact absurd h h1
      obtain ⟨x, hxw, hxq, hax, hxa'⟩ := exists_nonsing_nbr hw hw0 haw ha'w ha ha' h0 heq
      obtain ⟨g₁, hg₁, hg₁w, hg₁a⟩ :=
        exists_omega_fix_nonsing_bil_one hw hw0 ha haw hxq hxw hax
      obtain ⟨g₂, hg₂, hg₂w, hg₂x⟩ :=
        exists_omega_fix_nonsing_bil_one hw hw0 hxq hxw ha' ha'w hxa'
      exact ⟨g₂ * g₁, mul_mem hg₂ hg₁, by rw [Equiv.Perm.mul_apply, hg₁w, hg₂w],
        by rw [Equiv.Perm.mul_apply, hg₁a, hg₂x]⟩

end CFSG.EvenSporadicStandard.HNRecog.HaradaLA
