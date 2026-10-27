module

import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open scoped RealInnerProductSpace

variable {J : Type*} [DecidableEq J]

theorem ofLp_single_sub_single_apply (a b c : J) :
    WithLp.ofLp (EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1
        : EuclideanSpace ℝ J) c
      = (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
  simp [PiLp.single_apply]

theorem eq_and_eq_of_single_sub_single_eq {a b c d : J} (hab : a ≠ b)
    (h : (EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ J)
      = EuclideanSpace.single c 1 - EuclideanSpace.single d 1) : a = c ∧ b = d := by
  have h1 := congrArg (fun v : EuclideanSpace ℝ J => WithLp.ofLp v a) h
  have h2 := congrArg (fun v : EuclideanSpace ℝ J => WithLp.ofLp v b) h
  simp only [ofLp_single_sub_single_apply, if_pos, if_neg hab, if_neg hab.symm] at h1 h2
  refine ⟨?_, ?_⟩
  · by_contra hac
    rw [if_neg hac] at h1
    split_ifs at h1 <;> norm_num at h1
  · by_contra hbd
    rw [if_neg hbd] at h2
    split_ifs at h2 <;> norm_num at h2

private theorem exists_of_forall_eq_smul {R : Finset (EuclideanSpace ℝ J)} (ε : ℝ)
    (hε : ε = 1 ∨ ε = -1) (j₀ : J)
    (h : ∀ r ∈ R, ∃ x : J, x ≠ j₀ ∧ r = ε • (EuclideanSpace.single x (1 : ℝ)
      - EuclideanSpace.single j₀ 1)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ j₀ : J, ∃ j : R → J, Function.Injective j ∧
      (∀ r : R, j r ≠ j₀) ∧ ∀ r : R, (r : EuclideanSpace ℝ J)
        = ε • (EuclideanSpace.single (j r) (1 : ℝ) - EuclideanSpace.single j₀ 1) := by
  refine ⟨ε, hε, j₀, fun r => (h r r.2).choose, ?_, fun r => (h r r.2).choose_spec.1,
    fun r => (h r r.2).choose_spec.2⟩
  intro r s hrs
  refine Subtype.ext ?_
  rw [(h r r.2).choose_spec.2, (h s s.2).choose_spec.2]
  simp only at hrs
  rw [hrs]

variable [Fintype J]

theorem inner_single_sub_single (a b c d : J) :
    ⟪(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ J),
        EuclideanSpace.single c 1 - EuclideanSpace.single d 1⟫
      = ((if a = c then 1 else 0) - (if a = d then 1 else 0))
        - ((if b = c then 1 else 0) - (if b = d then 1 else 0)) := by
  simp [inner_sub_left, EuclideanSpace.inner_single_left]

theorem inner_single_sub_single_eq_one_iff {a b c d : J} (hab : a ≠ b) (hcd : c ≠ d) :
    ⟪(EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1 : EuclideanSpace ℝ J),
        EuclideanSpace.single c 1 - EuclideanSpace.single d 1⟫ = 1
      ↔ (a = c ∧ b ≠ d) ∨ (a ≠ c ∧ b = d) := by
  rw [inner_single_sub_single]
  split_ifs <;> simp_all <;> norm_num

theorem exists_common_endpoint_of_pairwise_inner_eq_one (R : Finset (EuclideanSpace ℝ J))
    (hform : ∀ r ∈ R, ∃ a b : J, a ≠ b ∧
      r = EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single b 1)
    (hinner : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → ⟪r, s⟫ = 1) (hR : R.Nonempty) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ j₀ : J, ∃ j : R → J, Function.Injective j ∧
      (∀ r : R, j r ≠ j₀) ∧ ∀ r : R, (r : EuclideanSpace ℝ J)
        = ε • (EuclideanSpace.single (j r) (1 : ℝ) - EuclideanSpace.single j₀ 1) := by
  obtain ⟨r₀, hr₀R⟩ := hR
  obtain ⟨a, b, hab, hr₀⟩ := hform r₀ hr₀R
  set T1 : EuclideanSpace ℝ J → Prop := fun s => ∃ c : J, c ≠ a ∧ c ≠ b ∧
    s = EuclideanSpace.single a (1 : ℝ) - EuclideanSpace.single c 1
  set T2 : EuclideanSpace ℝ J → Prop := fun s => ∃ d : J, d ≠ a ∧ d ≠ b ∧
    s = EuclideanSpace.single d (1 : ℝ) - EuclideanSpace.single b 1
  have hclass : ∀ s ∈ R, s ≠ r₀ → T1 s ∨ T2 s := by
    intro s hs hne
    obtain ⟨c, d, hcd, hsc⟩ := hform s hs
    have h := hinner s hs r₀ hr₀R hne
    rw [hsc, hr₀, inner_single_sub_single_eq_one_iff hcd hab] at h
    rcases h with ⟨hca, hdb⟩ | ⟨hca, hdb⟩
    · exact Or.inl ⟨d, hca ▸ hcd.symm, hdb, by rw [hsc, hca]⟩
    · exact Or.inr ⟨c, hca, hdb ▸ hcd, by rw [hsc, hdb]⟩
  have hexcl : ∀ s ∈ R, T1 s → ∀ t ∈ R, ¬ T2 t := by
    rintro s hs ⟨c, hca, hcb, hsc⟩ t ht ⟨d, hda, hdb, htd⟩
    have hst : s ≠ t := by
      rw [hsc, htd]
      intro hcon
      exact hda ((eq_and_eq_of_single_sub_single_eq hca.symm hcon).1).symm
    have h := hinner s hs t ht hst
    rw [hsc, htd, inner_single_sub_single_eq_one_iff hca.symm hdb] at h
    rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hda h1.symm
    · exact hcb h2
  by_cases hcase : ∃ s ∈ R, T1 s
  ·
    obtain ⟨s, hs, hsT1⟩ := hcase
    refine exists_of_forall_eq_smul (-1) (Or.inr rfl) a ?_
    intro r hr
    by_cases hrr₀ : r = r₀
    · exact ⟨b, hab.symm, by rw [hrr₀, hr₀, neg_one_smul, neg_sub]⟩
    · rcases hclass r hr hrr₀ with ⟨c, hca, -, hrc⟩ | h2
      · exact ⟨c, hca, by rw [hrc, neg_one_smul, neg_sub]⟩
      · exact absurd h2 (hexcl s hs hsT1 r hr)
  ·
    refine exists_of_forall_eq_smul 1 (Or.inl rfl) b ?_
    intro r hr
    by_cases hrr₀ : r = r₀
    · exact ⟨a, hab, by rw [hrr₀, hr₀, one_smul]⟩
    · rcases hclass r hr hrr₀ with h1 | ⟨d, -, hdb, hrd⟩
      · exact absurd ⟨r, hr, h1⟩ hcase
      · exact ⟨d, hdb, by rw [hrd, one_smul]⟩

end

end CFSG.FeitThompson
