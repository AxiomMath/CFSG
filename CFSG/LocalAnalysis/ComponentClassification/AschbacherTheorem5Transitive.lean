module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveCases

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

open SectionSix SectionSix.BarTools

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

theorem lemma_6_3 (h3 : AschbacherTheorem3.Theorem3Statement) (hin : SectionSixInputs)
    (hC : Counterexample G D r Abar) (i j : Fin r) :
    ∃ h ∈ Subgroup.normalizer (D : Set G),
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hj : j ∉ orbit D Abar i := hne
  obtain ⟨hI, hiq⟩ := orbit_singleton hC h3 hin (orbit_isInvariant i) (mem_orbit_self i) hj
  obtain ⟨hJ, hjq⟩ := orbit_singleton hC h3 hin (orbit_compl_isInvariant i) (k := j) hj
    (fun h => h (mem_orbit_self i))
  have hij : i ≠ j := fun h => hj (h ▸ mem_orbit_self i)
  set H := Subgroup.normalizer (D : Set G) with hHdef
  set Ai := aschbacherThm5Preimage D (Abar i) with hAidef
  set Aj := aschbacherThm5Preimage D (Abar j) with hAjdef
  have hHi : H ≤ Subgroup.normalizer (Ai : Set G) := by
    intro h hh
    obtain ⟨l, hl⟩ := hC.hyp.hperm h hh i
    have hlI : l ∈ orbit D Abar i := ⟨h, hh, hl⟩
    rw [hI, Set.mem_singleton_iff] at hlI
    rw [hlI] at hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hl
  have hHj : H ≤ Subgroup.normalizer (Aj : Set G) := by
    intro h hh
    obtain ⟨l, hl⟩ := hC.hyp.hperm h hh j
    have hlJ : l ∈ (orbit D Abar i)ᶜ := orbit_compl_isInvariant i h hh j hj l hl
    rw [hJ, Set.mem_singleton_iff] at hlJ
    rw [hlJ] at hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hl
  have hall : ∀ l, l = i ∨ l = j := by
    intro l
    by_cases hl : l ∈ orbit D Abar i
    · rw [hI] at hl
      exact Or.inl hl
    · have hl' : l ∈ (orbit D Abar i)ᶜ := hl
      rw [hJ] at hl'
      exact Or.inr hl'
  have hAiH : Ai ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hAjH : Aj ≤ H := (preimage_le D _).trans Subgroup.le_normalizer
  have hnotin : ∀ {x y : Fin r}, x ≠ y → ∀ {R : Subgroup (Bar D)},
      IsSylowOf 2 R (bar D (aschbacherThm5Preimage D (Abar y))) →
      AschbacherTheorem3.IsDihedralTwoGroup R → ∀ {z : G},
      z ∈ aschbacherThm5Preimage D (Abar x) → orderOf z = 2 →
      z ∉ aschbacherThm5Preimage D (Abar y) := by
    intro x y hxy R hR hRd z hzx hz hzy
    have hzH : z ∈ H := (preimage_le D _).trans Subgroup.le_normalizer hzx
    have hzC : toBar D ⟨z, hzH⟩ ∈
        Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar y)) : Set (Bar D)) :=
      (centralizes_iff_mem_centralizer D _ (preimage_le D _) ⟨z, hzH⟩).mp
        (centralizes_of_mem_centralizing (factor_le_centralizing hC.hyp.hcomm (Ne.symm hxy) hzx))
    have hz2 : toBar D ⟨z, hzH⟩ ^ 2 = 1 := by
      rw [← map_pow, show (⟨z, hzH⟩ : H) ^ 2 = 1 from
        Subtype.ext (TwoGroups.sq_eq_one_of_orderOf hz), map_one]
    have h1 := Factor.no_central_involution hC.hyp y hR hRd (toBar_mem_bar D hzy) hzC hz2
    exact TwoGroups.ne_one_of_orderOf hz (Strong.eq_one_of_mem_core_of_sq
      ((toBar_eq_one_iff D _).mp h1) (TwoGroups.sq_eq_one_of_orderOf hz))
  obtain ⟨Ri, hRi, hRit⟩ := Factor.factor_type hC h3 hin hij hHi hiq
  obtain ⟨Rj, hRj, hRjt⟩ := Factor.factor_type hC h3 hin hij.symm hHj hjq
  rcases hRit with hRiq | hRid
  · obtain ⟨zi, hziA, hzi, hzic⟩ := Factor.exists_central_involution hC.hyp i hRi hRiq
    by_cases hziB : zi ∈ Aj
    · rcases hRjt with hRjq | hRjd
      ·
        have hr2 : r = 2 := by
          have h2 := two_le hC
          by_contra hne2
          rcases hall ⟨0, by omega⟩ with h0 | h0 <;> rcases hall ⟨1, by omega⟩ with h1 | h1 <;>
            rcases hall ⟨2, by omega⟩ with h2' | h2' <;>
          · have v0 := congrArg Fin.val h0
            have v1 := congrArg Fin.val h1
            have v2 := congrArg Fin.val h2'
            simp only at v0 v1 v2
            omega
        subst hr2
        have hrank : ∀ l, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar l)) ≤ 1 := by
          intro l
          rcases hall l with rfl | rfl
          · exact Factor.pRank_le_one_of_quaternion hAiH hRi hRiq
          · exact Factor.pRank_le_one_of_quaternion hAjH hRj hRjq
        have hzA : ∀ l, zi ∈ aschbacherThm5Preimage D (Abar l) := by
          intro l
          rcases hall l with rfl | rfl
          · exact hziA
          · exact hziB
        exact hC.fails (conclusion_of_shared_involution hC.hyp hrank hzi hzA)
      · exact hnotin hij hRj hRjd hziA hzi hziB
    · exact Cases.not_central_outside hC h3 hin hij hHi hHj hjq hziA hzi hzic hziB
  · rcases hRjt with hRjq | hRjd
    · obtain ⟨zj, hzjA, hzj, hzjc⟩ := Factor.exists_central_involution hC.hyp j hRj hRjq
      by_cases hzjB : zj ∈ Ai
      · exact hnotin hij.symm hRi hRid hzjA hzj hzjB
      · exact Cases.not_central_outside hC h3 hin hij.symm hHj hHi hiq hzjA hzj hzjc hzjB
    · exact Cases.not_dihedral hC h3 hin hij hHi hHj hiq hRi hRid

end CFSG.ComponentClassification.AschbacherTheorem5
