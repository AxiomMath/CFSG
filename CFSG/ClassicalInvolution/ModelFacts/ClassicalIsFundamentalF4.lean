module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalF4Short
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalRootGrading

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.RootSystem

section Longest

variable {K : Type} [Field K]

theorem iform_weylAction {τ : Tag} (hA : TauCeti.IsFiniteType τ.cartan)
    (w : (coxeterMatrix hA).Group) (v : Fin τ.rank → ℤ) :
    iform (weylAction hA w v) (weylAction hA w v) = iform v v := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one => simp
  | mul_simple_left w i ih =>
    rw [weylAction_mul_apply, weylAction_simple_eq_reflect hA, iform_reflect, ih]

theorem lt_two_of_iform_single_F4 {j : Fin Tag.F4.rank}
    (h : iform (Pi.single j 1 : Fin Tag.F4.rank → ℤ) (Pi.single j 1) = 4) : j.val < 2 := by
  rw [iform_single_single] at h
  revert h
  fin_cases j <;> decide

theorem isLongestRoot_f4Datum_of_iform_eq_four {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot .F4 γ)
    (h : iform γ γ = 4) : IsLongestRoot (f4Datum K) γ := by
  rcases (mem_adjDatum_roots.2 hγ : γ ∈ (f4Datum K).roots) with
    ⟨w, j, rfl⟩ | ⟨w, j, hj, rfl⟩
  · have hinv := iform_weylAction (isFiniteType_cartan .F4) w (Pi.single j 1)
    rw [hinv] at h
    exact (isLongest_single_F4 rfl _ (lt_two_of_iform_single_F4 h)).map_weylAction w
  · exact absurd hj (Set.notMem_empty j)

end Longest

section Tag

variable {p f : ℕ} [Fact p.Prime]

theorem classicalMembersFundamental_f4 {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ClassicalMembersFundamental p f .F4 n f hp := by
  intro L z hL
  obtain ⟨g, b, γ, hγ, hLeq, hclass⟩ := exists_conj_eq_rootGroup_sup_of_isClassicalMember
    (τ := .F4) (Or.inr (Or.inl rfl)) hp2 hq hL
  have hlong : iform γ γ = 4 := by
    rcases iform_self_F4 hγ.1 with h2 | h4
    · exfalso
      obtain ⟨δ, hδ, hδγ, hδγ', hδker, hδ0⟩ :=
        F4_short_root_has_nonorthogonal_kernel_root (signTupleBits b) hγ.1 h2 hγ.2
      have hcls : (⟦⟨γ, hγ⟩⟧ : KernelComponent (maskChar (signTupleBits b))) =
          ⟦⟨δ, ⟨hδ, hδker⟩⟩⟧ := mk_eq_of_iform_ne_zero hδ0
      have hle := rootSubgroup_le_componentRootSpan (GaloisField p f)
        (⟨δ, ⟨hδ, hδker⟩⟩ : kernelRoots (maskChar (signTupleBits b)))
      rw [← hcls, hclass] at hle
      exact not_rootSubgroup_le_rootSubgroup_sup hγ.1 hδ hδγ hδγ' hle
    · exact h4
  exact ⟨g⁻¹, γ, Or.inl (isLongestRoot_f4Datum_of_iform_eq_four hγ.1 hlong), hLeq⟩

end Tag

end CFSG.ClassicalInvolution.ModelFacts
