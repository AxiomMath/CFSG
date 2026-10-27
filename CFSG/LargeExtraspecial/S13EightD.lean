module

public import CFSG.LargeExtraspecial.S13EightB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {K : Subgroup S.O}

theorem linearIndependent_four {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {a b c d : V}
    (ha : a ≠ 0) (hb : b ∉ (ZMod 2) ∙ a) (hc : c ∉ Submodule.span (ZMod 2) {a, b})
    (hd : d ∉ Submodule.span (ZMod 2) {a, b, c}) : LinearIndependent (ZMod 2) ![a, b, c, d] := by
  rw [Fintype.linearIndependent_iff]
  intro k hk
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at hk
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have ma : a ∈ Submodule.span (ZMod 2) ({a, b, c} : Set V) := Submodule.subset_span (by simp)
  have mb : b ∈ Submodule.span (ZMod 2) ({a, b, c} : Set V) := Submodule.subset_span (by simp)
  have mc : c ∈ Submodule.span (ZMod 2) ({a, b, c} : Set V) := Submodule.subset_span (by simp)
  have ma' : a ∈ Submodule.span (ZMod 2) ({a, b} : Set V) := Submodule.subset_span (by simp)
  have mb' : b ∈ Submodule.span (ZMod 2) ({a, b} : Set V) := Submodule.subset_span (by simp)
  have e3 : k 3 = 0 := by
    rcases h01 (k 3) with h | h
    · exact h
    · exfalso
      rw [h, one_smul] at hk
      apply hd
      rw [eq_neg_of_add_eq_zero_right hk]
      exact neg_mem (add_mem (add_mem (Submodule.smul_mem _ _ ma) (Submodule.smul_mem _ _ mb))
        (Submodule.smul_mem _ _ mc))
  rw [e3, zero_smul, add_zero] at hk
  have e2 : k 2 = 0 := by
    rcases h01 (k 2) with h | h
    · exact h
    · exfalso
      rw [h, one_smul] at hk
      apply hc
      rw [eq_neg_of_add_eq_zero_right hk]
      exact neg_mem (add_mem (Submodule.smul_mem _ _ ma') (Submodule.smul_mem _ _ mb'))
  rw [e2, zero_smul, add_zero] at hk
  have e1 : k 1 = 0 := by
    rcases h01 (k 1) with h | h
    · exact h
    · exfalso
      rw [h, one_smul] at hk
      apply hb
      rw [eq_neg_of_add_eq_zero_right hk]
      exact neg_mem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a))
  rw [e1, zero_smul, add_zero] at hk
  have e0 : k 0 = 0 := (smul_eq_zero.mp hk).resolve_right ha
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

namespace Hyp13

theorem mem_span_pair_cases {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {u v w : V}
    (hw : w ∈ Submodule.span (ZMod 2) ({u, v} : Set V)) :
    w = 0 ∨ w = u ∨ w = v ∨ w = u + v := by
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl <;> simp

theorem false_of_config' (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K)
    (hii : ∀ τ (hτ : τ ∈ S.Lbar g), τ ∉ Ebar S g K → Rbar S g τ = S.Lbar g ∨ LinCase S g hτ)
    {gA gE gU gX gF : G} (hA : ∃ h : S.M, gA = (h : G) * g) (hE : ∃ h : S.M, gE = (h : G) * g)
    (hU : ∃ h : S.M, gU = (h : G) * g) (hX : ∃ h : S.M, gX = (h : G) * g)
    (hF : ∃ h : S.M, gF = (h : G) * g)
    (hEA : S.cl (gE * S.z * gE⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gA))
    (hXA : S.cl (gX * S.z * gX⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gA))
    (hXE : S.cl (gX * S.z * gX⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gE))
    (hXU : S.cl (gX * S.z * gX⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gU))
    (hFA : S.cl (gF * S.z * gF⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gA))
    (hFE : S.cl (gF * S.z * gF⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gE))
    (hFU : S.cl (gF * S.z * gF⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa gU))
    (hXF : S.cl (gX * S.z * gX⁻¹) ∉ S.clSub (S.QG ⊓ S.Qa gF))
    (hli : LinearIndependent (ZMod 2) ![S.cl (gA * S.z * gA⁻¹), S.cl (gE * S.z * gE⁻¹),
      S.cl (gU * S.z * gU⁻¹), S.cl (gX * S.z * gX⁻¹)]) : False := by
  obtain ⟨pA, rfl⟩ := hA
  obtain ⟨pE, rfl⟩ := hE
  obtain ⟨pU, rfl⟩ := hU
  obtain ⟨pX, rfl⟩ := hX
  obtain ⟨pF, rfl⟩ := hF
  exact false_of_config hCE Y hii hEA hXA hXE hXU hFA hFE hFU hXF hli

end Hyp13

end CFSG.LargeExtraspecial.S13
