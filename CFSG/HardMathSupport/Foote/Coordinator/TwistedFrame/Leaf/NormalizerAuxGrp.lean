module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.OuterSL

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.ComponentClassification.OuterAutomorphisms (Outer solvable_of_equiv solvable_of_centerQuotient)
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame (commutatorElement_mul_eq isQuasisimple_SL)
open Subgroup
open scoped MatrixGroups commutatorElement

section Central

variable {G : Type*} [Group G]

theorem mem_center_of_commutator_mem_central [Group.IsPerfect G] {Z₀ : Subgroup G}
    (hZ : Z₀ ≤ center G) {g : G} (h : ∀ x : G, ⁅g, x⁆ ∈ Z₀) : g ∈ center G := by
  have hconj : ∀ a : G, MulAut.conj g a = a * ⁅g, a⁆ := by
    intro a
    have hc : a * ⁅g, a⁆ = ⁅g, a⁆ * a := (mem_center_iff.1 (hZ (h a)) a)
    rw [hc, MulAut.conj_apply, commutatorElement_def]
    group
  have hfix : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ (MulAut.conj g : G →* G).eqLocus (MonoidHom.id _) := by
    rw [commutator_le]
    intro a _ b _
    show MulAut.conj g ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hconj a, hconj b]
    exact commutatorElement_mul_eq ((mem_center_iff.1 (hZ (h a)) b).symm)
      ((mem_center_iff.1 (hZ (h b)) a).symm) ((mem_center_iff.1 (hZ (h a)) _).symm)
  rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top] at hfix
  rw [mem_center_iff]
  intro x
  have hx : MulAut.conj g x = x := hfix (mem_top x)
  rw [MulAut.conj_apply] at hx
  calc x * g = g * x * g⁻¹ * g := by rw [hx]
    _ = g * x := by group

theorem center_quotient_eq_map [Group.IsPerfect G] {Z₀ : Subgroup G} [Z₀.Normal]
    (hZ : Z₀ ≤ center G) :
    center (G ⧸ Z₀) = (center G).map (QuotientGroup.mk' Z₀) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    refine ⟨g, mem_center_of_commutator_mem_central hZ fun h => ?_, rfl⟩
    have hc : (QuotientGroup.mk h : G ⧸ Z₀) * QuotientGroup.mk g =
        QuotientGroup.mk g * QuotientGroup.mk h := mem_center_iff.1 hx (QuotientGroup.mk h)
    rw [← QuotientGroup.eq_one_iff]
    have e : (QuotientGroup.mk ⁅g, h⁆ : G ⧸ Z₀) =
        ⁅(QuotientGroup.mk g : G ⧸ Z₀), QuotientGroup.mk h⁆ :=
      map_commutatorElement (QuotientGroup.mk' Z₀) g h
    rw [e, commutatorElement_eq_one_iff_commute]
    exact hc.symm
  · rintro _ ⟨g, hg, rfl⟩
    rw [mem_center_iff]
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
    show QuotientGroup.mk h * QuotientGroup.mk g = QuotientGroup.mk g * QuotientGroup.mk h
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hg h]

noncomputable def centerQuotientQuotientEquiv [Group.IsPerfect G] {Z₀ : Subgroup G} [Z₀.Normal]
    (hZ : Z₀ ≤ center G) : ((G ⧸ Z₀) ⧸ center (G ⧸ Z₀)) ≃* G ⧸ center G :=
  (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map hZ)).trans
    (QuotientGroup.quotientQuotientEquivQuotient Z₀ (center G) hZ)

theorem outer_solvable_of_central_quotient [Group.IsPerfect G] {Z₀ : Subgroup G} [Z₀.Normal]
    (hZ : Z₀ ≤ center G) (h : Group.IsSolvable (Outer (G ⧸ center G))) :
    Group.IsSolvable (Outer (G ⧸ Z₀)) := by
  haveI : Group.IsPerfect (G ⧸ Z₀) := inferInstance
  haveI : Group.IsSolvable (Outer (G ⧸ center G)) := h
  haveI : Group.IsSolvable (Outer ((G ⧸ Z₀) ⧸ center (G ⧸ Z₀))) :=
    solvable_of_equiv (centerQuotientQuotientEquiv hZ).symm
  exact solvable_of_centerQuotient _

end Central

section SL

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type*} [Field K] [Finite K] {n : ℕ}

theorem isSolvable_out_projectiveSL (hn : 3 ≤ n) :
    Group.IsSolvable (Outer (projectiveSL n K)) := by
  refine ⟨⟨3, ?_⟩⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective _), eq_bot_iff]
  rintro _ ⟨φ, hφ, rfl⟩
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have htop := (automorphism_generation (K := K) hn).1
  have hR := (standard_outer_quotients (n := n) (K := K)).2.2.2.2.2.2.2.2.2
  have h3 : derivedSeries (MulAut (projectiveSL n K)) 3 ≤
      (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    simp only [derivedSeries_succ, derivedSeries_zero]
    rw [← htop]
    exact hR
  exact h3 hφ

theorem isSolvable_out_SL_centerQuotient (hn : 3 ≤ n) :
    Group.IsSolvable (Outer (SL(n, K) ⧸ center SL(n, K))) := by
  haveI := isSolvable_out_projectiveSL (K := K) hn
  exact solvable_of_equiv (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center n K))

theorem outer_solvable_SL_quotient (hn : 3 ≤ n) {Z₀ : Subgroup SL(n, K)} [Z₀.Normal]
    (hZ : Z₀ ≤ center SL(n, K)) : Group.IsSolvable (Outer (SL(n, K) ⧸ Z₀)) := by
  haveI : Group.IsPerfect SL(n, K) := (isQuasisimple_SL hn).1
  exact outer_solvable_of_central_quotient hZ (isSolvable_out_SL_centerQuotient hn)

end SL

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux
