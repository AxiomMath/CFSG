module

public import CFSG.ClassicalInvolution.SubnormalClosure.Basic
public import CFSG.Blueprint.Catalog
import CFSG.ClassicalInvolution.OrderForm
import CFSG.GroupTheory.NonabelianSimpleOrderSixty
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped MatrixGroups

@[expose] def AschbacherCIT : Prop :=
  ∀ (G : Type) [Group G] [Finite G], classicalInvolutionOddCore G = ⊥ →
    ∀ z : G, orderOf z = 2 → ∀ K : Subgroup G, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set G)) → classicalInvolutionWitness K →
    subnormalClosure K = ⊤ →
    (CFSG.Open.IsQuasisimple G ∧ (CFSG.Blueprint.OddLieType (G ⧸ Subgroup.center G) ∨
        CFSG.Blueprint.NativeSporadic.IsSporadic G .M11)) ∨
      (K = ⊤ ∧ (Nonempty (G ≃* SL(2, ZMod 3)) ∨
        (CFSG.Open.IsQuasisimple G ∧ Nat.card (Subgroup.center G) = 2 ∧
          Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 7)))))

section Witness

theorem classicalInvolutionWitness_of_mulEquiv {A B : Type*} [Group A] [Group B]
    {JA : Subgroup A} {JB : Subgroup B} (e : JA ≃* JB) (h : classicalInvolutionWitness JA) :
    classicalInvolutionWitness JB := by
  have hO : (classicalInvolutionOddCore JA).map e.toMonoidHom = classicalInvolutionOddCore JB :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  let q : JA ⧸ classicalInvolutionOddCore JA ≃* JB ⧸ classicalInvolutionOddCore JB :=
    QuotientGroup.congr _ _ e hO
  have hZ : (Subgroup.center (JA ⧸ classicalInvolutionOddCore JA)).map q.toMonoidHom =
      Subgroup.center (JB ⧸ classicalInvolutionOddCore JB) := Subgroup.map_center_eq q
  rcases h with ⟨p, n, hp, hp2, hn, ⟨φ⟩⟩ | ⟨hqs, hcard, ⟨ψ⟩⟩
  · exact Or.inl ⟨p, n, hp, hp2, hn, ⟨q.symm.trans φ⟩⟩
  · refine Or.inr ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv q.symm hqs, ?_,
      ⟨(QuotientGroup.congr _ _ q hZ).symm.trans ψ⟩⟩
    rw [← hcard, ← hZ]
    exact Subgroup.card_map_of_injective q.injective

end Witness

section Closure

variable {G : Type*} [Group G]

theorem isComponentOf_top_of_normal_simple (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a) : IsComponentOf F ⊤ := by
  have : Group.IsPerfect F :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top F hFnonab⟩
  exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
    CFSG.ComponentClassification.Quasisimple.simple_of_perfect F⟩

theorem le_subnormalClosure_of_isComponentOf [Finite G] {F K : Subgroup G}
    (hF : IsComponentOf F ⊤) (hC : Subgroup.centralizer (F : Set G) = ⊥) (hK : K ≠ ⊥) :
    F ≤ subnormalClosure K := by
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes F
      (subnormalClosure K) hF (isSubnormal_subnormalClosure K) with h | h
  · exact h
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at h
    exact (hK (le_bot_iff.mp ((le_subnormalClosure K).trans h))).elim

theorem eq_of_isQuasisimple_of_le {F H : Subgroup G} [F.Normal] (hFH : F ≤ H)
    (hH : CFSG.Open.IsQuasisimple H) (hFnonab : ∃ a b : F, a * b ≠ b * a) : H = F := by
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hH
    (F.subgroupOf H) with hcen | htop
  · obtain ⟨a, b, hab⟩ := hFnonab
    refine (hab ?_).elim
    have := Subgroup.mem_center_iff.mp (hcen (show (⟨a.1, hFH a.2⟩ : H) ∈ F.subgroupOf H from a.2))
      ⟨b.1, hFH b.2⟩
    exact Subtype.ext (congrArg Subtype.val this).symm
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hFH

theorem subgroupOf_centralizer_inf {H : Subgroup G} {z : G} (hz : z ∈ H) :
    (Subgroup.centralizer ({z} : Set G) ⊓ H).subgroupOf H =
      Subgroup.centralizer ({(⟨z, hz⟩ : H)} : Set H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩

end Closure

theorem card_specialLinearGroup_zmod_three : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Matrix.card_SL_field (𝔽 := ZMod 3) 2, ZMod.card, Fin.prod_univ_two]
  norm_num

theorem oddLieType_or_isSporadic_of_aschbacherCIT (hCIT : AschbacherCIT) {G : Type} [Group G]
    [Finite G] (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a) (hC : Subgroup.centralizer (F : Set G) = ⊥)
    (hO : classicalInvolutionOddCore G = ⊥) {z : G} (hz : orderOf z = 2) {J : Subgroup G}
    (hzJ : z ∈ J) (hJ : IsSubnormal J (Subgroup.centralizer ({z} : Set G)))
    (hw : classicalInvolutionWitness J) :
    CFSG.Blueprint.OddLieType F ∨ CFSG.Blueprint.NativeSporadic.IsSporadic F .M11 := by
  have hZ : Subgroup.center F = ⊥ :=
    CFSG.ComponentClassification.Helpers.center_eq_bot F hFnonab
  have hJbot : J ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.mem_bot] at hzJ
    rw [hzJ, orderOf_one] at hz
    exact absurd hz (by norm_num)
  obtain ⟨H, hHsub, hJH, hcl, hFH⟩ : ∃ H : Subgroup G, IsSubnormal H ⊤ ∧ J ≤ H ∧
      subnormalClosure (J.subgroupOf H) = ⊤ ∧ F ≤ H :=
    ⟨subnormalClosure J, isSubnormal_subnormalClosure J, le_subnormalClosure J,
      subnormalClosure_subgroupOf_subnormalClosure J,
      le_subnormalClosure_of_isComponentOf (isComponentOf_top_of_normal_simple F hFnonab) hC hJbot⟩
  have hzH : z ∈ H := hJH hzJ
  have hOH : classicalInvolutionOddCore H = ⊥ :=
    CFSG.ComponentClassification.OddCore.subnormal_corefree hO H hHsub
  have hJ' : IsSubnormal (J.subgroupOf H) (Subgroup.centralizer ({(⟨z, hzH⟩ : H)} : Set H)) := by
    have h1 : IsSubnormal J (Subgroup.centralizer ({z} : Set G) ⊓ H) := by
      have := isSubnormal_inf hJ H
      rwa [inf_eq_left.mpr hJH] at this
    rw [← subgroupOf_centralizer_inf hzH]
    exact isSubnormal_subgroupOf h1 H
  have hw' : classicalInvolutionWitness (J.subgroupOf H) :=
    classicalInvolutionWitness_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJH).symm hw
  rcases hCIT H hOH ⟨z, hzH⟩ (by rwa [Subgroup.orderOf_mk]) (J.subgroupOf H)
      (Subgroup.mem_subgroupOf.mpr hzJ) hJ' hw' hcl with ⟨hq, hlie⟩ | ⟨-, hSL | ⟨hq, hcard, -⟩⟩
  · obtain rfl := eq_of_isQuasisimple_of_le hFH hq hFnonab
    let e : H ⧸ Subgroup.center H ≃* H :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact hlie.imp (oddLieType_congr e).mp id
  · obtain ⟨e⟩ := hSL
    have hdvd : Nat.card F ∣ 24 := by
      rw [← card_specialLinearGroup_zmod_three, ← Nat.card_congr e.toEquiv]
      exact Subgroup.card_dvd_of_le hFH
    have h60 := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty ‹IsSimpleGroup F›
      hFnonab
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  · obtain rfl := eq_of_isQuasisimple_of_le hFH hq hFnonab
    rw [hZ, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)

end CFSG.ClassicalInvolution
