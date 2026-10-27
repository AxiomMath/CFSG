module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes
public import CFSG.LocalAnalysis.ComponentInitial.LocalBMaximalPropagation

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatLeaf (ProperFixedComponent)

noncomputable def quotCenterCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr (center A) (center B) e (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (MulEquivClass.apply_mem_center_iff e).2 hx
    · intro hy
      refine ⟨e.symm y, (MulEquivClass.apply_mem_center_iff e).1 ?_, e.apply_symm_apply y⟩
      rw [e.apply_symm_apply]
      exact hy)

variable {G : Type} [Group G]

structure Hyp (N : Subgroup G) [N.Normal] (α : G) (J : Subgroup G) : Prop where
  simple : IsSimpleGroup N
  centralizer_eq : centralizer (N : Set G) = ⊥
  order_two : orderOf α = 2
  le_N : J ≤ N
  le_C : J ≤ centralizer ({α} : Set G)
  component : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))
  lie : Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 3 2 2

variable {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

abbrev beta (N : Subgroup G) [N.Normal] (α : G) : MulAut N :=
  MulAut.conjNormal α

theorem coe_beta_apply (x : N) : ((beta N α x : N) : G) = α * x * α⁻¹ :=
  MulAut.conjNormal_apply α x

theorem mem_fixedSubgroup_beta {x : N} :
    x ∈ fixedSubgroup (beta N α) ↔ (x : G) ∈ centralizer ({α} : Set G) := by
  change beta N α x = x ↔ _
  rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, coe_beta_apply]
  constructor
  · intro h
    calc (x : G) * α = α * x * α⁻¹ * α := by rw [h]
      _ = α * x := by group
  · intro h
    rw [← h]
    group

theorem fixedSubgroup_beta :
    fixedSubgroup (beta N α) = (centralizer ({α} : Set G)).subgroupOf N := by
  ext x
  rw [mem_fixedSubgroup_beta, mem_subgroupOf]

theorem conjNormal_injective (hC : centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgC : g ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) hg
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * g = g * x * g⁻¹ * g := by rw [h1]
      _ = g * x := by group
  rw [hC, mem_bot] at hgC
  exact hgC

namespace Hyp

variable (h : Hyp N α J)
include h

theorem ne_one : α ≠ 1 := by
  intro h1
  have := h.order_two
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

theorem beta_sq : beta N α * beta N α = 1 := by
  rw [← map_mul, ← sq, ← h.order_two, pow_orderOf_eq_one, map_one]

theorem beta_ne_one : beta N α ≠ 1 := by
  intro h1
  apply h.ne_one
  exact conjNormal_injective h.centralizer_eq (by rw [map_one]; exact h1)

theorem orderOf_beta : orderOf (beta N α) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact h.beta_sq) h.beta_ne_one

theorem mem_of_mem_inner (hi : beta N α ∈ inner N) : α ∈ N := by
  obtain ⟨t, ht⟩ := hi
  have hc : MulAut.conjNormal (t : G) = (MulAut.conjNormal α : MulAut N) := by
    rw [MulAut.conjNormal_val]
    exact ht
  rw [← conjNormal_injective h.centralizer_eq hc]
  exact t.2

theorem le_fixed : J.subgroupOf N ≤ fixedSubgroup (beta N α) := fun _x hx =>
  mem_fixedSubgroup_beta.mpr (h.le_C (mem_subgroupOf.mp hx))

theorem isComponent_fixed [Finite G] :
    IsComponent ((J.subgroupOf N).subgroupOf (fixedSubgroup (beta N α))) := by
  have hle : J ≤ N ⊓ centralizer ({α} : Set G) := le_inf h.le_N h.le_C
  have h1 : IsComponent (J.subgroupOf (N ⊓ centralizer ({α} : Set G))) :=
    LieType.Chevalley.isComponent_subgroupOf_of_le hle inf_le_right h.component
  have h2 : Assembly.IsComponentOf J (N ⊓ centralizer ({α} : Set G)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle).mpr h1
  have h3 : Assembly.IsComponentOf (J.subgroupOf N) ((centralizer ({α} : Set G)).subgroupOf N) := by
    rw [← LocalAnalysis.ComponentInitial.isComponentOf_map_iff N.subtype_injective,
      subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr h.le_N, inf_comm]
    exact h2
  rw [← fixedSubgroup_beta] at h3
  exact (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.le_fixed).mp h3

theorem ne_top : J.subgroupOf N ≠ ⊤ := by
  intro htop
  apply h.ne_one
  have hα : α ∈ centralizer (N : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have hxJ : x ∈ J := by
      have : (⟨x, hx⟩ : N) ∈ J.subgroupOf N := htop ▸ mem_top _
      exact mem_subgroupOf.mp this
    exact mem_centralizer_singleton_iff.mp (h.le_C hxJ)
  rw [h.centralizer_eq, mem_bot] at hα
  exact hα

theorem properFixedComponent [Finite G] : ProperFixedComponent (beta N α) (J.subgroupOf N) :=
  ⟨fun y => by rw [← MulAut.mul_apply, h.beta_sq, MulAut.one_apply], h.le_fixed,
    LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent h.isComponent_fixed, h.ne_top⟩

theorem isL34Type [Finite G] :
    GrSLit.IsL34Type ((J.subgroupOf N) ⧸ Open.fusionZStar (J.subgroupOf N)) := by
  obtain ⟨-, ⟨eZ⟩⟩ := h.properFixedComponent.fusionZStar_equiv_of_quasisimple h.isComponent_fixed.1
  let e1 : ↥((J.subgroupOf N).subgroupOf (fixedSubgroup (beta N α))) ≃* ↥J :=
    (subgroupOfEquivOfLe h.le_fixed).trans (subgroupOfEquivOfLe h.le_N)
  exact LieType.CurtisTits.lieModel_of_mulEquiv (eZ.trans (quotCenterCongr e1)).symm h.lie

theorem nonabelian : ∃ a b : N, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := h.component.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ b
  refine ⟨⟨a.1.1, h.le_N (mem_subgroupOf.mp a.2)⟩, ⟨b.1.1, h.le_N (mem_subgroupOf.mp b.2)⟩,
    fun hc => hab ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  have hc' : (a.1.1 * b.1.1 : G) = b.1.1 * a.1.1 := congrArg Subtype.val hc
  exact Subtype.ext (Subtype.ext hc')

theorem card_quot : Nat.card (↥J ⧸ center ↥J) = 20160 :=
  CatLeaf.card_of_isL34Type h.lie

theorem dvd_card_J : 20160 ∣ Nat.card J := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center J), h.card_quot]
  exact dvd_mul_right _ _

theorem dvd_card_N : 20160 ∣ Nat.card N :=
  h.dvd_card_J.trans (Subgroup.card_dvd_of_le h.le_N)

theorem dvd_card_fixed :
    20160 ∣ Nat.card (fixedSubgroup (beta N α)) := by
  have hJ : Nat.card (J.subgroupOf N) = Nat.card J :=
    Nat.card_congr (subgroupOfEquivOfLe h.le_N).toEquiv
  have h1 : 20160 ∣ Nat.card (J.subgroupOf N) := by
    rw [hJ]
    exact h.dvd_card_J
  exact h1.trans (Subgroup.card_dvd_of_le h.le_fixed)

theorem dvd_card_fixed_congr {M : Type*} [Group M] (e : N ≃* M) :
    20160 ∣ Nat.card (fixedSubgroup (MulAut.congr e (beta N α))) := by
  rw [← Nat.card_congr (Sporadic.HeldB.fixedSubgroupCongr e (beta N α)).toEquiv]
  exact h.dvd_card_fixed

theorem seven_dvd_card_N : 7 ∣ Nat.card N :=
  (by norm_num : 7 ∣ 20160).trans h.dvd_card_N

end Hyp

end CFSG.ComponentClassification.GSThmB.Soc
