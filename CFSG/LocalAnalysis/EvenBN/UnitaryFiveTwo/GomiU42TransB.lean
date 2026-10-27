module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {G : Type} [Group G] {Bs : Subgroup G} {t : G} {E₂ J₀ : Subgroup G}

theorem elementary_subgroupOf (hE : E₂ ≤ Bs) (h : CFSG.IsElementaryAbelian 2 ↥E₂) :
    CFSG.IsElementaryAbelian 2 ↥(E₂.subgroupOf Bs) := by
  refine CFSG.IsElementaryAbelian.two_of_forall_mul_self ?_ ?_
  · intro a ha b hb
    have hc := mul_comm' (⟨(a : G), Subgroup.mem_subgroupOf.mp ha⟩ : ↥E₂)
      ⟨(b : G), Subgroup.mem_subgroupOf.mp hb⟩
    have hc' : (a : G) * (b : G) = (b : G) * (a : G) := congrArg Subtype.val hc
    exact Subtype.ext hc'
  · intro a ha
    apply Subtype.ext
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E₂) (a : G)
      (Subgroup.mem_subgroupOf.mp ha)
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
    exact h2

theorem card_subgroupOf_of_le (hE : E₂ ≤ Bs) :
    Nat.card ↥(E₂.subgroupOf Bs) = Nat.card ↥E₂ := by
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv

theorem mem_normalizer_subgroupOf (ht : t ∈ Bs) (h : t ∈ normalizer (E₂ : Set G)) :
    (⟨t, ht⟩ : ↥Bs) ∈ normalizer ((E₂.subgroupOf Bs : Subgroup ↥Bs) : Set ↥Bs) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact Subgroup.mem_normalizer_iff.mp h (x : G)

theorem isPGroup_sup_subgroupOf (ht : t ∈ Bs) (hE : E₂ ≤ Bs)
    (h : IsPGroup 2 ↥(E₂ ⊔ zpowers t)) :
    IsPGroup 2 ↥(E₂.subgroupOf Bs ⊔ zpowers (⟨t, ht⟩ : ↥Bs)) := by
  have hK : E₂ ⊔ zpowers t ≤ Bs := sup_le hE (Subgroup.zpowers_le.mpr ht)
  have hL : E₂.subgroupOf Bs ⊔ zpowers (⟨t, ht⟩ : ↥Bs) ≤ (E₂ ⊔ zpowers t).subgroupOf Bs := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · intro x hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx))
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  exact IsPGroup.to_le (h.of_equiv (Subgroup.subgroupOfEquivOfLe hK).symm) hL

theorem card_inf_subgroupOf (ht : t ∈ Bs) (hE : E₂ ≤ Bs)
    (h : Nat.card ↥(E₂ ⊓ centralizer ({t} : Set G)) = 2 ^ 4) :
    Nat.card ↥(E₂.subgroupOf Bs ⊓ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs)) = 2 ^ 4 := by
  have hle : E₂ ⊓ centralizer ({t} : Set G) ≤ Bs := inf_le_left.trans hE
  have key : E₂.subgroupOf Bs ⊓ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs)
      = (E₂ ⊓ centralizer ({t} : Set G)).subgroupOf Bs := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [key, card_subgroupOf_of_le hle, h]

theorem inf_le_subgroupOf (ht : t ∈ Bs)
    (h : E₂ ⊓ centralizer ({t} : Set G) ≤ J₀) :
    E₂.subgroupOf Bs ⊓ centralizer ({(⟨t, ht⟩ : ↥Bs)} : Set ↥Bs) ≤ J₀.subgroupOf Bs := by
  intro x hx
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
  have h2' : (x : G) * t = t * (x : G) := by
    have hc := Subgroup.mem_centralizer_singleton_iff.mp h2
    exact congrArg Subtype.val hc
  have h3 : (x : G) ∈ E₂ ⊓ centralizer ({t} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_centralizer_singleton_iff.mpr h2'⟩
  exact Subgroup.mem_subgroupOf.mpr (h h3)

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
