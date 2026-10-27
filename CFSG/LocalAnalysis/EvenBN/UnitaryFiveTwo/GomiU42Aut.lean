module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Selector
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {J D E : Subgroup X} {a : X}

theorem GomiU42Data.normal (h : GomiU42Data X J D E a) : D.Normal := by
  rw [← h.normalClosure_eq]
  exact normalClosure_normal

theorem GomiU42Data.le_D (h : GomiU42Data X J D E a) : J ≤ D := h.lt.le

theorem GomiU42Data.le_centralizer (h : GomiU42Data X J D E a) : J ≤ centralizer ({a} : Set X) := by
  rw [← h.sup_eq]
  exact le_sup_right

theorem GomiU42Data.commute_of_mem_J (h : GomiU42Data X J D E a) {x : X} (hx : x ∈ J) :
    a * x = x * a :=
  (mem_centralizer_singleton_iff.1 (h.le_centralizer hx)).symm

theorem GomiU42Data.conj_eq_of_mem_J (h : GomiU42Data X J D E a) {y : X} (hy : y ∈ J) :
    a * y * a⁻¹ = y := by
  calc a * y * a⁻¹ = (y * a) * a⁻¹ := by rw [h.commute_of_mem_J hy]
    _ = y := by group

theorem GomiU42Data.centralizer_le_normalizer (h : GomiU42Data X J D E a) :
    centralizer ({a} : Set X) ≤ normalizer (J : Set X) := by
  rw [← h.sup_eq]
  refine sup_le ?_ le_normalizer
  rw [zpowers_le, mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h.conj_eq_of_mem_J hy]
    exact hy
  · intro hy
    have hz : a⁻¹ * (a * y * a⁻¹) * a = a * y * a⁻¹ := by
      calc a⁻¹ * (a * y * a⁻¹) * a = a⁻¹ * ((a * y * a⁻¹) * a) := by group
        _ = a⁻¹ * (a * (a * y * a⁻¹)) := by rw [← h.commute_of_mem_J hy]
        _ = a * y * a⁻¹ := by group
    have hy' : y = a * y * a⁻¹ := by
      calc y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = a * y * a⁻¹ := hz
    rw [hy']
    exact hy

theorem GomiU42Data.conjNormal_injective (h : GomiU42Data X J D E a) :
    haveI := h.normal
    Function.Injective (MulAut.conjNormal : X →* MulAut D) := by
  haveI := h.normal
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxc : x ∈ centralizer (D : Set X) := by
    rw [mem_centralizer_iff]
    intro d hd
    have := congrArg (fun γ : MulAut D => (γ ⟨d, hd⟩ : X)) hx
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
    calc d * x = (x * d * x⁻¹) * x := by rw [this]
      _ = x * d := by group
  rw [h.centralizer_eq] at hxc
  exact mem_bot.1 hxc

theorem GomiU42Data.fixedRoot_conjNormal (h : GomiU42Data X J D E a) :
    haveI := h.normal
    orderOf (MulAut.conjNormal a : MulAut D) = 2 ∧
      J.subgroupOf D ≤ (MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D) ∧
      ((J.subgroupOf D).subgroupOf
        ((MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D))).Normal ∧
      (a ∈ D ↔ (MulAut.conjNormal a : MulAut D) ∈ inner D) := by
  haveI := h.normal
  have hinj := h.conjNormal_injective
  have hfix : ∀ x : D, x ∈ (MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus
      (MonoidHom.id D) ↔ (x : X) ∈ centralizer ({a} : Set X) := by
    intro x
    change MulAut.conjNormal a x = x ↔ _
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, MulAut.conjNormal_apply]
    constructor
    · intro hx
      calc (x : X) * a = (a * x * a⁻¹) * a := by rw [hx]
        _ = a * x := by group
    · intro hx
      calc a * (x : X) * a⁻¹ = ((x : X) * a) * a⁻¹ := by rw [hx]
        _ = x := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective _ hinj a, h.orderOf_a]
  · intro x hx
    exact (hfix x).2 (h.le_centralizer hx)
  · refine ⟨fun n hn g => ?_⟩
    have hnJ : ((n : D) : X) ∈ J := hn
    have hgC : (((g : D)) : X) ∈ centralizer ({a} : Set X) := (hfix g).1 g.2
    have hgN := h.centralizer_le_normalizer hgC
    change (((g : D) : X) * ((n : D) : X) * ((g : D) : X)⁻¹) ∈ J
    exact (mem_normalizer_iff.1 hgN _).1 hnJ
  · constructor
    · intro ha
      refine ⟨⟨a, ha⟩, ?_⟩
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    · rintro ⟨d, hd⟩
      have hda : (d : X) = a := by
        have hcomm : ((d : X)⁻¹ * a) ∈ centralizer (D : Set X) := by
          rw [mem_centralizer_iff]
          intro x hx
          have h0 := congrArg (fun γ : MulAut D => (γ ⟨x, hx⟩ : X)) hd
          have h1 : (((d * ⟨x, hx⟩ * d⁻¹ : D)) : X) = a * x * a⁻¹ := by
            simpa only [MulAut.conj_apply, MulAut.conjNormal_apply] using h0
          have this : (d : X) * x * (d : X)⁻¹ = a * x * a⁻¹ := h1
          calc x * ((d : X)⁻¹ * a) = (d : X)⁻¹ * ((d : X) * x * (d : X)⁻¹) * a := by group
            _ = (d : X)⁻¹ * (a * x * a⁻¹) * a := by rw [this]
            _ = (d : X)⁻¹ * a * x := by group
        rw [h.centralizer_eq] at hcomm
        have := mem_bot.1 hcomm
        calc (d : X) = (d : X) * ((d : X)⁻¹ * a) := by rw [this, mul_one]
          _ = a := by group
      rw [← hda]
      exact d.2

theorem GomiU42Data.inf_centralizer_eq (h : GomiU42Data X J D E a) (ha : a ∉ D) :
    D ⊓ centralizer ({a} : Set X) = J := by
  have hC := h.centralizer_le_normalizer
  have hJC := h.le_centralizer
  have hAC : zpowers a ≤ centralizer ({a} : Set X) := by
    rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl
  have hN : ((J.subgroupOf (centralizer ({a} : Set X)))).Normal :=
    normal_subgroupOf_of_le_normalizer hC
  have htop : (zpowers a).subgroupOf (centralizer ({a} : Set X)) ⊔
      J.subgroupOf (centralizer ({a} : Set X)) = ⊤ := by
    rw [← subgroupOf_sup hAC hJC, h.sup_eq, subgroupOf_self]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxD, hxC⟩ := mem_inf.1 hx
    let x' : centralizer ({a} : Set X) := ⟨x, hxC⟩
    have hx' : x' ∈ (zpowers a).subgroupOf (centralizer ({a} : Set X)) ⊔
        J.subgroupOf (centralizer ({a} : Set X)) := by
      rw [htop]
      exact mem_top _
    have hmul := mul_normal ((zpowers a).subgroupOf (centralizer ({a} : Set X)))
      (J.subgroupOf (centralizer ({a} : Set X)))
    have hx'' : x' ∈ (↑((zpowers a).subgroupOf (centralizer ({a} : Set X)) ⊔
        J.subgroupOf (centralizer ({a} : Set X))) : Set (centralizer ({a} : Set X))) := hx'
    rw [hmul] at hx''
    obtain ⟨g, hg, n, hn, hgn⟩ := hx''
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (mem_subgroupOf.1 hg)
    have hnJ : (n : X) ∈ J := mem_subgroupOf.1 hn
    have hxeq : x = (g : X) * (n : X) := by
      have := congrArg Subtype.val hgn
      exact this.symm
    have hgi : (g : X) = a ^ i := hi.symm
    have hnD : (n : X) ∈ D := h.le_D hnJ
    rcases Int.emod_two_eq_zero_or_one i with he | ho
    · have hai : a ^ i = 1 := by
        have he' : i % ((orderOf a : ℕ) : ℤ) = 0 := by
          rw [h.orderOf_a]; exact_mod_cast he
        rw [← zpow_mod_orderOf, he', zpow_zero]
      rw [hxeq, hgi, hai, one_mul]
      exact hnJ
    · exfalso
      have hai : a ^ i = a := by
        have ho' : i % ((orderOf a : ℕ) : ℤ) = 1 := by
          rw [h.orderOf_a]; exact_mod_cast ho
        rw [← zpow_mod_orderOf, ho', zpow_one]
      have : a = x * (n : X)⁻¹ := by
        rw [hxeq, hgi, hai]
        group
      exact ha (this ▸ mul_mem hxD (inv_mem hnD))
  · exact le_inf h.le_D (h.le_centralizer)

theorem GomiU42Data.eqLocus_eq (h : GomiU42Data X J D E a) (ha : a ∉ D) :
    haveI := h.normal
    (MulAut.conjNormal a : MulAut D).toMonoidHom.eqLocus (MonoidHom.id D) = J.subgroupOf D := by
  haveI := h.normal
  have hinf := h.inf_centralizer_eq ha
  ext x
  change MulAut.conjNormal a x = x ↔ _
  rw [mem_subgroupOf, ← Subtype.coe_inj, MulAut.conjNormal_apply]
  constructor
  · intro hx
    have hxc : (x : X) ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc (x : X) * a = (a * x * a⁻¹) * a := by rw [hx]
        _ = a * x := by group
    rw [← hinf]
    exact mem_inf.2 ⟨x.2, hxc⟩
  · intro hx
    have hxc := (mem_inf.1 (hinf ▸ hx : (x : X) ∈ D ⊓ centralizer ({a} : Set X))).2
    rw [mem_centralizer_singleton_iff] at hxc
    calc a * (x : X) * a⁻¹ = ((x : X) * a) * a⁻¹ := by rw [hxc]
      _ = x := by group

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
