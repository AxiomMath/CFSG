module

public import CFSG.GH74.GLS.Stage2.Local.Bar
public import CFSG.GH74.GLS.Stage2.Local.Basic
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12
open scoped commutatorElement

section Aux

variable {Y : Type*} [Group Y]

theorem commutator_self_eq_of_isPerfect (H : Subgroup Y) (hH : Group.IsPerfect ↥H) : ⁅H, H⁆ = H := by
  rw [← Subgroup.map_subtype_commutator, hH.commutator_eq_top, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem mul_mul_inv_mem_of_conjugate_eq {A B : Subgroup Y} {g : Y} (h : conjugate A g = B) {x : Y}
    (hx : x ∈ B) : g * x * g⁻¹ ∈ A := by
  rw [← h] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have : g * (MulAut.conj g⁻¹).toMonoidHom y * g⁻¹ = y := by
    simp [mul_assoc]
  rw [this]
  exact hy

theorem le_commutator_zpowers_of_swap {L Li Lj : Subgroup Y} {t : Y} (hLi : Li ≤ L)
    (hperf : ⁅Li, Li⁆ = Li) (hcomm : ∀ a ∈ Li, ∀ b ∈ Lj, a * b = b * a)
    (hconj : ∀ a ∈ Li, t * a * t⁻¹ ∈ Lj) : Li ≤ ⁅L, zpowers t⁆ := by
  rw [← hperf]
  refine Subgroup.commutator_le.mpr fun g hg a ha => ?_
  have hw : ⁅a, t⁆ ∈ ⁅L, zpowers t⁆ :=
    Subgroup.commutator_mem_commutator (hLi ha) (Subgroup.mem_zpowers t)
  have hgn : g ∈ normalizer ((⁅L, zpowers t⁆ : Subgroup Y) : Set Y) :=
    Subgroup.normalizer_commutator_ge_left L (zpowers t) (hLi hg)
  have h1 : g * ⁅a, t⁆ * g⁻¹ ∈ ⁅L, zpowers t⁆ := (Subgroup.mem_normalizer_iff.mp hgn _).mp hw
  have h2 : g * ⁅a, t⁆ * g⁻¹ * ⁅a, t⁆⁻¹ ∈ ⁅L, zpowers t⁆ :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hw)
  have hb : t * a⁻¹ * t⁻¹ ∈ Lj := hconj a⁻¹ (Subgroup.inv_mem _ ha)
  have hc : Commute g (t * a⁻¹ * t⁻¹) := hcomm g hg _ hb
  have e : ⁅a, t⁆ = a * (t * a⁻¹ * t⁻¹) := by simp [commutatorElement_def, mul_assoc]
  have key : g * ⁅a, t⁆ * g⁻¹ * ⁅a, t⁆⁻¹ = ⁅g, a⁆ := by
    rw [e]
    calc g * (a * (t * a⁻¹ * t⁻¹)) * g⁻¹ * (a * (t * a⁻¹ * t⁻¹))⁻¹
        = g * a * ((t * a⁻¹ * t⁻¹) * g⁻¹) * (t * a⁻¹ * t⁻¹)⁻¹ * a⁻¹ := by group
      _ = g * a * (g⁻¹ * (t * a⁻¹ * t⁻¹)) * (t * a⁻¹ * t⁻¹)⁻¹ * a⁻¹ := by rw [← hc.inv_left.eq]
      _ = ⁅g, a⁆ := by simp only [commutatorElement_def]; group
  rw [key] at h2
  exact h2

end Aux

section P22x

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

omit [Finite G] in
theorem commutator_LBar_le_barOf (z : G) {t : G} (ht : t ∈ Cen z) :
    ⁅LBar z, zpowers (toBar z ⟨t, ht⟩)⁆ ≤ barOf z ⁅LC z, zpowers t⁆ := by
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  obtain ⟨⟨l, hlC⟩, hl, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hy
  have hl' : l ∈ LC z := hl
  refine ⟨⁅(⟨l, hlC⟩ : ↥(Cen z)), (⟨t, ht⟩ : ↥(Cen z)) ^ n⁆, ?_, ?_⟩
  · refine Subgroup.mem_subgroupOf.mpr ?_
    have : ((⁅(⟨l, hlC⟩ : ↥(Cen z)), (⟨t, ht⟩ : ↥(Cen z)) ^ n⁆ : ↥(Cen z)) : G) = ⁅l, t ^ n⁆ := by
      simp [commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator hl' ⟨n, rfl⟩
  · rw [map_commutatorElement, map_zpow]

theorem Stage2Ctx.prop22x (h : Stage2Ctx G z k S) : Prop22x z S := by
  intro q L₁ L₂ hP t _ _ hsw
  obtain ⟨ht, h1, h2⟩ := hsw
  have hcomp : ∀ K ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))), IsComponent K := by
    intro K hK
    have : K ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by rw [hP.comps]; exact hK
    exact this
  have hperf₁ : ⁅L₁, L₁⁆ = L₁ :=
    commutator_self_eq_of_isPerfect L₁ (hcomp L₁ (Set.mem_insert _ _)).1.1
  have hperf₂ : ⁅L₂, L₂⁆ = L₂ :=
    commutator_self_eq_of_isPerfect L₂ (hcomp L₂ (Set.mem_insert_of_mem _ rfl)).1.1
  obtain ⟨hsup, hcomm, -⟩ := hP.prod
  have hL₁ : L₁ ≤ LBar z := by rw [← hsup]; exact le_sup_left
  have hL₂ : L₂ ≤ LBar z := by rw [← hsup]; exact le_sup_right
  have c12 : ∀ a ∈ L₁, toBar z ⟨t, ht⟩ * a * (toBar z ⟨t, ht⟩)⁻¹ ∈ L₂ := fun a ha =>
    mul_mul_inv_mem_of_conjugate_eq h2 ha
  have c21 : ∀ a ∈ L₂, toBar z ⟨t, ht⟩ * a * (toBar z ⟨t, ht⟩)⁻¹ ∈ L₁ := fun a ha =>
    mul_mul_inv_mem_of_conjugate_eq h1 ha
  have hle : LBar z ≤ ⁅LBar z, zpowers (toBar z ⟨t, ht⟩)⁆ :=
    calc LBar z = L₁ ⊔ L₂ := hsup.symm
      _ ≤ _ := sup_le (le_commutator_zpowers_of_swap hL₁ hperf₁ hcomm c12)
          (le_commutator_zpowers_of_swap hL₂ hperf₂ (fun a ha b hb => (hcomm b hb a ha).symm) c21)
  have hzF : toBar z ⟨z, mem_Cen_self z⟩ ∈ generalizedFitting (CentralizerBar z) :=
    centralizer_generalizedFitting_le (CentralizerBar z)
      (Subgroup.mem_centralizer_iff.mpr fun y _ =>
        Subgroup.mem_center_iff.mp (toBar_z_mem_center z) y)
  rw [hP.fitting] at hzF
  obtain ⟨⟨k', hk'C⟩, hk', hkz⟩ := commutator_LBar_le_barOf z ht (hle hzF)
  exact z_mem_of_toBar_eq h.orderOf_z (Subgroup.mem_subgroupOf.mp hk') hk'C hkz

end P22x

end CFSG.GH74.GLS.Stage2.Local
