module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Orbit

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.EvenSporadicStandard

theorem ncard_conj_orbit {Γ : Type} [Group Γ] (A : Subgroup Γ) (x : Γ) :
    Set.ncard {y : Γ | ∃ a ∈ A, y = a * x * a⁻¹} = (centralizer ({x} : Set Γ)).relIndex A := by
  let _ : MulAction A Γ := MulAction.compHom Γ ((MulAut.conj : Γ →* MulAut Γ).comp A.subtype)
  have h := MulAction.index_stabilizer A x
  have hstab : MulAction.stabilizer A x = (centralizer ({x} : Set Γ)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, mem_centralizer_singleton_iff]
    show (a : Γ) * x * (a : Γ)⁻¹ = x ↔ (a : Γ) * x = x * a
    rw [mul_inv_eq_iff_eq_mul]
  have horb : MulAction.orbit A x = {y : Γ | ∃ a ∈ A, y = a * x * a⁻¹} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  rw [← horb, ← h, hstab]
  rfl

theorem centralizer_omega_normal {Γ : Type} [Group Γ] (e : Γ) :
    (centralizer (omega e)).Normal := by
  refine ⟨fun x hx c => ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ omega e := conj_mem_omega hy c⁻¹
  have h := mem_centralizer_iff.1 hx _ hy'
  calc y * (c * x * c⁻¹) = c * ((c⁻¹ * y * c⁻¹⁻¹) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ := by rw [h]
    _ = c * x * c⁻¹ * y := by group

namespace Setting65

variable {Γ : Type} [Group Γ] {E H₁ : Subgroup Γ} {e : Γ} (hS : Setting65 Γ E H₁ e)
include hS

theorem eq_or_eq_of_normal_le {A : Subgroup Γ} (hA : A ≤ H₁) (hAn : (A.subgroupOf H₁).Normal)
    (hEA : E ⊓ H₁ ≤ A) : A = E ⊓ H₁ ∨ A = H₁ := by
  have := hS.normal₁
  have := hS.simple
  let π : ↥H₁ →* H₁ ⧸ E.subgroupOf H₁ := QuotientGroup.mk' (E.subgroupOf H₁)
  have hT : ((A.subgroupOf H₁).map π).Normal := hAn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.subgroupOf H₁).map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    refine le_antisymm (fun x hx => ⟨?_, hA hx⟩) hEA
    have := h (show (⟨x, hA hx⟩ : ↥H₁) ∈ A.subgroupOf H₁ from hx)
    exact mem_subgroupOf.1 this
  · right
    refine le_antisymm hA (fun y hy => ?_)
    have hmem : π ⟨y, hy⟩ ∈ (A.subgroupOf H₁).map π := h ▸ mem_top _
    obtain ⟨a, ha, hay⟩ := hmem
    have hker : a⁻¹ * ⟨y, hy⟩ ∈ E.subgroupOf H₁ := by
      rw [← QuotientGroup.ker_mk' (E.subgroupOf H₁), MonoidHom.mem_ker, map_mul, map_inv]
      change (π a)⁻¹ * π ⟨y, hy⟩ = 1
      rw [hay, inv_mul_cancel]
    have hker' : (a : Γ)⁻¹ * y ∈ E ⊓ H₁ :=
      ⟨mem_subgroupOf.1 hker, H₁.mul_mem (H₁.inv_mem a.2) hy⟩
    have : (a : Γ) * ((a : Γ)⁻¹ * y) ∈ A := A.mul_mem (mem_subgroupOf.1 ha) (hEA hker')
    simpa using this

theorem E_le_centralizer_omega : E ≤ centralizer (omega e) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  exact (hS.comm_of_mem_E hx (hS.omega_subset_E hy)).symm

section Finite

variable [Finite Γ]

theorem eq_or_ge_relIndex {S : Subgroup Γ} (hS₁ : S ≤ H₁) (hES : E ⊓ H₁ ≤ S) :
    S = H₁ ∨ 23 ≤ S.relIndex H₁ := by
  have := hS.normal₁
  have := hS.simple
  let π : ↥H₁ →* H₁ ⧸ E.subgroupOf H₁ := QuotientGroup.mk' (E.subgroupOf H₁)
  have hker : π.ker ≤ S.subgroupOf H₁ := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact mem_subgroupOf.2 (hES ⟨mem_subgroupOf.1 hx, x.2⟩)
  have hcomap : ((S.subgroupOf H₁).map π).comap π = S.subgroupOf H₁ :=
    Subgroup.comap_map_eq_self hker
  by_cases hT : (S.subgroupOf H₁).map π = ⊤
  · left
    have : S.subgroupOf H₁ = ⊤ := by rw [← hcomap, hT, comap_top]
    exact le_antisymm hS₁ (Subgroup.subgroupOf_eq_top.1 this)
  · right
    have hdvd := card_dvd_factorial_index hT
    rw [hS.card₁] at hdvd
    have h23 : 23 ∣ ((S.subgroupOf H₁).map π).index.factorial :=
      (by norm_num : 23 ∣ 10200960).trans hdvd
    have h23' : 23 ≤ ((S.subgroupOf H₁).map π).index :=
      (Nat.Prime.dvd_factorial (by decide)).1 h23
    rw [Subgroup.relIndex, ← hcomap,
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact h23'

theorem centralizer_omega : centralizer (omega e) = E := by
  have hNn := centralizer_omega_normal e
  have hEN := hS.E_le_centralizer_omega
  have hnorm : ((centralizer (omega e) ⊓ H₁).subgroupOf H₁).Normal := by
    rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf
  rcases hS.eq_or_eq_of_normal_le inf_le_right hnorm (inf_le_inf_right _ hEN) with hA | hA
  · refine le_antisymm (fun x hx => ?_) hEN
    have hxe : x ∈ centralizer ({e} : Set Γ) :=
      centralizer_le (Set.singleton_subset_iff.2 (e_mem_omega e)) hx
    rw [hS.centralizer_e] at hxe
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer hS.zpowers_le_centralizer hxe
    have hbE : b ∈ E := zpowers_le.2 hS.mem hb
    have haN : a ∈ centralizer (omega e) := by
      have hb' : b ∈ centralizer (omega e) := hEN hbE
      have : a = (a * b) * b⁻¹ := by group
      rw [this]
      exact mul_mem hx (inv_mem hb')
    have : a ∈ centralizer (omega e) ⊓ H₁ := ⟨haN, ha⟩
    rw [hA] at this
    exact mul_mem this.1 hbE
  · exfalso
    obtain ⟨g, hgH, hg23, hg1⟩ := hS.exists_g
    have hgN : g ∈ centralizer (omega e) := by
      have : g ∈ centralizer (omega e) ⊓ H₁ := by
        rw [hA]
        exact hgH
      exact this.1
    have hsub : omega e ⊆ ((E ⊓ centralizer ({g} : Set Γ) : Subgroup Γ) : Set Γ) := by
      intro y hy
      refine ⟨hS.omega_subset_E hy, mem_centralizer_singleton_iff.2 ?_⟩
      exact mem_centralizer_iff.1 hgN y hy
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : Nat.card ↥(E ⊓ centralizer ({g} : Set Γ)) =
        ((E ⊓ centralizer ({g} : Set Γ) : Subgroup Γ) : Set Γ).ncard :=
      Nat.card_coe_set_eq _
    rw [hS.ncard_omega, ← h2, hS.card_E_inf_centralizer_g hg23 hg1] at h1
    omega

end Finite

end Setting65

end CFSG.EvenSporadicStandard.Induction.Balance
