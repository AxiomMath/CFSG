module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AGen
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL41Defs

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped commutatorElement

section Q15A

variable {G : Type} [Group G] [Finite G]

theorem q15_commutator_le {Q : Subgroup G} {ρ : G} (hρ : ρ ∈ normalizer (Q : Set G)) :
    ⁅Q, zpowers ρ⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq r hr
  have hrmem : r ∈ normalizer (Q : Set G) := (Subgroup.zpowers_le.mpr hρ) hr
  have hconj : r * q⁻¹ * r⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hrmem (q⁻¹)).mp (Q.inv_mem hq)
  have heq : q * r * q⁻¹ * r⁻¹ = q * (r * q⁻¹ * r⁻¹) := by group
  rw [commutatorElement_def q r, heq]
  exact Q.mul_mem hq hconj

theorem q15_conj_commutator_left {A B : Subgroup G} {a x : G} (ha : a ∈ A)
    (hx : x ∈ ⁅A, B⁆) : a * x * a⁻¹ ∈ ⁅A, B⁆ := by
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hy
    have h1 : ⁅a * g₁, g₂⁆ ∈ ⁅A, B⁆ :=
      Subgroup.commutator_mem_commutator (A.mul_mem ha hg₁) hg₂
    have h2 : ⁅a, g₂⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hg₂
    have heq : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁, g₂⁆ * ⁅a, g₂⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (⁅A, B⁆).mul_mem h1 ((⁅A, B⁆).inv_mem h2)
  | one => simpa using one_mem (⁅A, B⁆)
  | mul y z _ _ ihy ihz =>
    have heq : a * (y * z) * a⁻¹ = (a * y * a⁻¹) * (a * z * a⁻¹) := by group
    rw [heq]
    exact (⁅A, B⁆).mul_mem ihy ihz
  | inv y _ ihy =>
    have heq : a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ := by group
    rw [heq]
    exact (⁅A, B⁆).inv_mem ihy

theorem q15_mem_normalizer_zpowers {ρ g : G} (h : g * ρ * g⁻¹ = ρ⁻¹ ∨ g * ρ * g⁻¹ = ρ) :
    g ∈ normalizer ((zpowers ρ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conj_mem ?_
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hmem : g * ρ * g⁻¹ ∈ zpowers ρ := by
    rcases h with h | h
    · rw [h]; exact (zpowers ρ).inv_mem (Subgroup.mem_zpowers ρ)
    · rw [h]; exact Subgroup.mem_zpowers ρ
  rw [(conj_zpow (a := g) (b := ρ) (i := k)).symm]
  exact (zpowers ρ).zpow_mem hmem k

theorem q15_mem_normalizer_commutator {Q : Subgroup G} {ρ g : G}
    (hQ : g ∈ normalizer (Q : Set G)) (hρ : g ∈ normalizer ((zpowers ρ : Subgroup G) : Set G)) :
    g ∈ normalizer ((⁅Q, zpowers ρ⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hQ hρ ⊢
  rw [Subgroup.map_commutator Q (zpowers ρ) (↑(MulAut.conj g) : G →* G), hQ, hρ]

theorem q15_comm_le_of_sectionIso {C N : Subgroup G} {K : Type} [CommGroup K]
    (e : Sec4SectionIso C N K) : ⁅C, C⁆ ≤ N := by
  obtain ⟨φ, -, hker⟩ := e
  rw [Subgroup.commutator_le]
  intro x hx y hy
  let u : ↥C := ⟨x, hx⟩
  let v : ↥C := ⟨y, hy⟩
  have h1 : φ ⁅u, v⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (φ u) (φ v))
  have h2 : ⁅u, v⁆ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
  rw [hker] at h2
  exact Subgroup.mem_subgroupOf.mp h2

end Q15A

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
