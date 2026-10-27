module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SimpleGroupReductions
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.GH74.GLS.TwoThin

open Subgroup
open scoped commutatorElement

section Product

variable {G : Type*} [Group G]

omit [Group G] in
theorem card_subgroupOf_eq {G : Type*} [Group G] {A T : Subgroup G} (h : A ≤ T) :
    Nat.card ↥(A.subgroupOf T) = Nat.card ↥A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_sup_mul_card_inf [Finite G] {A B : Subgroup G} (hB : B ≤ normalizer (A : Set G)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  set T := A ⊔ B with hT
  have hAT : A ≤ T := le_sup_left
  have hBT : B ≤ T := le_sup_right
  have hnorm : (A.subgroupOf T).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hAT]
    exact sup_le le_normalizer hB
  have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (A.subgroupOf T)
    (B.subgroupOf T)
  have hsup : A.subgroupOf T ⊔ B.subgroupOf T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAT hBT]
    exact Subgroup.subgroupOf_self T
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.card_mul_index (B.subgroupOf T)
  have h3 := Subgroup.relIndex_mul_card (B.subgroupOf T) (A.subgroupOf T)
  have h4 : (B.subgroupOf T) ⊓ (A.subgroupOf T) = (B ⊓ A).subgroupOf T := by
    ext z
    simp [Subgroup.mem_subgroupOf]
  rw [h4, card_subgroupOf_eq (inf_le_left.trans hBT), card_subgroupOf_eq hAT] at h3
  rw [card_subgroupOf_eq hBT] at h2
  have h5 : Nat.card ↥(B ⊓ A) = Nat.card ↥(A ⊓ B) := by rw [inf_comm]
  rw [h5] at h3
  have h6 : Nat.card ↥T = Nat.card ↥B * (B.subgroupOf T).index := by
    rw [← h2]
  rw [h6, h1]
  calc Nat.card ↥B * (B.subgroupOf T).relIndex (A.subgroupOf T) * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * ((B.subgroupOf T).relIndex (A.subgroupOf T) * Nat.card ↥(A ⊓ B)) := by
        rw [mul_assoc]
    _ = Nat.card ↥B * Nat.card ↥A := by rw [h3]
    _ = Nat.card ↥A * Nat.card ↥B := mul_comm _ _


theorem factorization_lt_of_sup [Finite G] {A B C Q : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) (hABC : A ⊔ B ≤ C) (hBp : IsPGroup 2 ↥B)
    (hQp : IsPGroup 2 ↥Q) (hQB : Nat.card ↥Q ≤ 2 * Nat.card ↥B) {b : ℕ}
    (hA : 2 ^ (b + 2) ∣ Nat.card ↥A) (hAB : Nat.card ↥(A ⊓ B) ≤ 2 ^ b) :
    (Nat.card ↥Q).factorization 2 < (Nat.card ↥C).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := hBp.exists_card_eq
  obtain ⟨γ, hγ⟩ := hQp.exists_card_eq
  have hABp : IsPGroup 2 ↥(A ⊓ B : Subgroup G) := hBp.to_inf_right
  obtain ⟨d, hd⟩ := hABp.exists_card_eq
  have hdb : d ≤ b := by
    rw [hd] at hAB
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hAB
  have hγβ : γ ≤ β + 1 := by
    rw [hγ, hβ] at hQB
    have : 2 ^ γ ≤ 2 ^ (β + 1) := by
      rw [pow_succ]
      linarith
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hprod := card_sup_mul_card_inf hB
  rw [hd, hβ] at hprod
  have h1 : 2 ^ (b + 2 + β) ∣ Nat.card ↥(A ⊔ B) * 2 ^ d := by
    rw [hprod, pow_add]
    exact Nat.mul_dvd_mul hA dvd_rfl
  have h2 : 2 ^ (β + 2) ∣ Nat.card ↥(A ⊔ B) := by
    have h22 : 2 ^ (b + 2 + β) = 2 ^ (β + 2 + (b - d)) * 2 ^ d := by
      rw [← pow_add]
      congr 1
      omega
    rw [h22] at h1
    have h3 := Nat.dvd_of_mul_dvd_mul_right (by positivity : 0 < 2 ^ d) h1
    exact (pow_dvd_pow 2 (by omega)).trans h3
  have h4 : 2 ^ (β + 2) ∣ Nat.card ↥C := h2.trans (Subgroup.card_dvd_of_le hABC)
  have h5 : β + 2 ≤ (Nat.card ↥C).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h4
  have h6 : (Nat.card ↥Q).factorization 2 = γ := by
    rw [hγ, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  omega

theorem four_dvd_card_of_simple_nonabelian {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) : 4 ∣ Nat.card S := by
  have heven : Even (Nat.card S) := by
    by_contra h
    have hodd : Odd (Nat.card S) := Nat.not_even_iff_odd.mp h
    have hsolv : Group.IsSolvable S := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨sylow⟩ : Nonempty (Sylow 2 S) := inferInstance
  have hnc := CFSG.DisconnectedInvolutionGraph.Helpers.simple_even_sylow_two_not_cyclic
    hnonab heven sylow
  have hcard : Nat.card ↥(sylow : Subgroup S) = 2 ^ (Nat.card S).factorization 2 :=
    Sylow.card_eq_multiplicity sylow
  by_contra h4
  have hlt : (Nat.card S).factorization 2 < 2 := by
    by_contra hge
    exact h4 (by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mpr
        (not_lt.mp hge)
      simpa using this)
  rcases Nat.lt_succ_iff.mp hlt |>.eq_or_lt with h | h
  · rw [h] at hcard
    have hp : Nat.card ↥(sylow : Subgroup S) = 2 := by simpa using hcard
    exact hnc (isCyclic_of_prime_card hp)
  · have h0 : (Nat.card S).factorization 2 = 0 := by omega
    rw [h0] at hcard
    have : Nat.card ↥(sylow : Subgroup S) = 1 := by simpa using hcard
    have : Subsingleton ↥(sylow : Subgroup S) := (Nat.card_eq_one_iff_unique.mp this).1
    exact hnc inferInstance

theorem exists_pow_dvd_card_of_isQuasisimple {L : Type*} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hZ : IsPGroup 2 ↥(center L)) :
    ∃ b : ℕ, Nat.card ↥(center L) = 2 ^ b ∧ 2 ^ (b + 2) ∣ Nat.card L := by
  obtain ⟨b, hb⟩ := hZ.exists_card_eq
  refine ⟨b, hb, ?_⟩
  have : IsSimpleGroup (L ⧸ center L) := hq.2.1
  have h4 : 4 ∣ Nat.card (L ⧸ center L) := four_dvd_card_of_simple_nonabelian hq.2.2
  have h1 : Nat.card L = Nat.card (L ⧸ center L) * Nat.card ↥(center L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h4' : 2 ^ 2 ∣ Nat.card (L ⧸ center L) := by simpa using h4
  rw [h1, hb, pow_add, mul_comm (Nat.card (L ⧸ center L))]
  exact Nat.mul_dvd_mul_left _ h4'

end Product

section Central

variable {H : Type*} [Group H]

theorem eq_of_normalizes_of_central {L : Subgroup H} (hL : ⁅L, L⁆ = L) {w : H}
    (hz : ∀ l ∈ L, ∃ z ∈ L, (∀ m ∈ L, z * m = m * z) ∧ w * l * w⁻¹ = l * z) :
    ∀ l ∈ L, w * l * w⁻¹ = l := by
  have hle : ⁅L, L⁆ ≤ L ⊓ centralizer ({w} : Set H) := by
    rw [Subgroup.commutator_le]
    intro l₁ hl₁ l₂ hl₂
    obtain ⟨z₁, hz₁L, hz₁c, hz₁⟩ := hz l₁ hl₁
    obtain ⟨z₂, hz₂L, hz₂c, hz₂⟩ := hz l₂ hl₂
    have hcL : ⁅l₁, l₂⁆ ∈ L := hL ▸ Subgroup.commutator_mem_commutator hl₁ hl₂
    refine Subgroup.mem_inf.mpr ⟨hcL, ?_⟩
    have hconj : w * ⁅l₁, l₂⁆ * w⁻¹ = ⁅w * l₁ * w⁻¹, w * l₂ * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have hk : ⁅l₁ * z₁, l₂ * z₂⁆ = ⁅l₁, l₂⁆ := by
      rw [CFSG.LocalAnalysis.ComponentInitial.commutatorElement_mul_mul_eq_mul
        (hz₁c l₁ hl₁).symm (hz₂c l₁ hl₁).symm (hz₁c l₂ hl₂).symm (hz₂c l₂ hl₂).symm]
      have : ⁅z₁, z₂⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hz₁c z₂ hz₂L)
      rw [this, mul_one]
    rw [hz₁, hz₂, hk] at hconj
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  rw [hL] at hle
  intro l hl
  have h := (Subgroup.mem_centralizer_iff.mp (hle hl).2) w (Set.mem_singleton w)
  exact mul_inv_eq_iff_eq_mul.mpr h

end Central

end CFSG.GH74.GLS.TwoThin
