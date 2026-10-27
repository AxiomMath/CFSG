module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
import CFSG.ClassicalInvolution.Asc77.AscP1SevenBurnside

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem m6z_mem_of_commute [Finite G] {C S : Subgroup G} (hS : IsSylow2Of S C) {z : G}
    (hzC : z ∈ C) (hz2 : z * z = 1) (hcomm : ∀ s ∈ S, s * z = z * s) : z ∈ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hS.exists_sylow
  have hord : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hz2)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)
  have hN : Subgroup.zpowers z ≤ Subgroup.normalizer (S : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have e : z * h * z⁻¹ = h := by rw [← hcomm h hh]; group
      rwa [e]
    · intro hh
      have e := hcomm _ hh
      have e2 : h = z * h * z⁻¹ := by
        calc h = z⁻¹ * ((z * h * z⁻¹) * z) := by group
          _ = z⁻¹ * (z * (z * h * z⁻¹)) := by rw [e]
          _ = z * h * z⁻¹ := by group
      rwa [e2]
  have hT : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers z) := hS.2.1.to_sup_of_normal_left' hzp hN
  have hTC : S ⊔ Subgroup.zpowers z ≤ C := sup_le hS.1 (Subgroup.zpowers_le.mpr hzC)
  have hT' : IsPGroup 2 ↥((S ⊔ Subgroup.zpowers z).subgroupOf C) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTC).symm
  have hle : (P : Subgroup ↥C) ≤ (S ⊔ Subgroup.zpowers z).subgroupOf C := fun x hx => by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_sup_left ?_
    rw [← hP]
    exact ⟨x, hx, rfl⟩
  have heq := P.is_maximal' hT' hle
  have hz : (⟨z, hzC⟩ : ↥C) ∈ (S ⊔ Subgroup.zpowers z).subgroupOf C :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  rw [heq] at hz
  rw [← hP]
  exact ⟨_, hz, rfl⟩

theorem m6z_exists_fixed_mem_sylow [Finite G] {C S : Subgroup G} (hS : IsSylow2Of S C)
    {Z : Set G} (hZC : ∀ z ∈ Z, z ∈ C) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hZS : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z) (hodd : Odd Z.ncard) :
    ∃ z ∈ Z, z ∈ S ∧ ∀ s ∈ S, s * z = z * s := by
  have hodd' : Odd (Nat.card Z) := by
    rw [Nat.card_coe_set_eq]
    exact hodd
  obtain ⟨z, hzZ, hfix⟩ :=
    CFSG.ClassicalInvolution.Asc77.Thompson.exists_fixed_mem_of_odd hS.2.1 hZS hodd'
  have hcomm : ∀ s ∈ S, s * z = z * s := fun s hs => by
    calc s * z = (s * z * s⁻¹) * s := by group
      _ = z * s := by rw [hfix s hs]
  exact ⟨z, hzZ, m6z_mem_of_commute hS (hZC z hzZ) (hZ2 z hzZ) hcomm, hcomm⟩

theorem m6z_notation_of_odd [Finite G] {t : G} {L S : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G)) (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (hN : ∀ s ∈ S, s ∈ normalizer (L : Set G))
    (hodd : Odd {z : G | z ∈ L ∧ IsI4PlusIn L z}.ncard) : ∃ z : G, Asc82Notation t L S z := by
  have hnorm : ∀ s ∈ S, CFSG.conjugate L s = L := fun s hs => by
    ext x
    rw [mem_conjugate_iff]
    exact ((Subgroup.mem_normalizer_iff.mp (hN s hs)) x).symm
  obtain ⟨z, hzZ, hzS, hcomm⟩ := m6z_exists_fixed_mem_sylow hS
    (Z := {z : G | z ∈ L ∧ IsI4PlusIn L z}) (fun z hz => hLt hz.1)
    (fun z hz => by
      rw [← pow_two]
      exact hz.2.1 ▸ pow_orderOf_eq_one z)
    (fun s hs z hz => by
      have h := hz.2.conjugate s⁻¹
      rw [hnorm s⁻¹ (S.inv_mem hs), inv_inv] at h
      exact ⟨h.mem, h⟩)
    hodd
  exact ⟨z, ⟨hS, hzS, hcomm, hzZ.2⟩⟩

end CFSG.OddStandard.SmallF3.Omega
