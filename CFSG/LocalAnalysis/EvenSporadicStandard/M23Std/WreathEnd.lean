module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem involution_conj_of_wreath {S1 S2 : Subgroup G} {z x : G} (hdisj : Disjoint S1 S2)
    (hcomm : ∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) (hz2 : z * z = 1)
    (hz1 : ∀ a ∈ S1, z * a * z ∈ S2) (hz2' : ∀ b ∈ S2, z * b * z ∈ S1)
    (hx : z * x ∈ S1 ⊔ S2) (hx2 : x * x = 1) : ∃ b ∈ S2, x = b⁻¹ * z * b := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hc : S2 ≤ centralizer (S1 : Set G) := fun b hb =>
    mem_centralizer_iff.2 fun a ha => hcomm a ha b hb
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hc hx
  have hxe : x = z * (a * b) := by
    rw [← hab, ← mul_assoc, hz2, one_mul]
  have ha' : z * b * z⁻¹ ∈ S1 := by rw [hzi]; exact hz2' b hb
  have hb' : z * a * z⁻¹ ∈ S2 := by rw [hzi]; exact hz1 a ha
  have hx2' : z * (a * b) * (z⁻¹ * (a * b)) = 1 := by
    rw [hzi, ← hxe]
    exact hx2
  have hprod : (z * b * z⁻¹ * a) * (z * a * z⁻¹ * b) = 1 := by
    have hcm : (z * b * z⁻¹ * a) * (z * a * z⁻¹) = (z * a * z⁻¹) * (z * b * z⁻¹ * a) :=
      hcomm _ (S1.mul_mem ha' ha) _ hb'
    calc (z * b * z⁻¹ * a) * (z * a * z⁻¹ * b)
        = ((z * b * z⁻¹ * a) * (z * a * z⁻¹)) * b := by group
      _ = ((z * a * z⁻¹) * (z * b * z⁻¹ * a)) * b := by rw [hcm]
      _ = z * (a * b) * (z⁻¹ * (a * b)) := by group
      _ = 1 := hx2'
  have h1 : z * b * z⁻¹ * a = 1 := by
    have hmem : z * b * z⁻¹ * a ∈ S2 := by
      have : z * b * z⁻¹ * a = (z * a * z⁻¹ * b)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      rw [this]
      exact S2.inv_mem (S2.mul_mem hb' hb)
    exact (Subgroup.disjoint_def.1 hdisj) (S1.mul_mem ha' ha) hmem
  have ha_eq : a = z * b⁻¹ * z⁻¹ := by
    have : a = (z * b * z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [this]
    group
  refine ⟨b, hb, ?_⟩
  calc x = z * (a * b) := hxe
    _ = z * (z * b⁻¹ * z⁻¹ * b) := by rw [ha_eq]
    _ = (z * z) * b⁻¹ * z⁻¹ * b := by group
    _ = b⁻¹ * z * b := by rw [hz2, one_mul, hzi]

section Sylow

variable [Finite G]

theorem sylow_of_fusion {S : Subgroup G} {z : G} (hS : IsPGroup 2 S) (hzS : z ∈ S)
    (hT : IsSylowOf 2 (S ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hfus : ∀ g : G, g⁻¹ * z * g ∈ S → ∃ s ∈ S, g⁻¹ * z * g = s⁻¹ * z * s) :
    ¬ 2 ∣ S.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP⟩ := hS.exists_le_sylow
  have hSeq : S = (P : Subgroup G) := by
    by_contra hne
    have hlt : S < (P : Subgroup G) := lt_of_le_of_ne hSP hne
    have hPp : IsPGroup 2 ↥(P : Subgroup G) := P.isPGroup'
    have : Group.IsNilpotent ↥(P : Subgroup G) := hPp.isNilpotent
    have hnc : NormalizerCondition ↥(P : Subgroup G) := Group.normalizerCondition_of_isNilpotent
    have hS' : S.subgroupOf (P : Subgroup G) < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      obtain ⟨y, hyP, hyS⟩ := IsConcreteLE.exists_of_lt hlt
      have : (⟨y, hyP⟩ : ↥(P : Subgroup G)) ∈ S.subgroupOf (P : Subgroup G) := by rw [htop]; trivial
      exact hyS this
    obtain ⟨n, hnn, hnS⟩ := IsConcreteLE.exists_of_lt (hnc _ hS')
    have hn1 : ∀ w ∈ S, (n : G) * w * (n : G)⁻¹ ∈ S := by
      intro w hw
      have := (mem_normalizer_iff.1 hnn ⟨w, hSP hw⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hw)
      simpa [Subgroup.mem_subgroupOf] using this
    obtain ⟨t, htS, ht⟩ := hfus ((n : G)⁻¹) (by simpa using hn1 z hzS)
    have hc : t * (n : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc t * (n : G) * z = t * ((n : G) * z * (n : G)⁻¹) * (n : G) := by group
        _ = t * (t⁻¹ * z * t) * (n : G) := by rw [← ht]; simp
        _ = z * (t * (n : G)) := by group
    have hQ : (P : Subgroup G) ⊓ centralizer ({z} : Set G) =
        S ⊓ centralizer ({z} : Set G) := by
      refine hT.eq_of_le (inf_le_inf_right _ hSP) inf_le_right (hPp.to_le inf_le_left)
    have hmem : t * (n : G) ∈ (P : Subgroup G) ⊓ centralizer ({z} : Set G) :=
      Subgroup.mem_inf.2 ⟨(P : Subgroup G).mul_mem (hSP htS) n.2, hc⟩
    rw [hQ] at hmem
    have hnS' : (n : G) ∈ S := by
      have := S.mul_mem (S.inv_mem htS) (Subgroup.mem_inf.1 hmem).1
      simpa using this
    exact hnS (Subgroup.mem_subgroupOf.2 hnS')
  rw [hSeq]
  exact P.not_dvd_index

end Sylow

end CFSG.EvenSporadicStandard.M23Std
