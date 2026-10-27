module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.WreathEnd
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Fusion

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_fusion [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz2 : z * z = 1) (hz1 : z ≠ 1) {S S0 : Subgroup G} (hS : IsPGroup 2 S) (hzS : z ∈ S)
    (hT : IsSylowOf 2 (S ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hS0 : S0 ≤ S) (hidx : S0.relIndex S = 2) (hz0 : z ∉ S0)
    (hfus : ∀ x ∈ S, x * x = 1 → x ∉ S0 → ∃ s ∈ S, x = s⁻¹ * z * s) :
    ∃ g : G, g⁻¹ * z * g ∈ S0 := by
  by_contra hX
  push Not at hX
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hfus' : ∀ g : G, g⁻¹ * z * g ∈ S → ∃ s ∈ S, g⁻¹ * z * g = s⁻¹ * z * s := by
    intro g hg
    have hx2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
      calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [hz2]; group
    exact hfus _ hg hx2 (hX g)
  have hSidx := sylow_of_fusion hS hzS hT hfus'
  have hz2' : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  obtain ⟨g, hg⟩ := exists_conj_mem_complement hnonab hS hSidx hS0 hidx hzS hz0 hz2'
  exact hX g hg

theorem not_dvd_index_of_weakly_closed {S A : Subgroup G} (hS : IsPGroup 2 S) (hAS : A ≤ S)
    (hwc : ∀ g : G, (∀ x ∈ A, g * x * g⁻¹ ∈ S) → ∀ x ∈ A, g * x * g⁻¹ ∈ A)
    (hSN : S ≤ normalizer (A : Set G)) (hSyl : IsSylowOf 2 S (normalizer (A : Set G))) :
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
      have : (⟨y, hyP⟩ : ↥(P : Subgroup G)) ∈ S.subgroupOf (P : Subgroup G) := by
        rw [htop]; trivial
      exact hyS this
    obtain ⟨n, hnn, hnS⟩ := IsConcreteLE.exists_of_lt (hnc _ hS')
    have hn1 : ∀ w ∈ S, (n : G) * w * (n : G)⁻¹ ∈ S := by
      intro w hw
      have := (mem_normalizer_iff.1 hnn ⟨w, hSP hw⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hw)
      simpa [Subgroup.mem_subgroupOf] using this
    have hnA : ∀ x, x ∈ A ↔ (n : G) * x * (n : G)⁻¹ ∈ A :=
      forall_mem_iff_of_forall_mem (hwc n fun x hx => hn1 x (hAS hx))
    have hnN : (n : G) ∈ normalizer (A : Set G) := Subgroup.mem_normalizer_iff.2 hnA
    have hQP : S ⊔ zpowers (n : G) ≤ (P : Subgroup G) := by
      refine sup_le hSP ?_
      rw [Subgroup.zpowers_le]
      exact n.2
    have hQN : S ⊔ zpowers (n : G) ≤ normalizer (A : Set G) := by
      refine sup_le hSN ?_
      rw [Subgroup.zpowers_le]
      exact hnN
    have hQ := hSyl.eq_of_le le_sup_left hQN (hPp.to_le hQP)
    exact hnS (Subgroup.mem_subgroupOf.2 (by
      rw [← hQ]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  rw [hSeq]
  exact P.not_dvd_index

end CFSG.EvenSporadicStandard.M23Std
