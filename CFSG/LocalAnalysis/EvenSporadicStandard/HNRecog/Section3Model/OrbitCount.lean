module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog.Section3
open CFSG.Sporadic.SmallOddCore
open Subgroup

theorem nonempty_mulEquiv_inf_Gx_of_conj {G : Type} [Group G] {K : Subgroup G} {k c : G}
    (hk : k ∈ K) : Nonempty (↥(K ⊓ Gx (k * c * k⁻¹)) ≃* ↥(K ⊓ Gx c)) := by
  refine ⟨{ toFun := fun x => ⟨k⁻¹ * x.1 * k, ?_⟩
            invFun := fun y => ⟨k * y.1 * k⁻¹, ?_⟩
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_ }⟩
  · exact ⟨K.mul_mem (K.mul_mem (K.inv_mem hk) x.2.1) hk, by
      refine mem_Gx.mpr ?_
      have hx : (k * c * k⁻¹) * x.1 = x.1 * (k * c * k⁻¹) := mem_Gx.mp x.2.2
      calc c * (k⁻¹ * x.1 * k)
          = k⁻¹ * ((k * c * k⁻¹) * x.1) * k := by group
        _ = k⁻¹ * (x.1 * (k * c * k⁻¹)) * k := by rw [hx]
        _ = (k⁻¹ * x.1 * k) * c := by group⟩
  · exact ⟨K.mul_mem (K.mul_mem hk y.2.1) (K.inv_mem hk), by
      refine mem_Gx.mpr ?_
      have hy : c * y.1 = y.1 * c := mem_Gx.mp y.2.2
      calc (k * c * k⁻¹) * (k * y.1 * k⁻¹)
          = k * (c * y.1) * k⁻¹ := by group
        _ = k * (y.1 * c) * k⁻¹ := by rw [hy]
        _ = (k * y.1 * k⁻¹) * (k * c * k⁻¹) := by group⟩
  · intro x
    ext
    group
  · intro y
    ext
    group
  · intro x y
    ext
    simp only [Subgroup.coe_mul]
    group

theorem orbitPartition_of_rows {G : Type} [Group G] [Finite G] {ι : Type} [Fintype ι]
    (K : Subgroup G) (B : Set G) (T : ι → Set G) (c : ι → G) (n : ι → ℕ)
    (hsub : ∀ i, T i ⊆ B) (hdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (hinv : ∀ i, ∀ k ∈ K, ∀ x ∈ T i, k * x * k⁻¹ ∈ T i)
    (hc : ∀ i, c i ∈ T i) (hstab : ∀ i, Nat.card ↥(K ⊓ Gx (c i)) = n i)
    (hsum : ∑ i, Nat.card K / n i = B.ncard) :
    IsOrbitPartition K B T ∧ StabCard K T n := by
  classical
  let O : ι → Set G := fun i => conjClass K (c i)
  have hO_sub_T : ∀ i, O i ⊆ T i := by
    intro i x hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass.mp hx
    exact hinv i k hk (c i) (hc i)
  have hO_sub_B : ∀ i, O i ⊆ B := fun i => (hO_sub_T i).trans (hsub i)
  have hO_disj : Pairwise (fun i j => Disjoint (O i) (O j)) := by
    intro i j hij
    exact (hdisj i j hij).mono (hO_sub_T i) (hO_sub_T j)
  have hcardO : ∀ i, (O i).ncard = Nat.card K / n i := by
    intro i
    have h1 := ncard_conjClass_mul_card K (c i)
    have hstab' : Nat.card ↥(K ⊓ centralizer ({c i} : Set G)) = n i := hstab i
    rw [hstab'] at h1
    have hpos : 0 < n i := by
      haveI : Nonempty ↥(K ⊓ centralizer ({c i} : Set G)) := ⟨1, by simp⟩
      rw [← hstab']
      exact Nat.card_pos
    have h2 : Nat.card K = (O i).ncard * n i := h1.symm
    rw [h2, Nat.mul_div_left (O i).ncard hpos]
  have hsumO : ∑ i, (O i).ncard = B.ncard :=
    calc ∑ i, (O i).ncard = ∑ i, Nat.card K / n i :=
          Finset.sum_congr rfl (fun i _ => hcardO i)
      _ = B.ncard := hsum
  have hUcard : (⋃ i, O i).ncard = ∑ i, (O i).ncard := by
    rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (O i)) hO_disj,
      finsum_eq_sum_of_fintype]
  have hUcard' : (⋃ i, O i).ncard = B.ncard := by rw [hUcard, hsumO]
  have hUeqB : (⋃ i, O i) = B :=
    Set.eq_of_subset_of_ncard_le (Set.iUnion_subset hO_sub_B) hUcard'.ge
  have hTeqO : ∀ i, T i = O i := by
    intro i
    refine Set.Subset.antisymm ?_ (hO_sub_T i)
    intro x hxT
    have hxU : x ∈ ⋃ j, O j := by rw [hUeqB]; exact hsub i hxT
    obtain ⟨j, hxOj⟩ := Set.mem_iUnion.mp hxU
    have hij : i = j := by
      by_contra hne
      exact (Set.disjoint_left.mp (hdisj i j hne) hxT) (hO_sub_T j hxOj)
    rw [hij]
    exact hxOj
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    rw [hTeqO i]
    exact hO_sub_B i
  · intro x hx
    have hxU : x ∈ ⋃ j, O j := by rw [hUeqB]; exact hx
    obtain ⟨j, hxOj⟩ := Set.mem_iUnion.mp hxU
    exact ⟨j, by rw [hTeqO j]; exact hxOj⟩
  · intro i j hij
    exact hdisj i j hij
  · intro i
    rw [hTeqO i]
    refine ⟨?_, ?_, ?_⟩
    · intro k hk x hx
      obtain ⟨g, hg, rfl⟩ := mem_conjClass.mp hx
      exact mem_conjClass.mpr ⟨k * g, K.mul_mem hk hg, by group⟩
    · exact ⟨c i, self_mem_conjClass K (c i)⟩
    · intro x hx y hy
      obtain ⟨g, hg, rfl⟩ := mem_conjClass.mp hx
      obtain ⟨g', hg', rfl⟩ := mem_conjClass.mp hy
      exact ⟨g' * g⁻¹, K.mul_mem hg' (K.inv_mem hg), by group⟩
  · intro i x hx
    rw [hTeqO i] at hx
    obtain ⟨k, hk, rfl⟩ := mem_conjClass.mp hx
    obtain ⟨e⟩ := nonempty_mulEquiv_inf_Gx_of_conj (K := K) (k := k) (c := c i) hk
    rw [Nat.card_congr e.toEquiv]
    exact hstab i

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
