module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] {p : ℕ}

private theorem le_of_isSylowOf_of_le_normalizer {S K X : Subgroup G} (hS : IsSylowOf p S K)
    (hXK : X ≤ K) (hX : IsPGroup p X) (hKX : K ≤ normalizer (X : Set G)) : X ≤ S := by
  obtain ⟨Q, rfl⟩ := hS
  have hn : (X.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  intro x hx
  have hX' : IsPGroup p (X.subgroupOf K) := hX.comap_subtype
  have hxQ : (⟨x, hXK hx⟩ : K) ∈ (Q : Subgroup K) :=
    IsPGroup.le_sylow_of_normal (N := X.subgroupOf K) hX' Q
      (show (⟨x, hXK hx⟩ : K) ∈ X.subgroupOf K from hx)
  exact ⟨_, hxQ, rfl⟩

theorem IsPIsolatedOver.le_of_normal {H K X : Subgroup G} (h : IsPIsolatedOver p K H)
    (hH : IsPGroup p H) (hHK : H ≤ K) (hKH : K ≤ normalizer (H : Set G)) (hXK : X ≤ K)
    (hX : IsPGroup p X) (hKX : K ≤ normalizer (X : Set G)) : X ≤ H := by
  by_contra hXH
  obtain ⟨S, T, hS, hT, hne⟩ := h
  refine hne (Relation.EqvGen.rel _ _ ⟨hS, hT, lt_of_le_of_ne ?_ ?_⟩)
  · exact le_inf (le_of_isSylowOf_of_le_normalizer hS hHK hH hKH)
      (le_of_isSylowOf_of_le_normalizer hT hHK hH hKH)
  · intro heq
    apply hXH
    rw [heq]
    exact le_inf (le_of_isSylowOf_of_le_normalizer hS hXK hX hKX)
      (le_of_isSylowOf_of_le_normalizer hT hXK hX hKX)

theorem le_of_inf_normalizer_le [Finite G] [Fact p.Prime] {H K X : Subgroup G}
    (hO : ∀ Y : Subgroup G, IsPGroup p Y → Y ≤ normalizer (H : Set G) ⊓ K →
      normalizer (H : Set G) ⊓ K ≤ normalizer (Y : Set G) → Y ≤ H)
    (hH : IsPGroup p H) (hHK : H ≤ K) (hX : IsPGroup p X) (hXK : X ≤ K)
    (hXN : normalizer (H : Set G) ⊓ K ≤ normalizer (X : Set G)) : X ≤ H := by
  have hHN : H ≤ normalizer (H : Set G) ⊓ K := le_inf le_normalizer hHK
  have hXH : IsPGroup p (X ⊔ H : Subgroup G) := hX.to_sup_of_normal_left' hH (hHN.trans hXN)
  have hNXH : normalizer (H : Set G) ⊓ K ≤ normalizer ((X ⊔ H : Subgroup G) : Set G) :=
    fun n hn => inf_normalizer_le_normalizer_sup X H ⟨hXN hn, hn.1⟩
  have hY : (X ⊔ H) ⊓ (normalizer (H : Set G) ⊓ K) ≤ H := by
    refine hO _ (hXH.to_le inf_le_left) inf_le_right ?_
    exact (le_inf hNXH le_normalizer).trans inf_normalizer_le_normalizer_inf
  by_contra hXH'
  have hlt : H < X ⊔ H := lt_of_le_of_ne le_sup_right fun heq => hXH' (heq ▸ le_sup_left)
  refine (lt_inf_normalizer_of_isPGroup hXH hlt).not_ge ?_
  calc (X ⊔ H) ⊓ normalizer (H : Set G) = (X ⊔ H) ⊓ (normalizer (H : Set G) ⊓ K) := by
        rw [← inf_assoc, inf_right_comm, inf_eq_left.mpr (sup_le hXK hHK)]
    _ ≤ H := hY

theorem IsPIsolatedOver.le_of_inf_normalizer_le [Finite G] [Fact p.Prime] {H K X : Subgroup G}
    (h : IsPIsolatedOver p (normalizer (H : Set G) ⊓ K) H) (hH : IsPGroup p H) (hHK : H ≤ K)
    (hX : IsPGroup p X) (hXK : X ≤ K)
    (hXN : normalizer (H : Set G) ⊓ K ≤ normalizer (X : Set G)) : X ≤ H :=
  CFSG.GroupTheory.le_of_inf_normalizer_le
    (fun _ hY hYN hNY => h.le_of_normal hH (le_inf le_normalizer hHK) inf_le_left hYN hY hNY)
    hH hHK hX hXK hXN

theorem IsPIsolatedOver.le_of_normalizer_le [Finite G] [Fact p.Prime] {H X : Subgroup G}
    (h : IsPIsolatedOver p (normalizer (H : Set G)) H) (hH : IsPGroup p H) (hX : IsPGroup p X)
    (hXN : normalizer (H : Set G) ≤ normalizer (X : Set G)) : X ≤ H :=
  IsPIsolatedOver.le_of_inf_normalizer_le (K := ⊤) (by rwa [inf_top_eq]) hH le_top hX le_top
    (by rwa [inf_top_eq])

end CFSG.GroupTheory
