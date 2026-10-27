module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_mem_closure_subtype_iff {G : Type} [Group G] (K : Subgroup G) (S : Set G)
    (hS : S ⊆ (K : Set G)) (m : ↥K) :
    (m : G) ∈ Subgroup.closure S ↔ m ∈ Subgroup.closure (K.subtype ⁻¹' S : Set ↥K) := by
  have h_img : K.subtype '' (K.subtype ⁻¹' S : Set ↥K) = S := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, hS hx⟩, hx, rfl⟩
  have key : (Subgroup.closure (K.subtype ⁻¹' S : Set ↥K)).map K.subtype =
      Subgroup.closure S := by
    rw [MonoidHom.map_closure, h_img]
  rw [← key]
  exact Subgroup.mem_map_iff_mem K.subtype_injective

theorem s7_centralizer_subtype_equiv {G : Type} [Group G] (K : Subgroup G) (t : ↥K)
    (L : Subgroup G) (hL : ∀ g : G, g ∈ L ↔ g ∈ K ∧ g * (t : G) = (t : G) * g) :
    Nonempty (↥(Subgroup.centralizer ({t} : Set ↥K)) ≃* ↥L) := by
  have hLK : L ≤ K := fun g hg => ((hL g).mp hg).1
  have h_eq : Subgroup.centralizer ({t} : Set ↥K) = L.subgroupOf K := by
    ext k
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      exact (hL (k : G)).mpr
        ⟨k.2, by simpa only [Subgroup.coe_mul] using congrArg Subtype.val hk⟩
    · intro hk
      have hcomm : (k : G) * (t : G) = (t : G) * (k : G) := ((hL (k : G)).mp hk).2
      exact Subtype.ext (by simpa only [Subgroup.coe_mul] using hcomm)
  exact ⟨(MulEquiv.subgroupCongr h_eq).trans (Subgroup.subgroupOfEquivOfLe hLK)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
