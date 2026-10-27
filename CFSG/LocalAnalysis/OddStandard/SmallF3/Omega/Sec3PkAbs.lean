module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

theorem mem_centralizer_self {Y : Type*} [Group Y] (z : Y) :
    z ∈ centralizer ({z} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem Sl23PocketIn.top_of_centralizer_equiv {Y A : Type} [Group Y] [Group A] {z : Y}
    (ψ : ↥(centralizer ({z} : Set Y)) ≃* A) (S : Subgroup A) [S.Normal]
    (hz : ψ ⟨z, mem_centralizer_self z⟩ ∈ S) (hS : IsSL23Mod ↥S) :
    ∃ K : Subgroup Y, Sl23PocketIn (⊤ : Subgroup Y) z K := by
  let ι : A →* Y := (centralizer ({z} : Set Y)).subtype.comp ψ.symm.toMonoidHom
  have hι : Function.Injective ι :=
    (centralizer ({z} : Set Y)).subtype_injective.comp ψ.symm.injective
  have hιC : ∀ a : A, ι a ∈ centralizer ({z} : Set Y) := fun a => (ψ.symm a).2
  have hιψ : ∀ c : ↥(centralizer ({z} : Set Y)), ι (ψ c) = (c : Y) := fun c => by
    change ((ψ.symm (ψ c) : ↥(centralizer ({z} : Set Y))) : Y) = c
    rw [MulEquiv.symm_apply_apply]
  refine ⟨S.map ι, ⟨ψ ⟨z, mem_centralizer_self z⟩, hz, hιψ _⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨s, -, rfl⟩
    exact ⟨Subgroup.mem_top _, hιC s⟩
  · have hn : ((S.map ι).subgroupOf (⊤ ⊓ centralizer ({z} : Set Y))).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨s, hs, hsn⟩ := hn
      have hgC : (g : Y) ∈ centralizer ({z} : Set Y) := g.2.2
      refine ⟨ψ ⟨g, hgC⟩ * s * (ψ ⟨g, hgC⟩)⁻¹, (inferInstance : S.Normal).conj_mem s hs _, ?_⟩
      rw [map_mul, map_mul, map_inv, hιψ ⟨g, hgC⟩, hsn]
      rfl
    exact hn.isSubnormal
  · exact isSL23Mod_of_mulEquiv (S.equivMapOfInjective ι hι) hS

theorem isI4PlusIn_top_of_centralizer_equiv {Y A : Type} [Group Y] [Group A] {z : Y}
    (hz2 : orderOf z = 2) (ψ : ↥(centralizer ({z} : Set Y)) ≃* A) (S : Subgroup A) [S.Normal]
    (hz : ψ ⟨z, mem_centralizer_self z⟩ ∈ S) (hS : IsSL23Mod ↥S) :
    IsI4PlusIn (⊤ : Subgroup Y) z :=
  ⟨hz2, Sl23PocketIn.top_of_centralizer_equiv ψ S hz hS⟩

end CFSG.OddStandard.SmallF3.Omega
