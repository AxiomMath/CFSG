module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.DataTransport

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G X : Type} [Group G] [Group X]

theorem normalizer_map_inf_range {φ : X →* G} (hφ : Function.Injective φ) (F : Subgroup X) :
    normalizer ((F.map φ : Subgroup G) : Set G) ⊓ φ.range = (normalizer (F : Set X)).map φ := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgN, ⟨n, rfl⟩⟩ := Subgroup.mem_inf.1 hg
    refine ⟨n, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.1 hgN (φ x)
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφ,
      Subgroup.mem_map_iff_mem hφ] at h1
    exact h1
  · rintro _ ⟨n, hn, rfl⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2
      (mem_map_iff_conj hφ (Subgroup.mem_normalizer_iff.1 hn)), ⟨n, rfl⟩⟩

@[expose] def NormQuotA7 (N F : Subgroup G) : Prop :=
  ∃ ψ : ↥N →* alternatingGroup (Fin 7), Function.Surjective ψ ∧ ψ.ker = F.subgroupOf N

theorem NormQuotA7.of_equiv {N F : Subgroup G} [(F.subgroupOf N).Normal]
    (e : ↥N ⧸ F.subgroupOf N ≃* alternatingGroup (Fin 7)) : NormQuotA7 N F := by
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (F.subgroupOf N)), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk x) = 1 ↔ x ∈ F.subgroupOf N
    rw [map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff]

theorem NormQuotA7.map {φ : X →* G} (hφ : Function.Injective φ) {N F : Subgroup X}
    (h : NormQuotA7 N F) : NormQuotA7 (N.map φ) (F.map φ) := by
  obtain ⟨ψ, hψ, hker⟩ := h
  let e : ↥N ≃* ↥(N.map φ) := Subgroup.equivMapOfInjective N φ hφ
  have he : ∀ x : ↥N, ((e x : ↥(N.map φ)) : G) = φ (x : X) := fun x => rfl
  refine ⟨ψ.comp e.symm.toMonoidHom, hψ.comp e.symm.surjective, ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, he]
  show ψ (e.symm (e x)) = 1 ↔ _
  rw [MulEquiv.symm_apply_apply, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  exact (Subgroup.mem_map_iff_mem hφ).symm

end CFSG.EvenSporadicStandard.M23Std
