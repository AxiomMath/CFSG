module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPreimage

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ProperTwoGeneratedCore

variable {G K : Type*} [Group G] [Group K]

theorem normal_closure_map (f : G →* K) (hf : Function.Surjective f)
    (Q : Subgroup G) :
    (Subgroup.normalClosure (Q : Set G)).map f =
      Subgroup.normalClosure (Q.map f : Set K) := by
  rw [Subgroup.map_normalClosure _ f hf, Subgroup.coe_map]

@[expose] def normalClosureHom (f : G →* K) (Q : Subgroup G) :
    Subgroup.normalClosure (Q : Set G) →*
      Subgroup.normalClosure (Q.map f : Set K) :=
  (f.comp (Subgroup.normalClosure (Q : Set G)).subtype).codRestrict
    (Subgroup.normalClosure (Q.map f : Set K)) (fun x => by
      have hle := Subgroup.map_normalClosure_le (Q : Set G) f
      rw [← Subgroup.coe_map] at hle
      exact hle (Subgroup.mem_map_of_mem f x.property))

theorem normalClosureHom_apply (f : G →* K) (Q : Subgroup G)
    (x : Subgroup.normalClosure (Q : Set G)) :
    (normalClosureHom f Q x : K) = f (x : G) := rfl

theorem normalClosureHom_surjective (f : G →* K) (hf : Function.Surjective f)
    (Q : Subgroup G) : Function.Surjective (normalClosureHom f Q) := by
  rintro ⟨y, hy⟩
  rw [← normal_closure_map f hf Q] at hy
  obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩

theorem normalClosureHom_ker (f : G →* K) (Q : Subgroup G) :
    (normalClosureHom f Q).ker =
      f.ker.subgroupOf (Subgroup.normalClosure (Q : Set G)) := by
  ext x
  change (normalClosureHom f Q x = 1) ↔ f (x : G) = 1
  exact Subtype.ext_iff

variable [Finite G]

omit [Finite G] in
theorem normalClosureHom_odd_ker (f : G →* K)
    (hodd : Odd (Nat.card f.ker)) (Q : Subgroup G) :
    Odd (Nat.card (normalClosureHom f Q).ker) := by
  rw [normalClosureHom_ker]
  have hcard : Nat.card (f.ker.subgroupOf (Subgroup.normalClosure (Q : Set G))) =
      Nat.card (f.ker ⊓ Subgroup.normalClosure (Q : Set G) : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  rw [hcard]
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)

theorem normal_closure_normalizer_preimage (f : G →* K)
    (hf : Function.Surjective f) (hkerodd : Odd (Nat.card f.ker))
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    ((Subgroup.normalizer (Q.map f : Set K)).subgroupOf
      (Subgroup.normalClosure (Q.map f : Set K))).comap (normalClosureHom f Q) =
    (Subgroup.normalizer (Q : Set G)).subgroupOf
      (Subgroup.normalClosure (Q : Set G)) := by
  ext x
  change f (x : G) ∈ Subgroup.normalizer (Q.map f : Set K) ↔
    (x : G) ∈ Subgroup.normalizer (Q : Set G)
  have hpre := odd_kernel_normalizer_preimage f hf hkerodd Q htight hodd hker
  change (x : G) ∈ (Subgroup.normalizer (Q.map f : Set K)).comap f ↔ _
  rw [hpre]

variable [Finite K]

theorem normal_closure_strong_embedding_of_odd_kernel_image (f : G →* K)
    (hf : Function.Surjective f) (hkerodd : Odd (Nat.card f.ker))
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G))
    (himage : fusionStronglyEmbedded
      ((Subgroup.normalizer (Q.map f : Set K)).subgroupOf
        (Subgroup.normalClosure (Q.map f : Set K)))) :
    fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf
        (Subgroup.normalClosure (Q : Set G))) := by
  have h := strongly_embedded_preimage_of_odd_kernel (normalClosureHom f Q)
    (normalClosureHom_surjective f hf Q) (normalClosureHom_odd_ker f hkerodd Q)
    ((Subgroup.normalizer (Q.map f : Set K)).subgroupOf
      (Subgroup.normalClosure (Q.map f : Set K))) himage
  rwa [normal_closure_normalizer_preimage f hf hkerodd Q htight hodd hker] at h

end CFSG.ComponentClassification.AschbacherTightEmbedding
