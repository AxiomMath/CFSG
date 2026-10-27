module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSylowTools
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.SquaresCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import Certificates.Certificate24160

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.ABGLocalTools CFSG.Blueprint.NativeSporadic
  CFSG.EvenSporadicStandard.Wong77.M23Sylow

theorem m23_sylow_squares_noncomm_of_le
    {G : Type} [Group G] [Finite G] {L K : Subgroup G} (hL : IsSporadic L .M23) (hLK : L ≤ K)
    {S : Subgroup G} (hS : IsSylowOf 2 S K) :
    ∃ a ∈ S, ∃ b ∈ S, a * a * (b * b) ≠ b * b * (a * a) := by
  obtain ⟨e⟩ := hL
  let φ : Carrier .M23 →* G := L.subtype.comp e.symm.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.symm.injective
  have hφK : sylowS.map φ ≤ K := by
    rintro _ ⟨g, -, rfl⟩
    exact hLK (e.symm g).2
  have hP : IsPGroup 2 (sylowS.map φ) :=
    (IsPGroup.of_card (card_sylowS (Certificates.certificate24160).1)).map φ
  obtain ⟨k, -, hk⟩ := CFSG.ComponentClassification.FooteLit.exists_conj_le_of_isSylowOf hS hφK hP
  obtain ⟨x, hx, w, hw, hne⟩ := SquaresCheck.exists_noncomm_squares
  refine ⟨k⁻¹ * φ x * k, hk _ (mem_map_of_mem φ hx), k⁻¹ * φ w * k,
    hk _ (mem_map_of_mem φ hw), fun h => hne (hφ ?_)⟩
  have h3 : k⁻¹ * (φ x * φ x * (φ w * φ w)) * k = k⁻¹ * (φ w * φ w * (φ x * φ x)) * k :=
    calc k⁻¹ * (φ x * φ x * (φ w * φ w)) * k
        = k⁻¹ * φ x * k * (k⁻¹ * φ x * k) * (k⁻¹ * φ w * k * (k⁻¹ * φ w * k)) := by group
      _ = k⁻¹ * φ w * k * (k⁻¹ * φ w * k) * (k⁻¹ * φ x * k * (k⁻¹ * φ x * k)) := h
      _ = k⁻¹ * (φ w * φ w * (φ x * φ x)) * k := by group
  simpa only [map_mul] using mul_left_cancel (mul_right_cancel h3)

theorem m23_sylow_squares_noncomm
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (_h : StdHyp G L)
    (hL : IsSporadic L .M23) {z : G} (hz : z ∈ centralizer (L : Set G))
    (_hz2 : orderOf z = 2) {S : Subgroup G} (hS : IsSylowOf 2 S (centralizer ({z} : Set G))) :
    ∃ a ∈ S, ∃ b ∈ S, a * a * (b * b) ≠ b * b * (a * a) :=
  m23_sylow_squares_noncomm_of_le hL
    (fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hz l hl)) hS

end CFSG.EvenSporadicStandard.M23Std
