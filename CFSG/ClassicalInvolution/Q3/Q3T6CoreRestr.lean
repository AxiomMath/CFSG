module

public import CFSG.ClassicalInvolution.Uniform.UHypOmegaGen
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreLift
public import CFSG.ClassicalInvolution.Asc77.AscIHSectL

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement


section Restrict

variable {t : MemberType} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hypOmegaModU_restrict (hΩ : HypOmegaModU t Ω) (Y : Subgroup G) :
    HypOmegaModU t (restrictFamily Ω Y) where
  conjInvariant := by
    rintro n _ ⟨L, hL, hLY, rfl⟩
    refine ⟨conjSub (n : G) L, hΩ.conjInvariant _ L hL, ?_, conjSub_subgroupOf Y n L⟩
    have := conjSub_mono (n := (n : G)) hLY
    rwa [conjSub_eq_self_of_mem n.2] at this
  classical := by
    rintro _ ⟨L, hL, hLY, rfl⟩
    obtain ⟨z, hz⟩ := hΩ.classical L hL
    exact ⟨_, hz.subgroupOf hLY⟩
  omega4 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    obtain ⟨h1, h2⟩ := hΩ.omega4 K hK J hJ hKJ
    have hcard : Nat.card ↥(K.subgroupOf Y ⊓ J.subgroupOf Y) = Nat.card ↥(K ⊓ J) := by
      rw [inf_subgroupOf_eq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hKY)).toEquiv
    rw [hcard]
    refine ⟨h1, fun h => ?_⟩
    have hle := h2 h
    rw [oddCoreOf_subgroupOf hKY, oddCoreOf_subgroupOf hJY]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    have hab : (⁅(a : G), (b : G)⁆) ∈ ⁅K, J⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
        (Subgroup.mem_subgroupOf.mp hb)
    exact ⟨Subgroup.mem_subgroupOf.mpr (hle hab).1, Subgroup.mem_subgroupOf.mpr (hle hab).2⟩
  omega5 := by
    rintro _ ⟨K, hK, hKY, rfl⟩ _ ⟨J, hJ, hJY, rfl⟩ hne z' hz' v hv hnc hv2 hvz
    have hKJ : K ≠ J := fun h => hne (by rw [h])
    have hzK : IsUniqueInvolution K (z' : G) := isUniqueInvolution_of_subgroupOf hz' hKY
    have hvJ : (v : G) ∈ J := Subgroup.mem_subgroupOf.mp hv
    have hnc' : ¬ ∀ w ∈ J, (v : G) * w = w * (v : G) := by
      intro h
      apply hnc
      rintro ⟨w, hw⟩ hw'
      exact Subtype.ext (h w (Subgroup.mem_subgroupOf.mp hw'))
    have hv2' : IsPGroup 2 (Subgroup.zpowers (v : G)) := isPGroup_zpowers_coe_iff.mpr hv2
    have hn := hΩ.omega5 K hK J hJ hKJ (z' : G) hzK (v : G) hvJ hnc' hv2' (congrArg Subtype.val hvz)
    exact (mem_normalizer_subgroupOf_iff hKY).mp hn

end Restrict

section Commute

variable {Y₀ : Type} [Group Y₀] [Finite Y₀] {Λ₀ : Set (Subgroup Y₀)}

theorem false_of_commutes_in_section (hΩ : HypOmegaModU (.sl2 3 1) Λ₀) (hDE : DEdgeless Λ₀)
    {A B : Subgroup (↥(omegaGen Λ₀) ⧸ classicalInvolutionOddCore ↥(omegaGen Λ₀))}
    (hA : A ∈ oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀)))
    (hB : B ∈ oddQuotientFamily (restrictFamily Λ₀ (omegaGen Λ₀))) (hAB : Commutes A B) :
    False := by
  set Y : Subgroup Y₀ := omegaGen Λ₀ with hY
  set N : Subgroup ↥Y := classicalInvolutionOddCore ↥Y with hN
  have hΩ' : HypOmegaModU (.sl2 3 1) (restrictFamily Λ₀ Y) := hypOmegaModU_restrict hΩ Y
  have hΩg : HypOmegaGen (restrictFamily Λ₀ Y) :=
    hypOmegaGenU_of_modU (MemberType.cert_sl2 3 1) hΩ'
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  obtain ⟨K, hK, rfl⟩ := hA
  obtain ⟨M, hM, rfl⟩ := hB
  by_cases hMK : M.map (QuotientGroup.mk' N) = K.map (QuotientGroup.mk' N)
  · obtain ⟨x, hx, y, hy, hxy⟩ := exists_noncomm_map_of_mem hΩg hK
    apply hxy
    exact hAB _ ⟨x, hx, rfl⟩ _ (hMK ▸ ⟨y, hy, rfl⟩)
  · have hcomm : ∀ x ∈ M, ∀ y ∈ K, QuotientGroup.mk' N x * QuotientGroup.mk' N y =
        QuotientGroup.mk' N y * QuotientGroup.mk' N x := fun x hx y hy =>
      (hAB _ ⟨y, hy, rfl⟩ _ ⟨x, hx, rfl⟩).symm
    obtain ⟨n, -, hn⟩ := exists_conj_omegaNbr_of_commute hΩg hNodd hK hM hMK hcomm
    exact dEdgeless_restrictFamily hDE Y (conjSub n K) (hΩ'.conjInvariant n K hK) M hM (Or.inl hn)

end Commute

end CFSG.ClassicalInvolution.Q3.Q3T6
