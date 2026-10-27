module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR2

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]


@[expose] def DeltaData (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 4 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ∃ κ ∈ K, κ * κ = z ∧ (v * v)⁻¹ * κ * (v * v) = κ⁻¹ ∧
              κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ ∧
              ∃ I ∈ CoreAssembly.conjClass K, IsUniqueInvolution I (κ * (v⁻¹ * κ * v))

theorem fusionCore_of_prop370_of_deltaData (hC : Prop370 p f) (hD : DeltaData p f) :
    FusionCoreStmt p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK
  by_contra hv
  have hUK : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  obtain ⟨κ, hκK, hκ2, hκn, hcomm, hcl⟩ :=
    hD G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv
  exact fusion_chain_contradiction hC G hnab hp2 hq K z hz hbelow hKc hJ hUK ht hne hvJ hv2 hv4
    hvz hκK hκ2 hκn hcomm hcl

end CFSG.ClassicalInvolution.Asc77.AscFusion
