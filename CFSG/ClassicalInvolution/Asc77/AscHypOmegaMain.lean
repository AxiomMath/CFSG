module

public import CFSG.ClassicalInvolution.Asc77.AscHypOmegaTwin
public import CFSG.ClassicalInvolution.Asc77.WP2Stand

public section

namespace CFSG.ClassicalInvolution.Asc77.AscHypOmega

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

section Fusion

variable {G : Type} [Group G]

@[expose] def TheoremIFirst (K : Subgroup G) (z : G) : Prop :=
  ∀ k ∈ K, IsPGroup 2 (Subgroup.zpowers k) → k ∉ Subgroup.zpowers z →
    ∀ g : G, g⁻¹ * k * g ∈ Subgroup.centralizer ({z} : Set G) →
      g⁻¹ * k * g ∈ Subgroup.normalizer (K : Set G)

@[expose] def FusionAt (K : Subgroup G) (z : G) : Prop :=
  HasTwin K z → ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
    ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → (¬ ∀ w ∈ J, v * w = w * v) →
      v * z = z * v → v ∈ Subgroup.normalizer (K : Set G)

end Fusion

@[expose] def ClassicalFusionStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → FusionAt K z

section Proofs

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}

theorem fusionAt_of_theoremIFirst (hz : IsClassicalMember p f K z) (h : TheoremIFirst K z) :
    FusionAt K z := by
  intro _ J hJ t _ _ v hvJ hv2 hvnc hvz
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  have hKC : K ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hz.subnormal
  have hk : b⁻¹ * v * b ∈ K := mem_conjSub_iff.mp hvJ
  have hk2 : IsPGroup 2 (Subgroup.zpowers (b⁻¹ * v * b)) := by
    have := isPGroup_zpowers_conj hv2 b⁻¹
    rwa [inv_inv] at this
  have hkz : b⁻¹ * v * b ∉ Subgroup.zpowers z := by
    intro hmem
    apply hvnc
    intro w hw
    have hwK : b⁻¹ * w * b ∈ K := mem_conjSub_iff.mp hw
    have hcomm : (b⁻¹ * v * b) * (b⁻¹ * w * b) = (b⁻¹ * w * b) * (b⁻¹ * v * b) := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← hn]
      have hzc : z * (b⁻¹ * w * b) = (b⁻¹ * w * b) * z :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hKC hwK)).symm
      exact ((Commute.zpow_left (show Commute z (b⁻¹ * w * b) from hzc) n).eq)
    calc v * w = b * ((b⁻¹ * v * b) * (b⁻¹ * w * b)) * b⁻¹ := by group
      _ = b * ((b⁻¹ * w * b) * (b⁻¹ * v * b)) * b⁻¹ := by rw [hcomm]
      _ = w * v := by group
  have hgv : (b⁻¹)⁻¹ * (b⁻¹ * v * b) * b⁻¹ = v := by group
  have := h _ hk hk2 hkz b⁻¹ (by rw [hgv]; exact Subgroup.mem_centralizer_singleton_iff.mpr hvz)
  rwa [hgv] at this

theorem omega5At_of_fusionAt (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h₀ : IsClassicalMember p f K z)
    (hfus : FusionAt K z) : Omega5At (CoreAssembly.conjClass K) K z := by
  intro J hJ _ v hvJ hvnc hv2 hvz
  have hU₀ := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq h₀
  obtain ⟨b, rfl⟩ := CoreAssembly.single_class K J hJ
  have hUb := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq (h₀.conj b)
  by_cases ht : b * z * b⁻¹ = z
  · refine normalizer_of_twins hp2 hq h₀ (CoreAssembly.mem_conjClass_self K) hJ hU₀ ?_ hvJ
    rw [← ht]
    exact hUb
  · by_cases htw : HasTwin K z
    · exact hfus htw _ hJ _ hUb ht v hvJ hv2 hvnc hvz
    · exact centralizer_le_normalizer_of_not_hasTwin hU₀ htw
        (Subgroup.mem_centralizer_singleton_iff.mpr hvz)

theorem hypOmegaMod_of_fusionAt (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hz : IsClassicalMember p f K z)
    (hfus : FusionAt K z) : HypOmegaMod p f (CoreAssembly.conjClass K) where
  conjInvariant := conjInvariant_conjClass K
  classical := fun L hL => by
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K L hL
    exact ⟨g * z * g⁻¹, hz.conj g⟩
  omega4 := fun _ h₁ _ hJ hne => omega4_of_classical hp2 hq hz h₁ hJ hne
  omega5 := omega5_of_omega5At hp2 hq hz (omega5At_of_fusionAt hp2 hq hz hfus)

theorem hypOmegaMod_of_not_hasTwin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hz : IsClassicalMember p f K z) (h : ¬ HasTwin K z) :
    HypOmegaMod p f (CoreAssembly.conjClass K) :=
  hypOmegaMod_of_fusionAt hp2 hq hz fun htw => absurd htw h

end Proofs

@[expose] def HypOmegaAllStmt (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → HypOmegaMod p f (CoreAssembly.conjClass K)

theorem hypOmegaAllStmt_of_fusion (h : ClassicalFusionStmt p f) : HypOmegaAllStmt p f :=
  fun G _ _ _ hnab hp2 hq K z hz hbelow =>
    hypOmegaMod_of_fusionAt hp2 hq hz (h G hnab hp2 hq K z hz hbelow)

theorem hypOmegaModD_of_all (h : HypOmegaAllStmt p f) : HypOmegaModD p f :=
  fun G _ _ _ K z hb => h G hb.nonabelian hb.odd hb.five K z hb.member hb.below

theorem hypOmegaModD_of_fusion (h : ClassicalFusionStmt p f) : HypOmegaModD p f :=
  hypOmegaModD_of_all (hypOmegaAllStmt_of_fusion h)

theorem hypOmegaModD_of_not_hasTwin
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
      DBranchD p f K z → ¬ HasTwin K z) : HypOmegaModD p f :=
  fun G _ _ _ K z hb =>
    hypOmegaMod_of_not_hasTwin hb.odd hb.five hb.member (h G K z hb)

theorem classicalFusionStmt_of_theoremIFirst
    (h : ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
      p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
        CITBelowU p f (Nat.card G) → TheoremIFirst K z) :
    ClassicalFusionStmt p f :=
  fun G _ _ _ hnab hp2 hq K z hz hbelow =>
    fusionAt_of_theoremIFirst hz (h G hnab hp2 hq K z hz hbelow)

end CFSG.ClassicalInvolution.Asc77.AscHypOmega
