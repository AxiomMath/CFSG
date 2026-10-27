module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR6
public import CFSG.ClassicalInvolution.Asc77.AscFusionR3

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]


@[expose] def NontrivAction (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → orderOf v = 4 → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ¬ ∀ k ∈ K, ⁅v * v, k⁆ ∈ oddCoreOf K

@[expose] def DeltaClassical (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → orderOf v = 4 → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ∀ κ ∈ K, κ * κ = z → (v * v)⁻¹ * κ * (v * v) = κ⁻¹ →
              κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ →
                ∃ I ∈ CoreAssembly.conjClass K, IsUniqueInvolution I (κ * (v⁻¹ * κ * v))

@[expose] def BigOrder (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 8 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ∃ κ ∈ K, κ * κ = z ∧ (v * v)⁻¹ * κ * (v * v) = κ⁻¹ ∧
              κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ ∧
              ∃ I ∈ CoreAssembly.conjClass K, IsUniqueInvolution I (κ * (v⁻¹ * κ * v))

theorem deltaData_of_residuals (hA : NontrivAction p f) (hcl : DeltaClassical p f)
    (h8 : BigOrder p f) : DeltaData p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv
  obtain ⟨s, hs⟩ := hv2.exists_card_eq
  rw [Nat.card_zpowers] at hs
  have hs2 : 2 ≤ s := by
    by_contra hlt
    have : 2 ^ s ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hs2 with h2 | h3
  ·
    have hv4' : orderOf v = 4 := by rw [hs, ← h2]; norm_num
    have hKz : IsUniqueInvolution K z :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
    have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
    have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
    have hnt := hA G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4' hvz hvK hv
    obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ :=
      exists_kappa hp2 hq hz hKc hKz hv4' hvz hv hvK' hnt
    exact ⟨κ, hκK, hκ2, hκn, hcomm,
      hcl G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4' hvz hvK hv κ hκK hκ2 hκn
        hcomm⟩
  · have h8le : 8 ≤ orderOf v := by
      rw [hs]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) h3
    exact h8 G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8le hvz hvK hv

theorem fusionCore_of_residuals (hC : Prop370 p f) (hA : NontrivAction p f)
    (hcl : DeltaClassical p f) (h8 : BigOrder p f) : FusionCoreStmt p f :=
  fusionCore_of_prop370_of_deltaData hC (deltaData_of_residuals hA hcl h8)

end CFSG.ClassicalInvolution.Asc77.AscFusion
