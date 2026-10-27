module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR13

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]


@[expose] def FusionCoreFour (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → orderOf v = 4 → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∈ Subgroup.normalizer (K : Set G)

theorem fusionCoreFour (p f : ℕ) [Fact p.Prime] (hC : Prop370 p f) (hQ : NoQuasidihedral p f) :
    FusionCoreFour p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK
  by_contra hv
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
  have hnt := nontrivAction p f G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz
    hvK hv
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hp2 hq hz hKc hKz hv4 hvz hv hvK' hnt
  have hcl := deltaClassical_of_typeI hC (nontrivAction p f) (typeI_of_noQuasidihedral p f hQ) G
    hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv κ hκK hκ2 hκn hcomm
  exact fusion_chain_contradiction hC G hnab hp2 hq K z hz hbelow hKc hJ hKz ht hne hvJ hv2
    (by omega) hvz hκK hκ2 hκn hcomm hcl

@[expose] def BigOrderCyc (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 8 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) →
          (∀ d ∈ J, d * z = z * d → d * v * d⁻¹ = v⁻¹ → orderOf d ≠ 4) →
            v ∈ Subgroup.normalizer (K : Set G)

theorem bigOrderFC_of_cyc (p f : ℕ) [Fact p.Prime] (h4 : FusionCoreFour p f)
    (hB : BigOrderCyc p f) : BigOrderFC p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8 hvz hvK
  classical
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hH K (CoreAssembly.mem_conjClass_self K) hKz
  by_cases hd : ∃ d ∈ J, d * z = z * d ∧ d * v * d⁻¹ = v⁻¹ ∧ orderOf d = 4
  · obtain ⟨d, hdJ, hdz, hdv, hd4⟩ := hd
    by_contra hv
    have hd2 : IsPGroup 2 (Subgroup.zpowers d) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_zpowers, hd4]
      norm_num
    have hdd : d * d = t := by
      have hd44 : (d * d) * (d * d) = 1 := by
        have : d ^ 4 = 1 := by rw [← hd4]; exact pow_orderOf_eq_one d
        simpa [pow_succ, mul_assoc] using this
      rcases ht.unique (d * d) (J.mul_mem hdJ hdJ) hd44 with h | h
      · exfalso
        have : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
        rw [hd4] at this
        omega
      · exact h
    by_cases hdK : d ∈ Subgroup.normalizer (K : Set G)
    ·
      have hu2 : (v * d) * (v * d) = t := by
        calc (v * d) * (v * d) = v * (d * v * d⁻¹) * (d * d) := by group
          _ = t := by rw [hdv, hdd]; group
      have huz : (v * d) * z = z * (v * d) := by
        calc (v * d) * z = v * (d * z) := by group
          _ = v * (z * d) := by rw [hdz]
          _ = (v * z) * d := by group
          _ = (z * v) * d := by rw [hvz]
          _ = z * (v * d) := by group
      have hu4 : orderOf (v * d) = 4 := by
        have h4' : (v * d) ^ 2 ^ (1 + 1) = 1 := by
          have : (v * d) ^ 4 = ((v * d) * (v * d)) * ((v * d) * (v * d)) := by
            simp [pow_succ, mul_assoc]
          rw [show 2 ^ (1 + 1) = 4 by norm_num, this, hu2]
          exact ht.sq
        have hn2 : ¬ (v * d) ^ 2 ^ 1 = 1 := by
          intro h
          apply ht.ne_one
          rw [← hu2]
          simpa [pow_two] using h
        have := orderOf_eq_prime_pow hn2 h4'
        simpa using this
      have huJ : v * d ∈ J := J.mul_mem hvJ hdJ
      have hupg : IsPGroup 2 (Subgroup.zpowers (v * d)) := by
        refine IsPGroup.of_card (n := 2) ?_
        rw [Nat.card_zpowers, hu4]
        norm_num
      have huK : (v * d) ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
        rw [pow_two, hu2]
        exact htK
      have h1 := h4 G hnab hp2 hq K z hz hbelow J hJ t ht hne hH (v * d) huJ hupg hu4 huz huK
      apply hv
      have : v = (v * d) * d⁻¹ := by group
      rw [this]
      exact (Subgroup.normalizer (K : Set G)).mul_mem h1
        ((Subgroup.normalizer (K : Set G)).inv_mem hdK)
    · have hdK2 : d ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
        rw [pow_two, hdd]
        exact htK
      exact hdK (h4 G hnab hp2 hq K z hz hbelow J hJ t ht hne hH d hdJ hd2 hd4 hdz hdK2)
  · push Not at hd
    exact hB G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8 hvz hvK
      (fun d hdJ hdz hdv => hd d hdJ hdz hdv)

theorem fusionCore_of_residuals_cyc (p f : ℕ) [Fact p.Prime] (hC : Prop370 p f)
    (hQ : NoQuasidihedral p f) (hB : BigOrderCyc p f) : FusionCoreStmt p f :=
  fusionCore_of_core_residuals p f hC hQ (bigOrderFC_of_cyc p f (fusionCoreFour p f hC hQ) hB)

end CFSG.ClassicalInvolution.Asc77.AscFusion
