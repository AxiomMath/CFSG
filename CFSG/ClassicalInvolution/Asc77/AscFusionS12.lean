module

public import CFSG.ClassicalInvolution.Asc77.AscFusionS10
public import CFSG.ClassicalInvolution.Asc77.AscFusionS11
public import CFSG.ClassicalInvolution.Asc77.AscFusionR13

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement Pointwise

variable {p f : ℕ} [Fact p.Prime]


theorem noQuasidihedral (p f : ℕ) [Fact p.Prime] : NoQuasidihedral p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv R hR2 htR hRK
  classical
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have hz2 : z * z = 1 := hKz.sq
  have ht2 : t * t = 1 := ht.sq
  have hvv : v * v = t := by
    have hv22 : (v * v) * (v * v) = 1 := by
      have : v ^ 4 = 1 := by rw [← hv4]; exact pow_orderOf_eq_one v
      simpa [pow_succ, mul_assoc] using this
    rcases ht.unique (v * v) (J.mul_mem hvJ hvJ) hv22 with h | h
    · exfalso
      have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      rw [hv4] at this
      omega
    · exact h
  have hvK' : v * v ∈ Subgroup.normalizer (K : Set G) := by simpa [pow_two] using hvK
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hH K hKc hKz
  have hzt : z * t = t * z := by
    rw [← hvv]
    calc z * (v * v) = (z * v) * v := by group
      _ = (v * z) * v := by rw [hvz]
      _ = v * (z * v) := by group
      _ = v * (v * z) := by rw [hvz]
      _ = (v * v) * z := by group
  have hzJ : z ∈ Subgroup.normalizer (J : Set G) :=
    prop370 p f G hnab hp2 hq K z hz hbelow J hJ t ht K hKc z hKz hne.symm hzt.symm htK
  have hnt := nontrivAction p f G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz
    hvK hv
  obtain ⟨κ, hκK, hκ2, hκn, hcomm⟩ := exists_kappa hp2 hq hz hKc hKz hv4 hvz hv hvK' hnt
  obtain ⟨hδ2, hnδ, hδvδ⟩ := kappa_delta_facts hz2 hvz hκ2 hκn hcomm
  set δ : G := κ * (v⁻¹ * κ * v) with hδ
  have hδt : t * δ = δ * t := by rw [← hvv]; exact hnδ
  have hδt' : δ * t * δ⁻¹ = t := by
    calc δ * t * δ⁻¹ = (t * δ) * δ⁻¹ := by rw [← hδt]
      _ = t := by group
  have hδJ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases ht.unique z h2 hz2 with h3 | h3
    · exact hKz.ne_one h3
    · exact hne h3.symm
  have hJm : IsClassicalMember p f J t := isClassicalMember_of_mem_conjClass hp2 hq hz hJ ht
  have hJK : J ∈ CoreAssembly.conjClass K := hJ
  have hznt : ¬ ∀ k ∈ J, ⁅z, k⁆ ∈ oddCoreOf J := fun hζ =>
    hv (mem_normalizer_of_trivial_action hp2 hq hz hJK ht hzt.symm hzJ hζ hvJ hv2 hvz)
  have hzI2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_sq_sq (by rw [hz2, one_mul])
  obtain ⟨RJ, hRJ2, hERJ, hRJJ⟩ := exists_sylow_normalized (J := J) (E := Subgroup.zpowers z) hzI2
    (Subgroup.zpowers_le.mpr hzJ)
  have hzRJ : z ∈ RJ := hERJ (Subgroup.mem_zpowers z)
  obtain ⟨j, hjJ, hj2, hjz⟩ :=
    exists_inverted_involution_member hp2 hJm hq hRJ2 hRJJ hzRJ hz2 hzJ hznt
  have hjz' : j⁻¹ * z * j = z * t := kappa_conj_eq hz2 ht2 hzt hj2 hjz
  have hjt : j * t = t * j := (ht.commute_of_mem hjJ.2).symm
  have hκt : t⁻¹ * κ * t = κ⁻¹ := by rw [← hvv]; exact hκn
  have hkz : κ * z = z * κ := (hKz.commute_of_mem hκK).symm
  have hkt : κ⁻¹ * t * κ = t * z := kappa_conj_eq ht2 hz2 hzt.symm hκ2 hκt
  obtain ⟨hxz, hxt⟩ := swap_element hz2 ht2 hzt hjt hjz' hkz hkt
  set x : G := j * κ * j with hx
  have hxtz : x * t * x⁻¹ = z := by rw [← hxz]; group
  have hxzt : x * z * x⁻¹ = t := by rw [← hxt]; group
  set J₂ : Subgroup G := conjSub x J with hJ₂
  set J₂' : Subgroup G := conjSub (x * δ) J with hJ₂'
  have hJ₂c : J₂ ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hJ _
  have hJ₂'c : J₂' ∈ CoreAssembly.conjClass K := conjSub_mem_conjClass hJ _
  have hJ₂z : IsUniqueInvolution J₂ z := by
    have := ht.conj x
    rwa [hxtz] at this
  have hJ₂'z : IsUniqueInvolution J₂' z := by
    have := ht.conj (x * δ)
    have e : (x * δ) * t * (x * δ)⁻¹ = z := by
      calc (x * δ) * t * (x * δ)⁻¹ = x * (δ * t * δ⁻¹) * x⁻¹ := by group
        _ = x * t * x⁻¹ := by rw [hδt']
        _ = z := hxtz
    rwa [e] at this
  have hJ₂ne : J₂ ≠ J₂' := by
    intro h
    apply hδJ
    have := congrArg (conjSub x⁻¹) h
    rwa [hJ₂, hJ₂', ← conjSub_mul, ← conjSub_mul, inv_mul_cancel, conjSub_one,
      show x⁻¹ * (x * δ) = δ by group] at this
  have htM : t ∈ J₂ ⊔ J₂' := by
    have e1 : x * v⁻¹ * x⁻¹ ∈ J₂ := conj_mem_conjSub (J.inv_mem hvJ)
    have e2 : (x * δ) * v * (x * δ)⁻¹ ∈ J₂' := conj_mem_conjSub hvJ
    have : t = (x * v⁻¹ * x⁻¹) * ((x * δ) * v * (x * δ)⁻¹) := by
      calc t = x * z * x⁻¹ := hxzt.symm
        _ = x * (v⁻¹ * (v * z)) * x⁻¹ := by group
        _ = x * (v⁻¹ * (δ * v * δ⁻¹)) * x⁻¹ := by rw [hδvδ]
        _ = (x * v⁻¹ * x⁻¹) * ((x * δ) * v * (x * δ)⁻¹) := by group
    rw [this]
    exact (J₂ ⊔ J₂').mul_mem (Subgroup.mem_sup_left e1) (Subgroup.mem_sup_right e2)
  have key : ∀ B : Subgroup G, B ∈ CoreAssembly.conjClass K → IsUniqueInvolution B z → K ≠ B →
      ∀ u ∈ K, ∀ w ∈ B, t = u * w → ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t := by
    intro B hBc hBz hKB u hu w hw htuw
    obtain ⟨hact, hg2⟩ := twin_product_action hp2 hq hz hKc hBc hKz hBz hKB ht2 hu hw htuw
    have hnc : ¬ ∀ y ∈ K, ⁅u, y⁆ ∈ oddCoreOf K := by
      intro hc
      apply hnt
      intro k hk
      rw [hvv]
      have e1 : ⁅t, k⁆ = (t * k * t⁻¹ * (u * k * u⁻¹)⁻¹) * ⁅u, k⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact (oddCoreOf K).mul_mem (hact k hk) (hc k hk)
    exact exists_fixed_order_four_of_inner hp2 hq hz hR2 hRK htR ht2 htK hu hact hg2 hnc
  by_cases hKJ₂ : K = J₂
  ·
    obtain ⟨hJ₂₁, hJ₂₂, -⟩ := twin_facts_general hq hp2 hz hJ₂c hJ₂'c hJ₂z hJ₂'z hJ₂ne
    have hset : ((J₂ ⊔ J₂' : Subgroup G) : Set G) = (J₂ : Set G) * (J₂' : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left J₂ J₂' hJ₂₁
    have htM' : t ∈ (J₂ : Set G) * (J₂' : Set G) := by
      rw [← hset]
      exact htM
    obtain ⟨u₁, hu₁, u₂, hu₂, htu⟩ := htM'
    have hKJ₂' : K ≠ J₂' := by
      rw [hKJ₂]
      exact hJ₂ne
    have hu₁K : u₁ ∈ K := by
      rw [hKJ₂]
      exact hu₁
    exact key J₂' hJ₂'c hJ₂'z hKJ₂' u₁ hu₁K u₂ hu₂ htu.symm
  · by_cases hKJ₂' : K = J₂'
    · obtain ⟨hJ₂₁, hJ₂₂, -⟩ := twin_facts_general hq hp2 hz hJ₂c hJ₂'c hJ₂z hJ₂'z hJ₂ne
      have hset : ((J₂' ⊔ J₂ : Subgroup G) : Set G) = (J₂' : Set G) * (J₂ : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left J₂' J₂ hJ₂₂
      have htM' : t ∈ (J₂' : Set G) * (J₂ : Set G) := by
        rw [← hset, sup_comm]
        exact htM
      obtain ⟨u₂, hu₂, u₁, hu₁, htu⟩ := htM'
      have hKJ₂'' : K ≠ J₂ := hKJ₂
      exact key J₂ hJ₂c hJ₂z hKJ₂'' u₂ (hKJ₂' ▸ hu₂) u₁ hu₁ htu.symm
    ·
      obtain ⟨hJ₂₁, hJ₂₂, -⟩ := twin_facts_general hq hp2 hz hJ₂c hJ₂'c hJ₂z hJ₂'z hJ₂ne
      have hset : ((J₂ ⊔ J₂' : Subgroup G) : Set G) = (J₂ : Set G) * (J₂' : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left J₂ J₂' hJ₂₁
      have htM' : t ∈ (J₂ : Set G) * (J₂' : Set G) := by
        rw [← hset]
        exact htM
      obtain ⟨u₁, hu₁, u₂, hu₂, htu⟩ := htM'
      exfalso
      apply hnt
      intro k hk
      rw [hvv, ← htu]
      exact commutator_mem_oddCoreOf_of_product hp2 hq hz hJ₂c hJ₂'c hKc hJ₂z hJ₂'z hKz
        (Ne.symm hKJ₂) (Ne.symm hKJ₂') hu₁ hu₂ k hk


end CFSG.ClassicalInvolution.Asc77.AscFusion
