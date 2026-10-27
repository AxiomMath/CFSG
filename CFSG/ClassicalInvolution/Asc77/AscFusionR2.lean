module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR1
public import CFSG.ClassicalInvolution.Asc77.AscFusionB

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]

section Elementary

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_sq_of_isUniqueInvolution {J : Subgroup G} {t v : G}
    (hJ : IsUniqueInvolution J t) (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v))
    (hv4 : 4 ≤ orderOf v) : t ∈ Subgroup.zpowers (v * v) := by
  obtain ⟨s, hs⟩ := hv2.exists_card_eq
  rw [Nat.card_zpowers] at hs
  have hs2 : 2 ≤ s := by
    by_contra hlt
    have : 2 ^ s ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  set w : G := v ^ (2 ^ (s - 1)) with hw
  have hwJ : w ∈ J := J.pow_mem hvJ _
  have hww : w * w = 1 := by
    rw [hw, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel (by omega), ← hs]
    exact pow_orderOf_eq_one v
  have hw1 : w ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hs] at this
    have h2 : 2 ^ s ≤ 2 ^ (s - 1) := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hwt : w = t := (hJ.unique w hwJ hww).resolve_left hw1
  rw [← hwt, hw]
  refine ⟨((2 ^ (s - 2) : ℕ) : ℤ), ?_⟩
  show (v * v) ^ ((2 ^ (s - 2) : ℕ) : ℤ) = v ^ 2 ^ (s - 1)
  rw [zpow_natCast, ← pow_two, ← pow_mul]
  congr 1
  have h1 : s - 1 = (s - 2) + 1 := by omega
  rw [h1, pow_succ']

end Elementary


@[expose] def Prop370 (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K₀ : Subgroup G) (z₀ : G), IsClassicalMember p f K₀ z₀ →
      CITBelowU p f (Nat.card G) →
      ∀ K ∈ CoreAssembly.conjClass K₀, ∀ z : G, IsUniqueInvolution K z →
        ∀ J ∈ CoreAssembly.conjClass K₀, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
          z * t = t * z → z ∈ Subgroup.normalizer (J : Set G) →
            t ∈ Subgroup.normalizer (K : Set G)

theorem fusion_chain_contradiction (hC : Prop370 p f)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (K₀ : Subgroup G) (z₀ : G)
    (h₀ : IsClassicalMember p f K₀ z₀) (hbelow : CITBelowU p f (Nat.card G))
    {K J : Subgroup G} (hK : K ∈ CoreAssembly.conjClass K₀) (hJ : J ∈ CoreAssembly.conjClass K₀)
    {z t : G} (hKz : IsUniqueInvolution K z) (hJt : IsUniqueInvolution J t) (hne : t ≠ z)
    {v : G} (hvJ : v ∈ J) (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hv4 : 4 ≤ orderOf v)
    (hvz : v * z = z * v) {κ : G} (hκK : κ ∈ K) (hκ2 : κ * κ = z)
    (hκn : (v * v)⁻¹ * κ * (v * v) = κ⁻¹)
    (hcomm : κ * (v⁻¹ * κ * v) = (v⁻¹ * κ * v) * κ)
    (hcl : ∃ I ∈ CoreAssembly.conjClass K₀, IsUniqueInvolution I (κ * (v⁻¹ * κ * v))) :
    False := by
  obtain ⟨I, hI, hIδ⟩ := hcl
  set κ' : G := v⁻¹ * κ * v with hκ'
  set δ : G := κ * κ' with hδ
  set n : G := v * v with hn
  have hz2 : z * z = 1 := hKz.sq
  have hzv : v⁻¹ * z * v = z := by
    calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
      _ = v⁻¹ * (v * z) := by rw [hvz]
      _ = z := by group
  have e1 : κ * v = v * κ' := by rw [hκ']; group
  have e2 : κ' * v = v * κ⁻¹ := by
    calc κ' * v = v⁻¹ * κ * (v * v) := by rw [hκ']; group
      _ = v * ((v * v)⁻¹ * κ * (v * v)) := by group
      _ = v * κ⁻¹ := by rw [hκn]
  have e3 : κ' * κ' = z := by
    calc κ' * κ' = v⁻¹ * (κ * κ) * v := by rw [hκ']; group
      _ = z := by rw [hκ2, hzv]
  have hδ2 : δ * δ = 1 := by
    calc δ * δ = κ * (κ' * κ) * κ' := by rw [hδ]; group
      _ = κ * (κ * κ') * κ' := by rw [← hcomm]
      _ = (κ * κ) * (κ' * κ') := by group
      _ = 1 := by rw [hκ2, e3, hz2]
  have hδi : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
  have hκ'n : n⁻¹ * κ' * n = κ'⁻¹ := by
    calc n⁻¹ * κ' * n = v⁻¹ * ((v * v)⁻¹ * κ * (v * v)) * v := by rw [hκ', hn]; group
      _ = κ'⁻¹ := by rw [hκn, hκ']; group
  have hnδ : n⁻¹ * δ * n = δ := by
    calc n⁻¹ * δ * n = (n⁻¹ * κ * n) * (n⁻¹ * κ' * n) := by rw [hδ]; group
      _ = κ⁻¹ * κ'⁻¹ := by rw [hκn, hκ'n]
      _ = (κ' * κ)⁻¹ := by group
      _ = δ⁻¹ := by rw [← hcomm]
      _ = δ := hδi
  have hnδ' : n * δ = δ * n := by
    have := congrArg (fun x => n * x) hnδ
    simpa [mul_assoc] using this.symm
  have hδt : t * δ = δ * t := by
    have htn : t ∈ Subgroup.zpowers n := mem_zpowers_sq_of_isUniqueInvolution hJt hvJ hv2 hv4
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp htn
    exact (Commute.zpow_left (show Commute n δ from hnδ') k).eq.symm.symm
  have hδvδ : δ * v * δ⁻¹ = v * z := by
    rw [hδi]
    calc δ * v * δ = κ * (κ' * v) * κ * κ' := by rw [hδ]; group
      _ = κ * (v * κ⁻¹) * κ * κ' := by rw [e2]
      _ = (κ * v) * κ' := by group
      _ = v * (κ' * κ') := by rw [e1]; group
      _ = v * z := by rw [e3]
  have hJδ : J ≠ conjSub δ J := by
    intro h
    have h1 : δ * v * δ⁻¹ ∈ conjSub δ J := conj_mem_conjSub hvJ
    rw [← h, hδvδ] at h1
    have h2 : z ∈ J := by
      have := J.mul_mem (J.inv_mem hvJ) h1
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hJt.unique z h2 hz2 with h3 | h3
    · exact hKz.ne_one h3
    · exact hne h3.symm
  have hcommv : v * (δ * v * δ⁻¹) = (δ * v * δ⁻¹) * v := by
    rw [hδvδ]
    calc v * (v * z) = (v * v) * z := by rw [mul_assoc]
      _ = v * (z * v) := by rw [mul_assoc, hvz]
      _ = v * z * v := by rw [mul_assoc]
  have hnz : n * z ∈ Subgroup.normalizer (I : Set G) := by
    have := diag_mem_normalizer_of_classical hp2 hq h₀ hJ hJt hδ2 hδt.symm hJδ hI hIδ hvJ hv2 hcommv
    rwa [hδvδ, ← mul_assoc] at this
  have hκ4 : orderOf κ = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 : κ ^ 2 ^ (1 + 1) = 1 := by
      calc κ ^ 2 ^ (1 + 1) = (κ * κ) * (κ * κ) := by simp [pow_succ, mul_assoc]
        _ = 1 := by rw [hκ2, hz2]
    have h2 : ¬ κ ^ 2 ^ 1 = 1 := by
      intro h
      apply hKz.ne_one
      rw [← hκ2, ← pow_two]
      simpa using h
    have := orderOf_eq_prime_pow h2 h1
    simpa using this
  have hκδ : κ * δ = δ * κ := by
    calc κ * δ = κ * (κ' * κ) := by rw [← hcomm]
      _ = (κ * κ') * κ := (mul_assoc κ κ' κ).symm
      _ = δ * κ := by rw [← hδ]
  have hz : z ∈ Subgroup.normalizer (I : Set G) := bstar hp2 hq h₀ hK hI hKz hIδ hκK hκ4 hκδ
  have hnI : n ∈ Subgroup.normalizer (I : Set G) := by
    have := (Subgroup.normalizer (I : Set G)).mul_mem hnz
      ((Subgroup.normalizer (I : Set G)).inv_mem hz)
    rwa [mul_assoc, mul_inv_cancel, mul_one] at this
  have htI : t ∈ Subgroup.normalizer (I : Set G) :=
    Subgroup.zpowers_le.mpr hnI (mem_zpowers_sq_of_isUniqueInvolution hJt hvJ hv2 hv4)
  have hδne : δ ≠ t := by
    intro h
    apply hJδ
    rw [h]
    exact (conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hJt.mem)).symm
  have hδN := hC G hnab hp2 hq K₀ z₀ h₀ hbelow J hJ t hJt I hI δ hIδ hδne hδt htI
  exact hJδ (conjSub_eq_of_mem_normalizer hδN).symm

end CFSG.ClassicalInvolution.Asc77.AscFusion
