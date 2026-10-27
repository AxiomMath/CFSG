module

public import CFSG.ClassicalInvolution.Asc77.AscFusionR12
public import CFSG.ClassicalInvolution.Asc77.AscFusionR11

public section

namespace CFSG.ClassicalInvolution.Asc77.AscFusion

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscHypOmega
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime]


theorem nontrivAction (p f : ℕ) [Fact p.Prime] : NontrivAction p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv hT0
  classical
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
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
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  have hvK'' : conjSub v⁻¹ K ≠ K := fun h =>
    hv (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ :=
    exists_twin_sylow hp2 hq hz hKc hKz hv2 hvz hvK'' hvK'
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  have hT0' : ∀ x ∈ K, ⁅t, x⁆ ∈ oddCoreOf K := by
    intro x hx
    rw [← hvv]
    exact hT0 x hx
  obtain ⟨a₀, ha₀, ha₀2, hta₀⟩ := exists_sq_eq_z_comm_of_trivial hp2 hq hz hR2 hRK htR hT0'
  obtain ⟨k, hkK, hk2, hkact⟩ := exists_inner_order_four hp2 hq hz hJ ht hne hvJ hv2 hv4 hvz
    hvK hv hRcomm hRinv ha₀ ha₀2 hta₀
  refine not_forall_comm_of_sq_eq hp2 hq hz hkK hk2 ?_
  intro u hu
  have hA := hT0' u hu
  have hB := hkact u hu
  have e : ⁅u, k⁆ = (⁅t, u⁆)⁻¹ * (t * u * t⁻¹ * (k * u * k⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  have h1 : ⁅u, k⁆ ∈ oddCoreOf K := by
    rw [e]
    exact (oddCoreOf K).mul_mem ((oddCoreOf K).inv_mem hA) hB
  rw [← commutatorElement_inv]
  exact (oddCoreOf K).inv_mem h1

@[expose] def NoQuasidihedral (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → orderOf v = 4 → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∉ Subgroup.normalizer (K : Set G) →
            ∀ R : Subgroup G, IsPGroup 2 R → t ∈ R → IsSylow2In (R ⊓ K) K →
              ∃ a ∈ R ⊓ K, a * a = z ∧ t * a = a * t

theorem typeI_of_noQuasidihedral (p f : ℕ) [Fact p.Prime] (h : NoQuasidihedral p f) :
    TypeI p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4 hvz hvK hv
  classical
  have hKc : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKz : IsUniqueInvolution K z :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
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
  have hvz' : v⁻¹ * z = z * v⁻¹ := by
    calc v⁻¹ * z = v⁻¹ * z * v * v⁻¹ := by group
      _ = z * v⁻¹ := by
        have : v⁻¹ * z * v = z := by
          calc v⁻¹ * z * v = v⁻¹ * (z * v) := by rw [mul_assoc]
            _ = v⁻¹ * (v * z) := by rw [hvz]
            _ = z := by group
        rw [this]
  have hvK'' : conjSub v⁻¹ K ≠ K := fun h =>
    hv (by
      have := (Subgroup.normalizer (K : Set G)).inv_mem
        (AscHypOmega.mem_normalizer_of_conjSub_eq h)
      simpa using this)
  obtain ⟨R, hR2, hvR, -, hRK, -, hRcomm, hRinv⟩ :=
    exists_twin_sylow hp2 hq hz hKc hKz hv2 hvz hvK'' hvK'
  have htR : t ∈ R := hvv ▸ R.mul_mem hvR hvR
  obtain ⟨a₀, ha₀, ha₀2, hta₀⟩ := h G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 hv4
    hvz hvK hv R hR2 htR hRK
  obtain ⟨k, hkK, -, hkact⟩ := exists_inner_order_four hp2 hq hz hJ ht hne hvJ hv2 hv4 hvz hvK
    hv hRcomm hRinv ha₀ ha₀2 hta₀
  exact ⟨k, hkK, hkact⟩

theorem fusionCore_of_residuals'' (hC : Prop370 p f) (hQ : NoQuasidihedral p f)
    (h8 : BigOrder p f) : FusionCoreStmt p f :=
  fusionCore_of_residuals' hC (nontrivAction p f) (typeI_of_noQuasidihedral p f hQ) h8

@[expose] def BigOrderFC (p f : ℕ) [Fact p.Prime] : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) →
      ∀ J ∈ CoreAssembly.conjClass K, ∀ t : G, IsUniqueInvolution J t → t ≠ z →
        (∀ Q ∈ CoreAssembly.conjClass K, IsUniqueInvolution Q z →
          t ∈ Subgroup.normalizer (Q : Set G)) →
        ∀ v ∈ J, IsPGroup 2 (Subgroup.zpowers v) → 8 ≤ orderOf v → v * z = z * v →
          v ^ 2 ∈ Subgroup.normalizer (K : Set G) → v ∈ Subgroup.normalizer (K : Set G)

theorem bigOrder_of_bigOrderFC (p f : ℕ) [Fact p.Prime] (hB : BigOrderFC p f) :
    BigOrder p f := by
  intro G _ _ _ hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8 hvz hvK hv
  exact absurd (hB G hnab hp2 hq K z hz hbelow J hJ t ht hne hH v hvJ hv2 h8 hvz hvK) hv

theorem fusionCore_of_core_residuals (p f : ℕ) [Fact p.Prime] (hC : Prop370 p f)
    (hQ : NoQuasidihedral p f) (hB : BigOrderFC p f) : FusionCoreStmt p f :=
  fusionCore_of_residuals'' hC hQ (bigOrder_of_bigOrderFC p f hB)

end CFSG.ClassicalInvolution.Asc77.AscFusion
