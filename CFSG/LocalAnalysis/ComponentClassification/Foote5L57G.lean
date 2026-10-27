module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57F
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

abbrev liftCent5 (L Q : Subgroup G) (v : G) : Subgroup G :=
  L ⊓ centralizer ((Q ⊔ zpowers v : Subgroup G) : Set G)

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
  {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
  {Lin : Subgroup (MulAut 𝕊)}
include h

omit [Finite 𝕊] in
theorem exists_involution_lifts_a4 {v : G} (hvS : v ∈ S) (hvQ : ∀ q ∈ Q, q * v = v * q)
    {X : Subgroup 𝕊} (hXfix : ∀ x ∈ X, actG L ε v x = x) (φ : X ≃* alternatingGroup (Fin 4)) :
    ∃ c₀ ∈ liftCent5 L Q v, ∃ u₁ ∈ ⁅liftCent5 L Q v, liftCent5 L Q v⁆,
      ∃ u₂ ∈ ⁅liftCent5 L Q v, liftCent5 L Q v⁆,
      ∃ (hc₀ : c₀ ∈ L) (hu₁ : u₁ ∈ L) (hu₂ : u₂ ∈ L),
        u₁ * u₁ = 1 ∧ u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧
        psi L ε ⟨u₁, hu₁⟩ ≠ 1 ∧ psi L ε ⟨u₂, hu₂⟩ ≠ 1 ∧
        psi L ε ⟨u₁, hu₁⟩ ≠ psi L ε ⟨u₂, hu₂⟩ ∧
        psi L ε ⟨u₁, hu₁⟩ * psi L ε ⟨u₂, hu₂⟩ = psi L ε ⟨u₂, hu₂⟩ * psi L ε ⟨u₁, hu₁⟩ ∧
        psi L ε ⟨c₀, hc₀⟩ * psi L ε ⟨u₁, hu₁⟩ * (psi L ε ⟨c₀, hc₀⟩)⁻¹ = psi L ε ⟨u₂, hu₂⟩ ∧
        psi L ε ⟨c₀, hc₀⟩ * psi L ε ⟨u₂, hu₂⟩ * (psi L ε ⟨c₀, hc₀⟩)⁻¹ =
          psi L ε ⟨u₁, hu₁⟩ * psi L ε ⟨u₂, hu₂⟩ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcX, y, hyX, y', hy'X, a₁, a₂, e₁, e₂, h12, h22, hcm, h11, h21, hne, hc1, hc2⟩ :=
    exists_a4_data φ
  obtain ⟨c₀, hc₀L, hc₀C, hψc⟩ := h.exists_lift_of_fixed ε hvS hvQ (hXfix c hcX)
  obtain ⟨d, hdL, hdC, hψd⟩ := h.exists_lift_of_fixed ε hvS hvQ (hXfix y hyX)
  obtain ⟨d', hd'L, hd'C, hψd'⟩ := h.exists_lift_of_fixed ε hvS hvQ (hXfix y' hy'X)
  set K := liftCent5 L Q v with hK
  have hc₀ : c₀ ∈ K := mem_inf.mpr ⟨hc₀L, hc₀C⟩
  have hd : d ∈ K := mem_inf.mpr ⟨hdL, hdC⟩
  have hd' : d' ∈ K := mem_inf.mpr ⟨hd'L, hd'C⟩
  have hk₁ : c₀ * d * c₀⁻¹ * d⁻¹ ∈ ⁅K, K⁆ := by
    rw [← commutatorElement_def]
    exact commutator_mem_commutator hc₀ hd
  have hk₂ : c₀ * d' * c₀⁻¹ * d'⁻¹ ∈ ⁅K, K⁆ := by
    rw [← commutatorElement_def]
    exact commutator_mem_commutator hc₀ hd'
  have hk₁L : c₀ * d * c₀⁻¹ * d⁻¹ ∈ L :=
    mul_mem (mul_mem (mul_mem hc₀L hdL) (inv_mem hc₀L)) (inv_mem hdL)
  have hk₂L : c₀ * d' * c₀⁻¹ * d'⁻¹ ∈ L :=
    mul_mem (mul_mem (mul_mem hc₀L hd'L) (inv_mem hc₀L)) (inv_mem hd'L)
  have hψk₁ : psi L ε ⟨_, hk₁L⟩ = a₁ := by
    rw [e₁, show (⟨c₀ * d * c₀⁻¹ * d⁻¹, hk₁L⟩ : L) =
      ⟨c₀, hc₀L⟩ * ⟨d, hdL⟩ * ⟨c₀, hc₀L⟩⁻¹ * ⟨d, hdL⟩⁻¹ from rfl, map_mul, map_mul, map_mul,
      map_inv, map_inv, hψc, hψd]
  have hψk₂ : psi L ε ⟨_, hk₂L⟩ = a₂ := by
    rw [e₂, show (⟨c₀ * d' * c₀⁻¹ * d'⁻¹, hk₂L⟩ : L) =
      ⟨c₀, hc₀L⟩ * ⟨d', hd'L⟩ * ⟨c₀, hc₀L⟩⁻¹ * ⟨d', hd'L⟩⁻¹ from rfl, map_mul, map_mul, map_mul,
      map_inv, map_inv, hψc, hψd']
  obtain ⟨u₁, hu₁M, hu₁L, hψu₁, hu₁2, -, -⟩ := exists_involution_lift ε hk₁ hk₁L hψk₁ h12 h11
  have hNodd : ¬ 2 ∣ Nat.card ↥(⁅K, K⁆ ⊓ oddCoreIn L) := fun h2 => by
    have h3 := Subgroup.card_dvd_of_le (inf_le_right : ⁅K, K⁆ ⊓ oddCoreIn L ≤ oddCoreIn L)
    have h4 := Nat.odd_iff.mp (odd_card_oddCoreIn L)
    have h5 := dvd_trans h2 h3
    omega
  have hPN : ∀ x ∈ zpowers u₁, ∀ n ∈ ⁅K, K⁆ ⊓ oddCoreIn L,
      x * n * x⁻¹ ∈ ⁅K, K⁆ ⊓ oddCoreIn L := by
    intro x hx n hn
    have hxM : x ∈ ⁅K, K⁆ := (zpowers_le.mpr hu₁M) hx
    have hxL : x ∈ L := (zpowers_le.mpr hu₁L) hx
    exact mem_inf.mpr ⟨mul_mem (mul_mem hxM (mem_inf.mp hn).1) (inv_mem hxM),
      conj_mem_oddCoreIn ε (le_normalizer hxL) (mem_inf.mp hn).2⟩
  have hy : ∀ x ∈ zpowers u₁, (c₀ * d' * c₀⁻¹ * d'⁻¹)⁻¹ * (x * (c₀ * d' * c₀⁻¹ * d'⁻¹) * x⁻¹) ∈
      ⁅K, K⁆ ⊓ oddCoreIn L := by
    intro x hx
    have hxM : x ∈ ⁅K, K⁆ := (zpowers_le.mpr hu₁M) hx
    have hxL : x ∈ L := (zpowers_le.mpr hu₁L) hx
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk₂) (mul_mem (mul_mem hxM hk₂) (inv_mem hxM)), ?_⟩
    have hxk : x * (c₀ * d' * c₀⁻¹ * d'⁻¹) * x⁻¹ ∈ L :=
      mul_mem (mul_mem hxL hk₂L) (inv_mem hxL)
    refine (psi_eq_iff ε ⟨_, hk₂L⟩ ⟨_, hxk⟩).mp ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    rw [show (⟨u₁ ^ i * (c₀ * d' * c₀⁻¹ * d'⁻¹) * (u₁ ^ i)⁻¹, hxk⟩ : L) =
      ⟨u₁, hu₁L⟩ ^ i * ⟨_, hk₂L⟩ * (⟨u₁, hu₁L⟩ ^ i)⁻¹ from rfl, map_mul, map_mul, map_inv,
      map_zpow, hψu₁, hψk₂, (Commute.zpow_left hcm i).eq, mul_inv_cancel_right]
  obtain ⟨k₂', hk₂'N, hk₂'c⟩ := exists_commute_of_coprime (P := zpowers u₁)
    (isPGroup_zpowers_of_pow_two (k := 1) (by rw [pow_one, sq]; exact hu₁2)) hNodd hPN hy
  have hk₂'M : k₂' ∈ ⁅K, K⁆ := by
    rw [show k₂' = (c₀ * d' * c₀⁻¹ * d'⁻¹) * ((c₀ * d' * c₀⁻¹ * d'⁻¹)⁻¹ * k₂') by group]
    exact mul_mem hk₂ (mem_inf.mp hk₂'N).1
  have hk₂'L : k₂' ∈ L := by
    rw [show k₂' = (c₀ * d' * c₀⁻¹ * d'⁻¹) * ((c₀ * d' * c₀⁻¹ * d'⁻¹)⁻¹ * k₂') by group]
    exact mul_mem hk₂L (mem_of_mem_oddCoreIn (mem_inf.mp hk₂'N).2)
  have hψk₂' : psi L ε ⟨k₂', hk₂'L⟩ = a₂ :=
    ((psi_eq_iff ε ⟨_, hk₂L⟩ ⟨k₂', hk₂'L⟩).mpr (mem_inf.mp hk₂'N).2).symm.trans hψk₂
  obtain ⟨u₂, hu₂M, hu₂L, hψu₂, hu₂2, -, m₂, rfl⟩ :=
    exists_involution_lift ε hk₂'M hk₂'L hψk₂' h22 h21
  have hcomm : u₁ * k₂' ^ m₂ = k₂' ^ m₂ * u₁ :=
    (Commute.pow_right (hk₂'c u₁ (mem_zpowers u₁)) m₂).eq
  refine ⟨c₀, hc₀, u₁, hu₁M, k₂' ^ m₂, hu₂M, hc₀L, hu₁L, hu₂L, hu₁2, hu₂2, hcomm, ?_⟩
  rw [hψu₁, hψu₂, hψc]
  exact ⟨h11, h21, hne, hcm, hc1, hc2⟩

end Sec5

end CFSG.ComponentClassification.Foote5
