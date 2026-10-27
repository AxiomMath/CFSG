module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem quaternionGroup_two_centralizer_pow :
    ∀ q q' : QuaternionGroup 2, q ^ 2 ≠ 1 → q' * q = q * q' →
      ∃ k : Fin 4, q' = q ^ (k : ℕ) := by
  decide +kernel

theorem y4_A_cent_b_mem_V (c : Ctx4 s e) {a : G} (ha : a ∈ s.fr.A)
    (h1 : ⁅a, s.fr.b₁⁆ = 1) (h2 : ⁅a, s.fr.b₂⁆ = 1) (hsq : a ^ 2 = 1) : a ∈ cen s.fr.B := by
  obtain ⟨⟨φ⟩, ⟨ψ⟩, hcomm, hsup, -, -⟩ := c.hLF.fact14.2.1
  have hnorm : ∀ x ∈ closure ({s.fr.a₁, s.fr.b₁} : Set G),
      ∀ y ∈ closure ({s.fr.a₂, s.fr.b₂} : Set G),
        x * y * x⁻¹ ∈ closure ({s.fr.a₂, s.fr.b₂} : Set G) := by
    intro x hx y hy
    rw [hcomm x hx y hy]
    simpa using hy
  have ha' : a ∈ closure ({s.fr.a₁, s.fr.b₁} : Set G) ⊔
      closure ({s.fr.a₂, s.fr.b₂} : Set G) := by
    have hsup' : closure ({s.fr.a₁, s.fr.b₁} : Set G) ⊔
        closure ({s.fr.a₂, s.fr.b₂} : Set G) = s.fr.A := hsup
    rw [hsup']
    exact ha
  obtain ⟨k1, hk1, k2, hk2, haeq⟩ := mem_sup_of_normalizes hnorm a ha'
  have hb1 : s.fr.b₁ ∈ closure ({s.fr.a₁, s.fr.b₁} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hb2 : s.fr.b₂ ∈ closure ({s.fr.a₂, s.fr.b₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hcomm_a1 : a * s.fr.b₁ = s.fr.b₁ * a :=
    commutatorElement_eq_one_iff_commute.mp h1
  have hka1 : (k1 * k2) * s.fr.b₁ * (k1 * k2)⁻¹ = s.fr.b₁ := by
    calc (k1 * k2) * s.fr.b₁ * (k1 * k2)⁻¹ = a * s.fr.b₁ * a⁻¹ := by rw [haeq]
      _ = s.fr.b₁ := by rw [hcomm_a1]; group
  have hk2b1' : k2 * s.fr.b₁ * k2⁻¹ = s.fr.b₁ := by
    rw [← hcomm s.fr.b₁ hb1 k2 hk2]; group
  have hk1b1' : k1 * s.fr.b₁ * k1⁻¹ = s.fr.b₁ := by
    calc k1 * s.fr.b₁ * k1⁻¹ = k1 * (k2 * s.fr.b₁ * k2⁻¹) * k1⁻¹ := by rw [hk2b1']
      _ = (k1 * k2) * s.fr.b₁ * (k1 * k2)⁻¹ := by group
      _ = s.fr.b₁ := hka1
  have hk1b1 : k1 * s.fr.b₁ = s.fr.b₁ * k1 := mul_inv_eq_iff_eq_mul.mp hk1b1'
  have hq1 : (φ ⟨s.fr.b₁, hb1⟩) ^ 2 ≠ 1 := by
    intro h
    have hφ : φ (⟨s.fr.b₁, hb1⟩ ^ 2) = φ 1 := by rw [map_pow, h, map_one]
    have h2' : (⟨s.fr.b₁, hb1⟩ : ↥(closure ({s.fr.a₁, s.fr.b₁} : Set G))) ^ 2 = 1 :=
      φ.injective hφ
    have h3 : s.fr.z = 1 := by
      have h3' : s.fr.b₁ ^ 2 = 1 := by
        have := congrArg Subtype.val h2'
        simpa [Subgroup.coe_pow] using this
      exact h3'
    exact y4_z_ne_one c h3
  have hc1 : φ ⟨k1, hk1⟩ * φ ⟨s.fr.b₁, hb1⟩ = φ ⟨s.fr.b₁, hb1⟩ * φ ⟨k1, hk1⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (by simpa using hk1b1))
  obtain ⟨m, hm⟩ :=
    quaternionGroup_two_centralizer_pow (φ ⟨s.fr.b₁, hb1⟩) (φ ⟨k1, hk1⟩) hq1 hc1
  have hk1pow : k1 = s.fr.b₁ ^ (m : ℕ) := by
    have hφ : φ ⟨k1, hk1⟩ = φ (⟨s.fr.b₁, hb1⟩ ^ (m : ℕ)) := by
      rw [map_pow]
      exact hm
    have := congrArg Subtype.val (φ.injective hφ)
    simpa [Subgroup.coe_pow] using this
  have hcomm_a2 : a * s.fr.b₂ = s.fr.b₂ * a :=
    commutatorElement_eq_one_iff_commute.mp h2
  have hka2 : (k1 * k2) * s.fr.b₂ * (k1 * k2)⁻¹ = s.fr.b₂ := by
    calc (k1 * k2) * s.fr.b₂ * (k1 * k2)⁻¹ = a * s.fr.b₂ * a⁻¹ := by rw [haeq]
      _ = s.fr.b₂ := by rw [hcomm_a2]; group
  have hk1b2' : k1 * s.fr.b₂ * k1⁻¹ = s.fr.b₂ := by
    rw [hcomm k1 hk1 s.fr.b₂ hb2]; group
  have hk2b2' : k2 * s.fr.b₂ * k2⁻¹ = s.fr.b₂ := by
    calc k2 * s.fr.b₂ * k2⁻¹
        = k1⁻¹ * ((k1 * k2) * s.fr.b₂ * (k1 * k2)⁻¹) * k1 := by group
      _ = k1⁻¹ * s.fr.b₂ * k1 := by rw [hka2]
      _ = s.fr.b₂ := by
        nth_rewrite 1 [← hk1b2']
        group
  have hk2b2 : k2 * s.fr.b₂ = s.fr.b₂ * k2 := mul_inv_eq_iff_eq_mul.mp hk2b2'
  have hq2 : (ψ ⟨s.fr.b₂, hb2⟩) ^ 2 ≠ 1 := by
    intro h
    have hφ : ψ (⟨s.fr.b₂, hb2⟩ ^ 2) = ψ 1 := by rw [map_pow, h, map_one]
    have h2' : (⟨s.fr.b₂, hb2⟩ : ↥(closure ({s.fr.a₂, s.fr.b₂} : Set G))) ^ 2 = 1 :=
      ψ.injective hφ
    have h3 : s.fr.b₂ ^ 2 = 1 := by
      have := congrArg Subtype.val h2'
      simpa [Subgroup.coe_pow] using this
    exact y4_z_ne_one c (by rw [← c.hRel.b2_sq]; exact h3)
  have hc2 : ψ ⟨k2, hk2⟩ * ψ ⟨s.fr.b₂, hb2⟩ = ψ ⟨s.fr.b₂, hb2⟩ * ψ ⟨k2, hk2⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (by simpa using hk2b2))
  obtain ⟨n, hn⟩ :=
    quaternionGroup_two_centralizer_pow (ψ ⟨s.fr.b₂, hb2⟩) (ψ ⟨k2, hk2⟩) hq2 hc2
  have hk2pow : k2 = s.fr.b₂ ^ (n : ℕ) := by
    have hφ : ψ ⟨k2, hk2⟩ = ψ (⟨s.fr.b₂, hb2⟩ ^ (n : ℕ)) := by
      rw [map_pow]
      exact hn
    have := congrArg Subtype.val (ψ.injective hφ)
    simpa [Subgroup.coe_pow] using this
  refine y4_sq_one_mem_V c ?_ hsq
  rw [haeq, hk1pow, hk2pow]
  exact Subgroup.mul_mem _
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) m)
    (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) n)

end CFSG.OddStandard.HigherRank.YamadaG23
