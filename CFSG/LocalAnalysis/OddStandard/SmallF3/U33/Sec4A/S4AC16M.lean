module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem c16_cent_V2_Y (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho)
    {V₂ : Subgroup G} (hV₂ : IsPGroup 2 V₂) (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hN : V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) :
    V₂ ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) = l41R t x₁ x₂ rho := by
  let Y : Subgroup G := l41Y t x₁ x₂ rho
  let R : Subgroup G := l41R t x₁ x₂ rho
  let Q : Subgroup G := l41Q t x₁ x₂ rho
  let Q₁ : Subgroup G := l41Q1 t x₁ x₂ rho
  let V₁ : Subgroup G := l41V1 t x₁ x₂ rho lam
  have hRQ' : Q₁ ⊓ centralizer ((Y : Subgroup G) : Set G) = R := hRQ
  have htV₁ : t ∈ V₁ := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htV₂ : t ∈ V₂ := hV₁ htV₁
  have hQV₁ : Q ≤ V₁ := by
    change Q ≤ l41V1 t x₁ x₂ rho lam
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact le_sup_left
  have hRC : R ≤ centralizer ((Y : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact m13_comm_R h.toL41GPh10 (m13_Y_le_R t x₁ x₂ rho hy) hr
  have hRD : R ≤ V₂ ⊓ centralizer ((Y : Subgroup G) : Set G) :=
    le_inf ((h.q1facts.R_le.trans (q15_Q1_le_Q h.toL41GPh8)).trans (hQV₁.trans hV₁)) hRC
  have htD : ∀ d ∈ V₂ ⊓ centralizer ((Y : Subgroup G) : Set G),
      t * d * t⁻¹ ∈ V₂ ⊓ centralizer ((Y : Subgroup G) : Set G) := by
    intro d hd
    obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨V₂.mul_mem (V₂.mul_mem htV₂ hdV) (V₂.inv_mem htV₂), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : t⁻¹ * y * t⁻¹⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer (Y : Set G)).inv_mem (hN htV₂)) y).mp hy
    have hc := Subgroup.mem_centralizer_iff.mp hdC _ hy'
    rw [inv_inv] at hc
    calc y * (t * d * t⁻¹) = t * ((t⁻¹ * y * t) * d) * t⁻¹ := by group
      _ = t * (d * (t⁻¹ * y * t)) * t⁻¹ := by rw [hc]
      _ = (t * d * t⁻¹) * y := by group
  have htK : ∀ k ∈ R, t * k * t⁻¹ ∈ R := fun k hk => m13_t_conj_R h.toL41GPh8 hk
  have hcl : ∀ z ∈ V₂ ⊓ centralizer ((Y : Subgroup G) : Set G),
      (∀ k ∈ R, z * k * z⁻¹ ∈ R) →
      (∃ k ∈ R, t * z * t⁻¹ = z * k) → z ∈ R := by
    intro z hz _ hzt
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨k, hk, hzk⟩ := hzt
    have ht2 : t * t = 1 := t_mul_self h.hyp
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    have hk'R : t * k * t⁻¹ ∈ R := m13_t_conj_R h.toL41GPh8 hk
    have hconj : z⁻¹ * t * z = t * (t * k * t⁻¹) := by
      have h1 : t * z = z * k * t := by
        have := congrArg (· * t) hzk
        simpa [mul_assoc, htinv, ht2] using this
      calc z⁻¹ * t * z = z⁻¹ * (t * z) := by group
        _ = z⁻¹ * (z * k * t) := by rw [h1]
        _ = k * t := by group
        _ = t * (t * k * t⁻¹) := by
          rw [htinv]
          calc k * t = (t * t) * k * t := by rw [ht2, one_mul]
            _ = t * (t * k * t) := by group
    have hinv : (z⁻¹ * t * z) * (z⁻¹ * t * z) = 1 := by
      calc z⁻¹ * t * z * (z⁻¹ * t * z) = z⁻¹ * (t * t) * z := by group
        _ = 1 := by rw [ht2]; group
    have horb : z⁻¹ * t * z ∈ conjIn Q t := by
      rw [h.qfacts.orbit_t]
      exact ⟨n4_mem_smul_iff.mpr ⟨t * k * t⁻¹, hk'R, hconj⟩, hinv⟩
    obtain ⟨q, hqQ, hq⟩ := horb
    have hcV₂ : z * q ∈ V₂ := V₂.mul_mem hzV (hV₁ (hQV₁ hqQ))
    have hcomm : (z * q) * t = t * (z * q) := by
      calc z * q * t = z * (q * t * q⁻¹) * q := by group
        _ = z * (z⁻¹ * t * z) * q := by rw [hq]
        _ = t * (z * q) := by group
    have hcV₁ : z * q ∈ V₁ := z18_cent_t_le h hV₂ hV₁ hcV₂ hcomm
    have hzV₁ : z ∈ V₁ := by
      have hz' : z = (z * q) * q⁻¹ := by group
      rw [hz']
      exact V₁.mul_mem hcV₁ (V₁.inv_mem (hQV₁ hqQ))
    have hzV₁C : z ∈ V₁ ⊓ centralizer ((Y : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hzV₁, hzC⟩
    rw [c16_cent_V1_Y h hRQ'] at hzV₁C
    exact hzV₁C
  exact z18_cent_eq hV₂ inf_le_left hRD htV₂ htD htK hcl

theorem c16_normal_R_V2 (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho)
    {V₂ : Subgroup G} (hV₂ : IsPGroup 2 V₂) (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hN : V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) :
    ∀ v ∈ V₂, ∀ r ∈ l41R t x₁ x₂ rho, v * r * v⁻¹ ∈ l41R t x₁ x₂ rho := by
  let Y : Subgroup G := l41Y t x₁ x₂ rho
  let R : Subgroup G := l41R t x₁ x₂ rho
  have hcent : V₂ ⊓ centralizer ((Y : Subgroup G) : Set G) = R :=
    c16_cent_V2_Y h hRQ hV₂ hV₁ hN
  intro v hv r hr
  have hrD : r ∈ V₂ ⊓ centralizer ((Y : Subgroup G) : Set G) := by
    rw [hcent]
    exact hr
  obtain ⟨hrV, _⟩ := Subgroup.mem_inf.mp hrD
  change v * r * v⁻¹ ∈ R
  rw [← hcent]
  refine Subgroup.mem_inf.mpr ⟨V₂.mul_mem (V₂.mul_mem hv hrV) (V₂.inv_mem hv), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hy' : v⁻¹ * y * v ∈ Y :=
    (Subgroup.mem_normalizer_iff''.mp (hN hv) y).mp hy
  have hcomm : (v⁻¹ * y * v) * r = r * (v⁻¹ * y * v) :=
    m13_comm_R h.toL41GPh10 (m13_Y_le_R t x₁ x₂ rho hy') hr
  calc y * (v * r * v⁻¹) = v * ((v⁻¹ * y * v) * r) * v⁻¹ := by group
    _ = v * (r * (v⁻¹ * y * v)) * v⁻¹ := by rw [hcomm]
    _ = (v * r * v⁻¹) * y := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
