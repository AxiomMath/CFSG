module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16M
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

private theorem c16_exists_mem_normalizer_not_mem {U P : Subgroup G} (hP : IsPGroup 2 P)
    (hUP : U < P) : ∃ w ∈ P, w ∈ normalizer (U : Set G) ∧ w ∉ U := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : U.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact absurd (Subgroup.subgroupOf_eq_top.mp h) (not_le_of_gt hUP)
  obtain ⟨w, hw, hwU⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨w, w.2, ?_, fun h => hwU (Subgroup.mem_subgroupOf.mpr h)⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hw ⟨g, hUP.le hg⟩).mp
      (Subgroup.mem_subgroupOf.mpr hg))
  · intro hg
    have hgP : g ∈ P := by
      rw [show g = (w : G)⁻¹ * ((w : G) * g * (w : G)⁻¹) * w by group]
      exact mul_mem (mul_mem (inv_mem w.2) (hUP.le hg)) w.2
    exact Subgroup.mem_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp hw ⟨g, hgP⟩).mpr
      (Subgroup.mem_subgroupOf.mpr hg))

theorem c16_exists_n (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho) :
    ∃ n : G, n ∉ l41V1 t x₁ x₂ rho lam ∧ IsPGroup 2 ↥(l41V1 t x₁ x₂ rho lam ⊔ zpowers n) ∧
      n ∈ normalizer ((l41V1 t x₁ x₂ rho lam : Subgroup G) : Set G) ∧
      n ∈ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) ∧
      n ∈ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) ∧
      n ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) ∧
      n ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) := by
  obtain ⟨V₂, hV₂, hV₁, hN, hodd⟩ := z18_exists_V2 h
  have hne : l41V1 t x₁ x₂ rho lam ≠ V₂ := by
    intro heq
    have h2 := h.q1facts.V1_not_sylow
    rw [heq] at h2
    exact hodd h2
  obtain ⟨n, hnV₂, hnV₁N, hnV₁⟩ :=
    c16_exists_mem_normalizer_not_mem hV₂ (lt_of_le_of_ne hV₁ hne)
  have hRfwd : ∀ m ∈ V₂, ∀ r ∈ l41R t x₁ x₂ rho, m * r * m⁻¹ ∈ l41R t x₁ x₂ rho :=
    fun m hm r hr => c16_normal_R_V2 h hRQ hV₂ hV₁ hN m hm r hr
  have hKfwd : ∀ m ∈ V₂, ∀ k ∈ fourGrp x₁ x₂, m * k * m⁻¹ ∈ fourGrp x₁ x₂ := by
    intro m hm k hk
    obtain ⟨r, hr, rfl⟩ := (c16_mem_K_iff h).mp hk
    refine (c16_mem_K_iff h).mpr ⟨m * r * m⁻¹, hRfwd m hm r hr, ?_⟩
    group
  have hQV₁ : l41Q t x₁ x₂ rho ≤ l41V1 t x₁ x₂ rho lam := by
    rw [q15_V1_eq h.q1facts.Q_eq]
    exact le_sup_left
  have hQfwd : ∀ m ∈ V₂, m ∈ normalizer ((l41V1 t x₁ x₂ rho lam : Subgroup G) : Set G) →
      ∀ q ∈ l41Q t x₁ x₂ rho, m * q * m⁻¹ ∈ l41Q t x₁ x₂ rho := by
    intro m hm hmN q hq
    have hmqV : m * q * m⁻¹ ∈ l41V1 t x₁ x₂ rho lam :=
      (Subgroup.mem_normalizer_iff.mp hmN q).mp (hQV₁ hq)
    refine c16_V1_cent_K h hmqV ?_
    intro k hk
    have hk' : m⁻¹ * k * m⁻¹⁻¹ ∈ fourGrp x₁ x₂ := hKfwd m⁻¹ (V₂.inv_mem hm) k hk
    have hc := c16_Q_cent_K h hq hk'
    calc m * q * m⁻¹ * k = m * (q * (m⁻¹ * k * m⁻¹⁻¹)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * k * m⁻¹⁻¹) * q) * m⁻¹ := by rw [hc]
      _ = k * (m * q * m⁻¹) := by group
  have hnR : n ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨hRfwd n hnV₂ r, fun hr => ?_⟩
    have h1 := hRfwd n⁻¹ (V₂.inv_mem hnV₂) _ hr
    have e : n⁻¹ * (n * r * n⁻¹) * n⁻¹⁻¹ = r := by group
    rwa [e] at h1
  have hnK : n ∈ normalizer ((fourGrp x₁ x₂ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨hKfwd n hnV₂ k, fun hk => ?_⟩
    have h1 := hKfwd n⁻¹ (V₂.inv_mem hnV₂) _ hk
    have e : n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ = k := by group
    rwa [e] at h1
  have hnQ : n ∈ normalizer ((l41Q t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨hQfwd n hnV₂ hnV₁N q, fun hq => ?_⟩
    have hninvN : n⁻¹ ∈ normalizer ((l41V1 t x₁ x₂ rho lam : Subgroup G) : Set G) :=
      (normalizer _).inv_mem hnV₁N
    have h1 := hQfwd n⁻¹ (V₂.inv_mem hnV₂) hninvN _ hq
    have e : n⁻¹ * (n * q * n⁻¹) * n⁻¹⁻¹ = q := by group
    rwa [e] at h1
  exact ⟨n, hnV₁, hV₂.to_le (sup_le hV₁ (Subgroup.zpowers_le.mpr hnV₂)), hnV₁N, hN hnV₂, hnK,
    hnR, hnQ⟩

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
