module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16I
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16J
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16L
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC16N

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem c16_mem_M_of (h : L41GPh15 t L S x₁ x₂ lam rho) {n : G}
    (hnR : n ∈ normalizer ((l41R t x₁ x₂ rho : Subgroup G) : Set G))
    (hnt : n * t * n⁻¹ * t⁻¹ ∈ l41R t x₁ x₂ rho) : n ∈ l41M t x₁ x₂ rho := by
  have hRF : l41R t x₁ x₂ rho ≤ l41F t x₁ x₂ rho := le_sup_left
  have hle : (l41F t x₁ x₂ rho).map (MulAut.conj n).toMonoidHom ≤ l41F t x₁ x₂ rho := by
    rw [Subgroup.map_le_iff_le_comap]
    intro f hf
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases m13_mem_F h.toL41GPh8 hf with hfR | ⟨k, hk, rfl⟩
    · exact hRF ((Subgroup.mem_normalizer_iff.mp hnR f).mp hfR)
    · have hnk : n * k * n⁻¹ ∈ l41R t x₁ x₂ rho :=
        (Subgroup.mem_normalizer_iff.mp hnR k).mp hk
      have heq : n * (t * k) * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t * (n * k * n⁻¹) := by group
      rw [heq]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRF hnt) (q14_t_mem_F t x₁ x₂ rho))
        (hRF hnk)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge)

theorem c16_false (h : L41GPh15 t L S x₁ x₂ lam rho)
    (hRQ : l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41R t x₁ x₂ rho) : False := by
  obtain ⟨z, u, fz, fu, H⟩ := c16_exists_ab h
  have hcQY := c16_cent_Q_Y h hRQ
  have hR : ∀ r, r ∈ l41R t x₁ x₂ rho ↔
      r ∈ l41Q t x₁ x₂ rho ∧ ∀ f ∈ l41Y t x₁ x₂ rho, r * f = f * r := by
    intro r
    rw [← hcQY, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hQ, hc⟩
      exact ⟨hQ, fun f hf => (hc f hf).symm⟩
    · rintro ⟨hQ, hc⟩
      exact ⟨hQ, fun f hf => (hc f hf).symm⟩
  have hR3 : ¬ 3 ∣ Nat.card (l41R t x₁ x₂ rho) := by
    rw [h.rfacts.card_R]
    norm_num
  have hQt : ∀ x ∈ l41Q t x₁ x₂ rho, rho * x * rho⁻¹ = x → x = 1 ∨ x = t := by
    intro x hxQ hfix
    have hxc : x ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact n4_comm_of_conj_eq hfix
    have hxt : x ∈ zpowers t := by
      rw [← q14_cent_Q_rho h.toL41GPh10]
      exact Subgroup.mem_inf.mpr ⟨hxQ, hxc⟩
    exact pt_eq_one_or_of_mem_zpowers h.hyp.ord_t hxt
  have htQ : t ∈ l41Q t x₁ x₂ rho := q14_t_mem_Q h.toL41GPh8
  have hQm := c16_beta_qm H hR hR3 hQt
  have hQc : Nat.card (l41Q t x₁ x₂ rho) = 2 ^ 9 := by
    rw [q14_card_Q h.toL41GPh10]
    norm_num
  have hsurj := c16_beta_surj H hR hQc h.rfacts.card_R hQm
  obtain ⟨n, hnV1, hnP, -, hnY, hnK, hnR, hnQ⟩ := c16_exists_n h hRQ
  have hβ := c16_beta_conj_t H hQm hsurj htQ hnY hnK hnQ
  have hntQ : n * t * n⁻¹ ∈ l41Q t x₁ x₂ rho := (Subgroup.mem_normalizer_iff.mp hnQ t).mp htQ
  have htinvQ : t⁻¹ ∈ l41Q t x₁ x₂ rho := (l41Q t x₁ x₂ rho).inv_mem htQ
  have hprodQ : n * t * n⁻¹ * t⁻¹ ∈ l41Q t x₁ x₂ rho := Subgroup.mul_mem _ hntQ htinvQ
  have hzero : c16Beta z u fz fu (n * t * n⁻¹ * t⁻¹) = 0 := by
    rw [c16_beta_add H hntQ htinvQ, hβ, c16_beta_inv H htQ, c16_beta_t H]
    exact c16_add_self _
  have hnt : n * t * n⁻¹ * t⁻¹ ∈ l41R t x₁ x₂ rho :=
    (hR _).mpr ⟨hprodQ, (c16_beta_eq_zero_iff H hprodQ).mp hzero⟩
  have hnM : n ∈ l41M t x₁ x₂ rho := c16_mem_M_of h hnR hnt
  have hsup : l41V1 t x₁ x₂ rho lam ⊔ zpowers n ≤ l41M t x₁ x₂ rho :=
    sup_le (z18_V1_le_M h) (Subgroup.zpowers_le.mpr hnM)
  have heq := eq_of_isPGroup_of_odd_relIndex le_sup_left hsup hnP h.q1facts.V1_sylow
  have hnmem : n ∈ l41V1 t x₁ x₂ rho lam ⊔ zpowers n :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
  rw [heq] at hnmem
  exact hnV1 hnmem

theorem l41_centq1_of (h : L41GPh15 t L S x₁ x₂ lam rho) :
    l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) =
      l41Q1 t x₁ x₂ rho := by
  rcases h.q1facts.cent_Q1_Y with hR | hQ1
  · exact (c16_false h hR).elim
  · exact hQ1

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

namespace CFSG.OddStandard.SmallF3.HarrisU33

theorem l41_centq1_holds : L41CentQ1Stmt :=
  fun h => S4A.l41_centq1_of h.toG

end CFSG.OddStandard.SmallF3.HarrisU33
