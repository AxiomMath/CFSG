module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18C
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18D
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AR10E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_V_le_V1 (h : L41GPh15 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ≤ l41V1 t x₁ x₂ rho lam := by
  rw [h.rfacts.V_eq]
  exact sup_le (h.q1facts.R_le.trans le_sup_left) le_sup_right

theorem z18_cent_t_le (h : L41GPh15 t L S x₁ x₂ lam rho) {V₂ : Subgroup G} (hV₂ : IsPGroup 2 V₂)
    (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂) {c : G} (hc : c ∈ V₂) (hct : c * t = t * c) :
    c ∈ l41V1 t x₁ x₂ rho lam :=
  z18_V_le_V1 h (r10_cent_sylow h.toCtx0 hV₂ ((z18_V_le_V1 h).trans hV₁) hc hct)

theorem z18_cent_V2_Y (h : L41GPh17 t L S x₁ x₂ lam rho) {V₂ : Subgroup G} (hV₂ : IsPGroup 2 V₂)
    (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hN : V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G))
    (hC1 : ∀ v ∈ l41V1 t x₁ x₂ rho lam, (∀ y ∈ l41Y t x₁ x₂ rho, y * v = v * y) →
      v ∈ l41Q1 t x₁ x₂ rho) :
    V₂ ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) = l41Q1 t x₁ x₂ rho := by
  have htV₁ : t ∈ l41V1 t x₁ x₂ rho lam :=
    Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
  have htV₂ : t ∈ V₂ := hV₁ htV₁
  have htM : t ∈ l41M t x₁ x₂ rho :=
    Subgroup.le_normalizer (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
  have hQ1C : l41Q1 t x₁ x₂ rho ≤ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
    intro q hq
    have : q ∈ l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [h.centQ1]
      exact hq
    exact (Subgroup.mem_inf.mp this).2
  have hQ1V₂ : l41Q1 t x₁ x₂ rho ≤ V₂ := le_sup_left.trans hV₁
  refine z18_cent_eq hV₂ inf_le_left (le_inf hQ1V₂ hQ1C) htV₂ ?_
    (fun k hk => h.q1facts.normal_Q1.2 t htM k hk) ?_
  · intro d hd
    obtain ⟨hdV, hdC⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨V₂.mul_mem (V₂.mul_mem htV₂ hdV) (V₂.inv_mem htV₂),
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t⁻¹⁻¹ ∈ l41Y t x₁ x₂ rho :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer _).inv_mem (hN htV₂)) y).mp hy
    have hc := Subgroup.mem_centralizer_iff.mp hdC _ hy'
    rw [inv_inv] at hc
    calc y * (t * d * t⁻¹) = t * ((t⁻¹ * y * t) * d) * t⁻¹ := by group
      _ = t * (d * (t⁻¹ * y * t)) * t⁻¹ := by rw [hc]
      _ = (t * d * t⁻¹) * y := by group
  · intro z hz hzn hzt
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨k, hk, hzk⟩ := hzt
    exact hC1 z (z18_hcl h hV₁ (fun c hc hct => z18_cent_t_le h.toL41GPh15 hV₂ hV₁ hc hct) hzV hk
      hzk) fun y hy => (Subgroup.mem_centralizer_iff.mp hzC y hy)

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
