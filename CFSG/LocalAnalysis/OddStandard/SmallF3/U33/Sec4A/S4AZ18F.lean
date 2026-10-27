module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AZ18B

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem z18_not_cent {Y : Subgroup G} {k : G} (h4 : Nat.card ↥(Y ⊓ centralizer ({k} : Set G)) = 4)
    (hY : Nat.card Y = 16) (hc : ∀ y ∈ Y, y * k = k * y) : False := by
  have : Y ⊓ centralizer ({k} : Set G) = Y :=
    inf_eq_left.mpr fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hc y hy)
  rw [this, hY] at h4
  omega


theorem z18_cent_V1_Y (h : L41GPh16 t L S x₁ x₂ lam rho) {v : G}
    (hv : v ∈ l41V1 t x₁ x₂ rho lam) (hc : ∀ y ∈ l41Y t x₁ x₂ rho, y * v = v * y) :
    v ∈ l41Q1 t x₁ x₂ rho := by
  have hKn : closure ({t, lam} : Set G) ≤
      normalizer ((l41Q1 t x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [Subgroup.closure_le]
    intro k hk
    have hkM : k ∈ l41M t x₁ x₂ rho :=
      z18_V1_le_M h.toL41GPh15 (Subgroup.mem_sup_right (Subgroup.subset_closure hk))
    exact mem_normalizer_of_conj_mem fun q hq => h.q1facts.normal_Q1.2 k hkM q hq
  have hv' : v ∈ ((l41Q1 t x₁ x₂ rho ⊔ closure ({t, lam} : Set G) : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKn] at hv'
  obtain ⟨q, hq, k, hk, rfl⟩ := Set.mem_mul.mp hv'
  have hqC : ∀ y ∈ l41Y t x₁ x₂ rho, y * q = q * y := by
    intro y hy
    have : q ∈ l41Q1 t x₁ x₂ rho ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) := by
      rw [h.centQ1]
      exact hq
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp this).2 y hy
  have hkC : ∀ y ∈ l41Y t x₁ x₂ rho, y * k = k * y := by
    intro y hy
    apply mul_left_cancel (a := q)
    calc q * (y * k) = (q * y) * k := (mul_assoc _ _ _).symm
      _ = (y * q) * k := by rw [hqC y hy]
      _ = y * (q * k) := mul_assoc _ _ _
      _ = (q * k) * y := hc y hy
      _ = q * (k * y) := mul_assoc _ _ _
  have hY16 := h.yfacts.Y_elem.2
  have htl : t * lam = lam * t := m13_t_comm_L h.toL41GPh5 (generators_mem_L h.toCtx0).2.2
  rcases (m11_mem_K_iff h.toL41GPh5).mp hk with rfl | rfl | rfl | rfl
  · simpa using hq
  · exfalso
    refine z18_not_cent (k := k) ?_ hY16 hkC
    have := h.yfacts.cent_Y_t
    have hc4 := n4_card_four h.toCtx0
    rw [← this] at hc4
    exact hc4
  · exact (z18_not_cent h.yfacts.card_cent_Y_lam hY16 hkC).elim
  · refine (z18_not_cent (k := t * lam) ?_ hY16 hkC).elim
    rw [htl]
    exact h.yfacts.card_cent_Y_lamt

theorem z18_cent_V2_Y' (h : L41GPh17 t L S x₁ x₂ lam rho) {V₂ : Subgroup G} (hV₂ : IsPGroup 2 V₂)
    (hV₁ : l41V1 t x₁ x₂ rho lam ≤ V₂)
    (hN : V₂ ≤ normalizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G)) :
    V₂ ⊓ centralizer ((l41Y t x₁ x₂ rho : Subgroup G) : Set G) = l41Q1 t x₁ x₂ rho :=
  z18_cent_V2_Y h hV₂ hV₁ hN fun _ hv hc => z18_cent_V1_Y h.toL41GPh16 hv hc

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
