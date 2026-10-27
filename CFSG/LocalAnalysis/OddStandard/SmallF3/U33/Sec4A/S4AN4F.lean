module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AN4E

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem n4_V_decomp (h : L41GPh1 t L S x₁ x₂ lam rho) {v : G} (hv : v ∈ l41V S t x₁ x₂) :
    ∃ c ∈ l41O2 t x₁ x₂, ∃ s ∈ S, v = c * s := by
  have hv' : v ∈ ((l41O2 t x₁ x₂ ⊔ S : Subgroup G) : Set G) := hv
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (n4_S_le_normalizer_O2 h)] at hv'
  obtain ⟨c, hc, s, hs, rfl⟩ := Set.mem_mul.mp hv'
  exact ⟨c, hc, s, hs, rfl⟩

theorem n4_O2_cent_t (h : L41GPh3 t L S x₁ x₂ lam rho) {c : G} (hc : c ∈ l41O2 t x₁ x₂)
    (hct : c * t * c⁻¹ = t) : c ∈ ctxW t x₁ x₂ := by
  rw [← h.basic.cent_A]
  refine (n4_fix_iff h c).mp fun x hx => ?_
  obtain ⟨f, hf, rfl⟩ := n4_mem_smul_iff.mp hx
  calc c * (t * f) * c⁻¹ = (c * t * c⁻¹) * (c * f * c⁻¹) := by group
    _ = t * f := by rw [hct, n4_O2_fix h hc hf]

theorem n4_cent_V_t (h : L41GPh3 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ invCent t = S := by
  apply le_antisymm
  · intro v hv
    obtain ⟨hvV, hvt⟩ := Subgroup.mem_inf.mp hv
    obtain ⟨c, hc, s, hs, rfl⟩ := n4_V_decomp h.toL41GPh1 hvV
    have hct : c ∈ invCent t := by
      have := Subgroup.mul_mem _ hvt (Subgroup.inv_mem _ (h.le_invCent hs))
      simpa using this
    have hcW : c ∈ ctxW t x₁ x₂ :=
      n4_O2_cent_t h hc (n4_conj_eq_of_comm (mem_invCent_iff.mp hct).symm)
    exact Subgroup.mul_mem _ (h.basic.normal_W.1 hcW) hs
  · exact le_inf le_sup_right h.le_invCent

theorem n4_cent_V_A (h : L41GPh3 t L S x₁ x₂ lam rho) :
    l41V S t x₁ x₂ ⊓ centralizer ((ctxE t x₁ x₂ : Subgroup G) : Set G) = ctxW t x₁ x₂ := by
  rw [h.basic.cent_A]
  exact inf_eq_right.mpr (n4_W_le_V h.toL41GPh1)

theorem n4_V_sylow (h : L41GPh3 t L S x₁ x₂ lam rho) :
    ¬ 2 ∣ (l41V S t x₁ x₂).relIndex (l41N t x₁ x₂) := by
  have h1 := Subgroup.relIndex_mul_card (H := l41V S t x₁ x₂) (K := l41N t x₁ x₂)
  rw [inf_eq_left.mpr (n4_V_le_N h.toL41GPh1), n4_card_V h, n4_card_N h] at h1
  have hW : 0 < Nat.card ↥(ctxW t x₁ x₂) := Nat.card_pos
  generalize (l41V S t x₁ x₂).relIndex (l41N t x₁ x₂) = r at h1 ⊢
  generalize Nat.card ↥(ctxW t x₁ x₂) = w at h1 hW
  have h3 : (r * 8) * w = 24 * w := by
    rw [mul_assoc]
    exact h1
  have h4 := Nat.eq_of_mul_eq_mul_right hW h3
  omega

theorem n4_V_not_sylow (h : L41Ph3 t L S x₁ x₂ lam rho) : 2 ∣ (l41V S t x₁ x₂).index := by
  by_contra hodd
  have hcop : Nat.Coprime (2 ^ 4) (l41V S t x₁ x₂).index :=
    Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have hG := h.glob.dvd
  rw [← Subgroup.card_mul_index (l41V S t x₁ x₂), n4_card_V h.toG, pt_card_W h.toCtx0] at hG
  have hP : 0 < Nat.card ↥(twoCore t) := Nat.card_pos
  have hP4 := h.fusion.card_P_le
  generalize (l41V S t x₁ x₂).index = i at hcop hG
  generalize Nat.card ↥(twoCore t) = p at hG hP hP4
  have hG' : 2 ^ 7 * 2 ^ 4 ∣ 2 ^ 7 * (p * i) := by
    have e1 : 2 ^ 7 * 2 ^ 4 = 2 ^ 11 := by norm_num
    have e2 : 2 ^ 7 * (p * i) = 8 * (2 ^ 4 * p) * i := by ring
    rw [e1, e2]
    exact hG
  have h4 : 2 ^ 4 ∣ p * i := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hG'
  have h5 : 2 ^ 4 ∣ p := Nat.Coprime.dvd_of_dvd_mul_right hcop h4
  have h6 := Nat.le_of_dvd hP h5
  omega

theorem l41_normalizer0_of (h : L41GPh3 t L S x₁ x₂ lam rho) :
    L41Normalizer0 t S x₁ x₂ lam rho where
  normal_F2 := n4_normal_F2 h
  quot_N := n4_quot_N h
  orbit_t := n4_orbit_t h
  O2_eq := n4_O2_eq h
  card_O2 := n4_card_O2 h
  N_eq := n4_N_eq h
  V_le := n4_V_le_N h.toL41GPh1
  V_pGroup := n4_V_pGroup h.toL41GPh1
  V_sylow := n4_V_sylow h
  card_V := n4_card_V h
  cent_V_t := n4_cent_V_t h
  cent_V_A := n4_cent_V_A h
  quot_V := n4_quot_V h

theorem l41_normalizer_of (h : L41GPh3 t L S x₁ x₂ lam rho) (hV : 2 ∣ (l41V S t x₁ x₂).index) :
    L41Normalizer t S x₁ x₂ lam rho :=
  { l41_normalizer0_of h with V_not_sylow := hV }

end S4A

theorem l41_normalizer_holds : L41NormalizerStmt :=
  fun h => S4A.l41_normalizer_of h.toG (S4A.n4_V_not_sylow h)

end CFSG.OddStandard.SmallF3.HarrisU33
