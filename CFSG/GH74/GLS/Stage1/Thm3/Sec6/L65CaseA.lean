module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65P1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Base

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem not_isConj_of_order_eight (h : Std4 G z S K₁ K₂) (hII : II4_4_4_center) (hrec : Bg.B_reciprocity)
    (h7 : IsDoubleCoverOfAlt (Hat K₁) 7) {a u : G} (haK : a ∈ K₁) (ha8 : orderOf a = 8) (huz : u ≠ z) (huC : u ∈ centralizer ({z} : Set G)) (huN : u ∈ normalizer (K₁ : Set G))
    (hau : a * u = u * a) : ¬ IsConj z u := by
  intro hconj
  have hM := m4_of_std hII h
  obtain ⟨g, hg⟩ := M.exists_conj_inv hconj
  have hz2 : z * z = 1 := hM.z_sq
  have hz4 : a ^ 4 = z := pow_four_eq_z_of_order_eight h hII haK ha8
  have haP : IsPGroup 2 ↥(zpowers a) := IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, ha8]; norm_num)
  have haz : a ∉ zpowers z := by
    intro hmem
    have := orderOf_dvd_of_mem_zpowers hmem
    rw [ha8, h.orderOf_z] at this
    omega
  have hN := rec1b_of_std hII hrec h u g hg huC K₁ K₁ (Or.inl rfl) (Or.inl rfl) huN a haK haP haz hau
  have hy : g * a * g⁻¹ ∈ normalizer (K₁ : Set G) := M.mem_normalizer_cj hN
  have hzu : z = g * u * g⁻¹ := by
    rw [← hg]; group
  have hy8 : (g * a * g⁻¹) ^ 8 = 1 := by
    rw [conj_pow, ← ha8, pow_orderOf_eq_one]; group
  have hy4 : (g * a * g⁻¹) ^ 4 = g * z * g⁻¹ := by
    rw [conj_pow, hz4]
  have hcS : (g * a * g⁻¹) ^ 4 ∈ cSec K₁ := pow_four_mem_cSec h7 hy hy8
  rw [hy4] at hcS
  have hF : InducesFAut (g * z * g⁻¹) K₁ :=
    inducesFAut_of_mem_cSec h.simple h.orderOf_z (h.comp_isPCompIn (Or.inl rfl))
      (h.comp_pRank (Or.inl rfl)) hcS
  have hzc : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := by
    have hcu : u * z = z * u := (M.centralizer_comm huC).symm ▸ rfl
    calc g * z * g⁻¹ * z = g * z * g⁻¹ * (g * u * g⁻¹) := by rw [← hzu]
      _ = g * (z * u) * g⁻¹ := by group
      _ = g * (u * z) * g⁻¹ := by rw [← hcu]
      _ = (g * u * g⁻¹) * (g * z * g⁻¹) := by group
      _ = z * (g * z * g⁻¹) := by rw [← hzu]
  have hz'C : g * z * g⁻¹ ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hzc
  have hz'conj : IsConj z (g * z * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have hz'sq : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hz'nZ : g * z * g⁻¹ ∉ M.ZsM (pPrimeCoreOf 2) (K₁ ⊔ K₂) := by
    intro hZ
    rcases hM.inv_ZsK hZ hz'sq with h1 | h1
    · exact hM.z_ne (by simpa using h1)
    · apply huz
      have : g * z = z * g := by
        calc g * z = g * z * g⁻¹ * g := by group
          _ = z * g := by rw [h1]
      calc u = g⁻¹ * z * g := hg.symm
        _ = g⁻¹ * (z * g) := by group
        _ = g⁻¹ * (g * z) := by rw [this]
        _ = z := by group
  exact hM.he (g * z * g⁻¹) hz'C hz'conj hz'nZ K₁ (Or.inl rfl) hF

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
