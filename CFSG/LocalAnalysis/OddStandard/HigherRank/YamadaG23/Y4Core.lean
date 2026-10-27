module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4CoreB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4CoreJ0
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4CoreP

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_core_false (c : Ctx4 s e) {x : G} (hx : x ∈ M2 s) (hxB : x ∉ s.fr.B)
    (hx2 : x * x = 1) (hxF : x ∉ normalizer (s.fr.F : Set G))
    (hcard : 8 ≤ Nat.card ↥(centEl s.fr.B x)) : False := by
  have hH : F33Hyp s e := c.toF33
  have hxC : x ∈ s.C₂ := y4_M2_le_C2 hH hx
  have hxN : x ∈ normalizer (s.fr.B : Set G) :=
    c.h33.1.2.2 (Subgroup.mem_sup_right hxC)
  have hxJ : ∀ j ∈ thompsonSubgroup s.fr.B, x * j * x⁻¹ ∈ thompsonSubgroup s.fr.B :=
    y5_J_conj s x hxN
  have hxV : ∀ v ∈ cen s.fr.B, x * v * x⁻¹ = v := fun v hv => y4_C2_cent_V c hxC hv
  obtain ⟨j₀, hj₀, hj₀V, hxα⟩ := y4_exists_j0 c hxC hxF
  obtain ⟨j₁, hj₁, hj₁V, hxj₁, hcov⟩ :=
    y4_core_prep (J := thompsonSubgroup s.fr.B) (V := cen s.fr.B) (B := s.fr.B)
      (α := s.fr.a₁ * s.fr.a₂) (x := x) (j₀ := j₀)
      (y5_V_le_J hH) (y5_J_le_B s) (y4_J_comm hH) (y4_V_mul_self hH)
      (y4_J_sq_mem_V hH) (y4_J_sq_one_mem_V hH) (y4_card_V hH) (y4_card_J hH)
      (y4_B_cases hH) hx2 hxJ hxV hj₀ hj₀V hxα hcard
  obtain ⟨k, hk⟩ := y52_exists_K hH
  exact y4_core_comp (J := thompsonSubgroup s.fr.B) (V := cen s.fr.B)
    (α := s.fr.a₁ * s.fr.a₂) (x := x) (k := k) (j₀ := j₀) (j₁ := j₁)
    (y5_V_le_J hH) (y4_J_comm hH) (y4_V_mul_self hH) (y4_J_sq_mem_V hH)
    (y4_J_sq_one_mem_V hH) (y4_alpha_sq hH) (y4_alpha_inv_J hH) hx2 hxJ hxV
    hj₀ hj₀V hxα hj₁ hj₁V hxj₁ hcov hk.cube (y5_J_conj s k hk.mem.2)
    (y4_conj_V hk.mem.2) (y4_fixJ hH hk) (y4_prod_cases c hk hx hxB)

end CFSG.OddStandard.HigherRank.YamadaG23
