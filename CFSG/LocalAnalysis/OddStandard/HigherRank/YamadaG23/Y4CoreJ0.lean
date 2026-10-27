module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4JStr
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4T2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54K1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_exists_j0 (c : Ctx4 s e) {x : G} (hx : x ∈ s.C₂)
    (hxF : x ∉ normalizer (s.fr.F : Set G)) :
    ∃ j₀ ∈ thompsonSubgroup s.fr.B, j₀ ∉ cen s.fr.B ∧
      x * (s.fr.a₁ * s.fr.a₂) * x⁻¹ = j₀ * (s.fr.a₁ * s.fr.a₂) := by
  obtain hH : F33Hyp s e := c.toF33
  have hxB : x ∈ normalizer (s.fr.B : Set G) :=
    y4_mem_normalizer_of_conj_mem (y54_C2_norm_B hH x hx)
  have hαB : x * (s.fr.a₁ * s.fr.a₂) * x⁻¹ ∈ s.fr.B :=
    y54_C2_norm_B hH x hx _ (y5_a12_mem_B hH)
  rcases y4_B_cases hH _ hαB with hin | ⟨j, hj, hjα⟩
  · exfalso
    have hinv : x⁻¹ ∈ normalizer (s.fr.B : Set G) :=
      (normalizer (s.fr.B : Set G)).inv_mem hxB
    have hαJ : s.fr.a₁ * s.fr.a₂ ∈ thompsonSubgroup s.fr.B := by
      have h := y5_J_conj s x⁻¹ hinv (x * (s.fr.a₁ * s.fr.a₂) * x⁻¹) hin
      rwa [show x⁻¹ * (x * (s.fr.a₁ * s.fr.a₂) * x⁻¹) * (x⁻¹)⁻¹ =
        s.fr.a₁ * s.fr.a₂ by group] at h
    exact y5_a12_not_mem_J hH hαJ
  · refine ⟨j, hj, ?_, hjα⟩
    intro hjV
    refine hxF (y4_mem_normalizer_of_conj_mem (x := x) ?_)
    have hVF : cen s.fr.B ≤ s.fr.F := y54_V_le_F hH
    intro u hu
    rw [SFrame.F] at hu ⊢
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · rw [hjα]
          exact s.fr.F.mul_mem (hVF hjV) (Subgroup.subset_closure (by simp))
        · rw [y4_C2_cent_V c hx (y4_w_mem_V c)]
          exact Subgroup.subset_closure (by simp)
        · rw [y4_C2_cent_V c hx (y4_z_mem_V c)]
          exact Subgroup.subset_closure (by simp)
    | one => simp
    | mul a b _ _ ha hb =>
        rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group]
        exact s.fr.F.mul_mem ha hb
    | inv a _ ha =>
        rw [show x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ by group]
        exact s.fr.F.inv_mem ha

end CFSG.OddStandard.HigherRank.YamadaG23
