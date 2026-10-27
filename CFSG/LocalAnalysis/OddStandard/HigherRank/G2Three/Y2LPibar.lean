module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LRho
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LCodes
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup Matrix

@[expose] def y2l_g3 : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide, by decide⟩

theorem y2l_g3_sq_ne : y2l_g3 * y2l_g3 ≠ 1 := fun h => by
  have h' := congrArg Units.val h
  rw [Units.val_mul, Units.val_one] at h'
  exact absurd h' (by decide)

variable {X : Type} [Group X] {M : Subgroup X} [M.Normal]
  (τ : M ≃* Multiplicative (Fin 3 → ZMod 4))

@[expose] noncomputable def y2l_pibar : X →* GL (Fin 3) (ZMod 2) :=
  (Matrix.GeneralLinearGroup.map (ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2))).comp
    (y2l_rho τ).toHomUnits

theorem y2l_coe_pibar (x : X) :
    (y2l_pibar τ x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = y2l_red (y2l_rho τ x) :=
  rfl

theorem y2l_pibar_eq_one_iff {x : X} : y2l_pibar τ x = 1 ↔ y2l_red (y2l_rho τ x) = 1 := by
  rw [← y2l_coe_pibar, Units.val_eq_one]

theorem y2l_ker_pibar (hC : centralizer (M : Set X) = M) (ψ : X →* GL (Fin 3) (ZMod 2))
    (hψ : Function.Surjective ψ) (hker : ψ.ker = M) : (y2l_pibar τ).ker = M := by
  refine le_antisymm ?_ fun m hm => MonoidHom.mem_ker.mpr ((y2l_pibar_eq_one_iff τ).mpr (by
    rw [y2l_rho_of_mem τ hm, map_one]))
  have hsq : ∀ x ∈ (y2l_pibar τ).ker, x * x ∈ M := fun x hx => by
    rw [← y2l_rho_eq_one_iff τ hC, map_mul]
    exact y2l_sq_of_red ((y2l_pibar_eq_one_iff τ).mp (MonoidHom.mem_ker.mp hx))
  haveI := CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh
  haveI := (y2l_pibar τ).normal_ker.map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((y2l_pibar τ).ker.map ψ) with h | h
  · rwa [Subgroup.map_eq_bot_iff, hker] at h
  · have hg : y2l_g3 ∈ (y2l_pibar τ).ker.map ψ := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨x, hx, hgx⟩ := Subgroup.mem_map.mp hg
    have h1 : ψ (x * x) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hsq x hx
    rw [map_mul, hgx] at h1
    exact absurd h1 y2l_g3_sq_ne

theorem y2l_pibar_surj [Finite X] (hker : (y2l_pibar τ).ker = M) (hidx : M.index = 168) :
    Function.Surjective (y2l_pibar τ) := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, hker, hidx, CFSG.ComponentClassification.GHarris.card_GL32_gh]

end CFSG.OddStandard.HigherRank.G2Three.Sec2
