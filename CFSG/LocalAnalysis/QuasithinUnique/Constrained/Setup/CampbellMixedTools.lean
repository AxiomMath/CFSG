module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAut
public import CFSG.Quasithin.Background.BlueprintB2Defs

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2
open scoped LinearAlgebra.Projectivization

section Delta

variable {G : Type*} [Group G]

@[expose] def delta (S₀ : Subgroup G) (α : S₀ ≃* S₀) (h : G) (Y : Subgroup G) : Subgroup G :=
  aimg S₀ α (cj (aimg S₀ α.symm Y) h)

variable {S₀ Q₀ : Subgroup G} [Q₀.Normal] (hQ : Q₀ ≤ S₀) (α : S₀ ≃* S₀) (h : G)

include hQ

theorem cj_aimg_symm_le {Y : Subgroup G} (hY : aimg S₀ α.symm Y ≤ Q₀) :
    cj (aimg S₀ α.symm Y) h ≤ S₀ := by
  have := cj_mono (g := h) hY
  rw [cj_eq_self_of_normal (Y := Q₀)] at this
  exact this.trans hQ

theorem aimg_symm_delta {Y : Subgroup G} (hY : aimg S₀ α.symm Y ≤ Q₀) :
    aimg S₀ α.symm (delta S₀ α h Y) = cj (aimg S₀ α.symm Y) h :=
  aimg_symm_aimg (cj_aimg_symm_le hQ α h hY)

theorem aimg_symm_delta_le {Y : Subgroup G} (hY : aimg S₀ α.symm Y ≤ Q₀) :
    aimg S₀ α.symm (delta S₀ α h Y) ≤ Q₀ := by
  rw [aimg_symm_delta hQ α h hY]
  have := cj_mono (g := h) hY
  rwa [cj_eq_self_of_normal (Y := Q₀)] at this

theorem delta_commutator {Y Y' : Subgroup G} (hY : Y ≤ S₀) (hY' : Y' ≤ S₀)
    (hYQ : aimg S₀ α.symm Y ≤ Q₀) (hYQ' : aimg S₀ α.symm Y' ≤ Q₀) :
    delta S₀ α h ⁅Y, Y'⁆ = ⁅delta S₀ α h Y, delta S₀ α h Y'⁆ := by
  unfold delta
  rw [aimg_commutator hY hY', cj_commutator,
    aimg_commutator (cj_aimg_symm_le hQ α h hYQ) (cj_aimg_symm_le hQ α h hYQ')]

theorem delta_delta {Y : Subgroup G} (hY : Y ≤ S₀) (hYQ : aimg S₀ α.symm Y ≤ Q₀)
    (hh : h * h = 1) : delta S₀ α h (delta S₀ α h Y) = Y := by
  have h1 := aimg_symm_delta hQ α h hYQ
  unfold delta at h1 ⊢
  rw [h1, cj_cj, hh, cj_one, aimg_aimg_symm hY]

omit hQ in
theorem delta_mono {Y Y' : Subgroup G} (hYY : Y ≤ Y') :
    delta S₀ α h Y ≤ delta S₀ α h Y' :=
  aimg_mono (cj_mono (aimg_mono hYY))

omit hQ in
theorem delta_bot : delta S₀ α h ⊥ = ⊥ := by
  unfold delta; rw [aimg_bot, cj_bot, aimg_bot]

end Delta

end CFSG.QuasithinUnique.Setup.Campbell
