module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open (StatedOmega StatedQuadPlus StatedQuadMinus)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv elementaryGroup_le_orthogonalGroup)
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
  (IsF2 statedOmega_quadPlus_eq_map_elementaryGroup statedOmega_quadMinus_eq_map_elementaryGroup
    eq_one_of_commute_elementaryGroup_of_isometry_plus
    eq_one_of_commute_elementaryGroup_of_isometry_minus)

theorem ivOmega_centre_bot_of_rigid {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Subgroup (GL ι K)} {E G : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    (hE : H.map (toLinEquiv ι K).toMonoidHom = E) (hEG : E ≤ G)
    (hrig : ∀ g ∈ G, (∀ x ∈ E, g * x = x * g) → g = 1) :
    Subgroup.center ↥H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hzE : toLinEquiv ι K (z : GL ι K) ∈ E := by
    rw [← hE]
    exact Subgroup.mem_map.2 ⟨(z : GL ι K), z.2, rfl⟩
  have h1 : toLinEquiv ι K (z : GL ι K) = 1 := by
    refine hrig _ (hEG hzE) fun x hx => ?_
    rw [← hE, Subgroup.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hgz : (g : GL ι K) * (z : GL ι K) = (z : GL ι K) * g := by
      simpa using congrArg Subtype.val (hz ⟨g, hg⟩)
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hgz]
  exact Subtype.ext ((toLinEquiv ι K).map_eq_one_iff.1 h1)

theorem ivOmega_centre_plus {K : Type} [Field K] [IsF2 K] {m : ℕ} (hm : 3 ≤ m) :
    Subgroup.center ↥(StatedOmega (StatedQuadPlus m K)) = ⊥ :=
  ivOmega_centre_bot_of_rigid
    (statedOmega_quadPlus_eq_map_elementaryGroup (K := K) hm)
    (elementaryGroup_le_orthogonalGroup _)
    fun g hg hc => eq_one_of_commute_elementaryGroup_of_isometry_plus (K := K) hm
      (LinearEquiv.refl K (Fin m ⊕ Fin m → K)) (by intro v; rfl) hg hc

theorem ivOmega_centre_minus {K : Type} [Field K] [IsF2 K] {m : ℕ} (hm : 3 ≤ m) :
    Subgroup.center ↥(StatedOmega (StatedQuadMinus m K 1 1)) = ⊥ :=
  ivOmega_centre_bot_of_rigid
    (statedOmega_quadMinus_eq_map_elementaryGroup (m := m) (K := K) (by omega))
    (elementaryGroup_le_orthogonalGroup _)
    fun g hg hc => eq_one_of_commute_elementaryGroup_of_isometry_minus (K := K) hm
      (LinearEquiv.refl K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K)) (by intro v; rfl) hg hc

theorem omegaCentreTrivial_holds : OmegaCentreTrivial := by
  unfold OmegaCentreTrivial
  intro n hn
  exact ⟨ivOmega_centre_plus (K := ZMod 2) (m := n + 1) (by omega),
    ivOmega_centre_minus (K := ZMod 2) (m := n + 1) (by omega)⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
