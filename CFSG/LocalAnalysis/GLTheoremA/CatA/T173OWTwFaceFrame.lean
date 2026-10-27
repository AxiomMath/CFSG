module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OWTwFaceRigid
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted

import CFSG.LieType.Chevalley.E6EvenRootTorus

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.HardMathSupport.Timmesfeld.CrossChar



theorem exists_rootDiagUnit_mul_of_mem_levi_sup_diag {F : Type} [Field F] (σ : F ≃+* F)
    (J : Set (Fin TwistTag.E6.foldedTag.rank)) {x : ModGL TwistTag.E6.tag F}
    (hx : x ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) :
    ∃ b : Fin TwistTag.E6.tag.rank → Fˣ,
      ∃ s ∈ subsystemGroup TwistTag.E6.tag F (TwistTag.E6.orbitUnion J),
        x = rootDiagUnit TwistTag.E6.tag b * s := by
  let SA := subsystemGroup TwistTag.E6.tag F (TwistTag.E6.orbitUnion J)
  let D := (rootDiagUnitHom TwistTag.E6.tag F).range
  have hDnorm : D ≤ Subgroup.normalizer (SA : Set (ModGL TwistTag.E6.tag F)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, rfl⟩ g hg
    exact RootTorus.conj_rootDiagUnit_mem_subsystemGroup (TwistTag.E6.orbitUnion J) b hg
  have hlev : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ≤ D ⊔ SA := by
    refine (inf_le_left : graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ≤
      parabolicLevi TwistTag.E6.tag F (TwistTag.E6.orbitUnion J)).trans ?_
    refine sup_le ?_ le_sup_right
    intro y hy
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
    exact Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨l, rfl⟩)
  have hdiag : twistedE6DiagGL F σ ≤ D ⊔ SA := by
    rintro _ ⟨u, rfl⟩
    exact Subgroup.mem_sup_left
      (MonoidHom.mem_range.2 ⟨compatDiag TwistTag.E6 σ.toRingHom u, rfl⟩)
  have hx' : x ∈ (↑(D ⊔ SA) : Set (ModGL TwistTag.E6.tag F)) := (sup_le hlev hdiag) hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D SA hDnorm] at hx'
  obtain ⟨d, hd, s, hs, rfl⟩ := hx'
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.1 hd
  exact ⟨b, s, hs, rfl⟩

theorem LeviFactor.exists_conj_of_mem_levi_sup_diag {F : Type} [Field F] (σ : F ≃+* F)
    {m : ℕ} {S T : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S) (hST : Disjoint S T)
    (h0 : ∀ i ∈ S, ∀ j ∈ T, TwistTag.E6.tag.cartan i j = 0)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : TwistTag.E6.orbitUnion J = S ∪ T)
    {x : ModGL TwistTag.E6.tag F}
    (hx : x ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ) :
    ∃ A : Matrix.GeneralLinearGroup (Fin m) F, ∀ g,
      x * f.ι g * x⁻¹ = f.ι (slConjugation m F A g) := by
  obtain ⟨b, s, hs, rfl⟩ := exists_rootDiagUnit_mul_of_mem_levi_sup_diag σ J hx
  rw [hJ] at hs
  exact LeviFactor.exists_conj f hST h0 b hs

theorem exists_rootDiagUnit_eq_of_mem_levi_sup_diag {F : Type} [Field F] (σ : F ≃+* F)
    {m₁ m₂ m₃ : ℕ} {S₁ S₂ S₃ : Set (Fin TwistTag.E6.tag.rank)}
    (f₁ : LeviFactor F m₁ S₁) (f₂ : LeviFactor F m₂ S₂) (f₃ : LeviFactor F m₃ S₃)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃)
    (c12 : ∀ i ∈ S₁, ∀ j ∈ S₂, TwistTag.E6.tag.cartan i j = 0)
    (c13 : ∀ i ∈ S₁, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    (c23 : ∀ i ∈ S₂, ∀ j ∈ S₃, TwistTag.E6.tag.cartan i j = 0)
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : TwistTag.E6.orbitUnion J = S₁ ∪ S₂ ∪ S₃)
    {x : ModGL TwistTag.E6.tag F}
    (hx : x ∈ graphFixedParabolicLevi TwistTag.E6 F σ.toRingHom J ⊔ twistedE6DiagGL F σ)
    (hc₁ : x ∈ Subgroup.centralizer (f₁.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hc₂ : x ∈ Subgroup.centralizer (f₂.ι.range : Set (ModGL TwistTag.E6.tag F)))
    (hc₃ : x ∈ Subgroup.centralizer (f₃.ι.range : Set (ModGL TwistTag.E6.tag F))) :
    ∃ b : Fin TwistTag.E6.tag.rank → Fˣ, x = rootDiagUnit TwistTag.E6.tag b ∧
      ∀ i ∈ S₁ ∪ S₂ ∪ S₃, b i = 1 := by
  obtain ⟨b, s, hs, rfl⟩ := exists_rootDiagUnit_mul_of_mem_levi_sup_diag σ J hx
  rw [hJ] at hs
  exact exists_rootDiagUnit_eq_of_mem_centralizer f₁ f₂ f₃ h12 h13 h23 c12 c13 c23 b hs
    hc₁ hc₂ hc₃

theorem subsystemGroup_image_perm_le_map_twistHom {F : Type} [Field F] (σ : F ≃+* F)
    (S : Set (Fin TwistTag.E6.tag.rank)) :
    subsystemGroup TwistTag.E6.tag F (TwistTag.E6.perm '' S) ≤
      (subsystemGroup TwistTag.E6.tag F S).map (twistHom TwistTag.E6 F σ.toRingHom) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, h | h⟩
  · obtain ⟨j, hj, rfl⟩ := hi
    rw [h]
    refine Subgroup.mem_map.2 ⟨xUnit TwistTag.E6.tag F j (σ.symm c),
      xUnit_mem_subsystemGroup hj _, ?_⟩
    rw [twistHom_xUnit]
    exact congrArg (xUnit TwistTag.E6.tag F (TwistTag.E6.perm j)) (σ.apply_symm_apply c)
  · obtain ⟨j, hj, rfl⟩ := hi
    rw [h]
    refine Subgroup.mem_map.2 ⟨yUnit TwistTag.E6.tag F j (σ.symm c),
      yUnit_mem_subsystemGroup hj _, ?_⟩
    rw [twistHom_yUnit]
    exact congrArg (yUnit TwistTag.E6.tag F (TwistTag.E6.perm j)) (σ.apply_symm_apply c)

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
