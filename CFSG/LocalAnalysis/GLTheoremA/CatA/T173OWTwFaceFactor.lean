module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
import CFSG.LieType.Chevalley.SubsystemComponent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatalogueBHigherLinearAction


structure LeviFactor (F : Type) [Field F] (m : ℕ) (S : Set (Fin TwistTag.E6.tag.rank)) where
  ι : Matrix.SpecialLinearGroup (Fin m) F →* ModGL TwistTag.E6.tag F
  injective : Function.Injective ι
  range_eq : ι.range = subsystemGroup TwistTag.E6.tag F S
  diag_conj : ∀ b : Fin TwistTag.E6.tag.rank → Fˣ, ∃ D : Matrix.GeneralLinearGroup (Fin m) F,
    (∀ a a' : Fin m, a ≠ a' → (D : Matrix (Fin m) (Fin m) F) a a' = 0) ∧
    ∀ g, rootDiagUnit TwistTag.E6.tag b * ι g * (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      ι (slConjugation m F D g)
  diag_mem : ∀ h : Matrix.SpecialLinearGroup (Fin m) F,
    (∀ a a' : Fin m, a ≠ a' → (h : Matrix (Fin m) (Fin m) F) a a' = 0) →
      ι h ∈ (rootDiagUnitHom TwistTag.E6.tag F).range

private theorem conj_mul_of_commute {G : Type*} [Group G] {d h t g : G}
    (htg : Commute t g) (hth : Commute t h) :
    d * (h * t) * g * (d * (h * t))⁻¹ = d * (h * g * h⁻¹) * d⁻¹ := by
  have he : d * (h * t) * g * (d * (h * t))⁻¹ = d * h * (t * g * t⁻¹) * h⁻¹ * d⁻¹ := by
    group
  rw [he, htg.mul_inv_cancel]
  group

private theorem slConjugation_mul_conj {m : ℕ} {F : Type} [Field F]
    (D : Matrix.GeneralLinearGroup (Fin m) F) (h g : Matrix.SpecialLinearGroup (Fin m) F) :
    slConjugation m F D (h * g * h⁻¹) =
      slConjugation m F (D * Matrix.SpecialLinearGroup.toGL h) g := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation, toGL_slConjugation, map_mul, map_mul, map_inv]
  group

theorem LeviFactor.exists_eq_mul {F : Type} [Field F] {m : ℕ}
    {S T : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S) (hST : Disjoint S T)
    (h0 : ∀ i ∈ S, ∀ j ∈ T, TwistTag.E6.tag.cartan i j = 0) {s : ModGL TwistTag.E6.tag F}
    (hs : s ∈ subsystemGroup TwistTag.E6.tag F (S ∪ T)) :
    ∃ h : Matrix.SpecialLinearGroup (Fin m) F,
      ∃ t ∈ subsystemGroup TwistTag.E6.tag F T, s = f.ι h * t := by
  have hcent : subsystemGroup TwistTag.E6.tag F S ≤
      Subgroup.centralizer
        (subsystemGroup TwistTag.E6.tag F T : Set (ModGL TwistTag.E6.tag F)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (SubsysComp.commute_of_cartan_eq_zero hST h0 x hx y hy).eq.symm
  have hnorm : subsystemGroup TwistTag.E6.tag F S ≤
      Subgroup.normalizer (subsystemGroup TwistTag.E6.tag F T : Set (ModGL TwistTag.E6.tag F)) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hmem : s ∈ (↑(subsystemGroup TwistTag.E6.tag F S ⊔
      subsystemGroup TwistTag.E6.tag F T) : Set (ModGL TwistTag.E6.tag F)) := by
    rw [← SubsysComp.subsystemGroup_union S T]
    exact hs
  rw [Subgroup.coe_mul_of_left_le_normalizer_right (subsystemGroup TwistTag.E6.tag F S)
    (subsystemGroup TwistTag.E6.tag F T) hnorm] at hmem
  obtain ⟨n, hn, t, ht, hnt⟩ := Set.mem_mul.mp hmem
  have hn' : n ∈ f.ι.range := by
    rw [f.range_eq]
    exact hn
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hn'
  exact ⟨h, t, ht, hnt.symm⟩

theorem LeviFactor.exists_conj {F : Type} [Field F] {m : ℕ}
    {S T : Set (Fin TwistTag.E6.tag.rank)} (f : LeviFactor F m S) (hST : Disjoint S T)
    (h0 : ∀ i ∈ S, ∀ j ∈ T, TwistTag.E6.tag.cartan i j = 0)
    (b : Fin TwistTag.E6.tag.rank → Fˣ) {s : ModGL TwistTag.E6.tag F}
    (hs : s ∈ subsystemGroup TwistTag.E6.tag F (S ∪ T)) :
    ∃ A : Matrix.GeneralLinearGroup (Fin m) F, ∀ g,
      rootDiagUnit TwistTag.E6.tag b * s * f.ι g * (rootDiagUnit TwistTag.E6.tag b * s)⁻¹ =
        f.ι (slConjugation m F A g) := by
  obtain ⟨h, t, ht, rfl⟩ := f.exists_eq_mul hST h0 hs
  obtain ⟨D, -, hDconj⟩ := f.diag_conj b
  refine ⟨D * Matrix.SpecialLinearGroup.toGL h, fun g => ?_⟩
  have hmem : ∀ x ∈ f.ι.range, Commute x t := by
    intro x hx
    have hx' : x ∈ subsystemGroup TwistTag.E6.tag F S := by
      rwa [← f.range_eq]
    exact SubsysComp.commute_of_cartan_eq_zero hST h0 x hx' t ht
  have htg : Commute t (f.ι g) := (hmem (f.ι g) (MonoidHom.mem_range.mpr ⟨g, rfl⟩)).symm
  have hth : Commute t (f.ι h) := (hmem (f.ι h) (MonoidHom.mem_range.mpr ⟨h, rfl⟩)).symm
  calc
    rootDiagUnit TwistTag.E6.tag b * (f.ι h * t) * f.ι g *
        (rootDiagUnit TwistTag.E6.tag b * (f.ι h * t))⁻¹
        = rootDiagUnit TwistTag.E6.tag b * (f.ι h * f.ι g * (f.ι h)⁻¹) *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹ := conj_mul_of_commute htg hth
    _ = rootDiagUnit TwistTag.E6.tag b * f.ι (h * g * h⁻¹) *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹ := by
          rw [show f.ι h * f.ι g * (f.ι h)⁻¹ = f.ι (h * g * h⁻¹) by simp]
    _ = f.ι (slConjugation m F D (h * g * h⁻¹)) := hDconj (h * g * h⁻¹)
    _ = f.ι (slConjugation m F (D * Matrix.SpecialLinearGroup.toGL h) g) := by
          rw [slConjugation_mul_conj]

end CFSG.LocalAnalysis.GLTheoremA.T173O.TwFace
