module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open scoped Pointwise
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootWeight CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section GroupTheory

private theorem exists_eq_mul_of_mem_sup_of_le_normalizer {G : Type*} [Group G] {C T : Subgroup G}
    (hTC : T ≤ Subgroup.normalizer (C : Set G)) {x : G} (hx : x ∈ C ⊔ T) :
    ∃ d ∈ C, ∃ t ∈ T, x = d * t := by
  have h : ((C ⊔ T : Subgroup G) : Set G) = (C : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left C T hTC
  rw [← SetLike.mem_coe, h] at hx
  obtain ⟨d, hd, t, ht, rfl⟩ := hx
  exact ⟨d, hd, t, ht, rfl⟩

private theorem map_supported_eq_of_mem_diagonalGroup {τ : Tag} {K : Type} [Field K] {t : ModGL τ K}
    (ht : t ∈ (diagonalGroup : Subgroup (ModGL τ K))) (S : Set (Label τ)) :
    (Finsupp.supported K K S).map (t : Module.End K (RootModule τ K)) =
      Finsupp.supported K K S := by
  have key : ∀ u ∈ (diagonalGroup : Subgroup (ModGL τ K)),
      (Finsupp.supported K K S).map (u : Module.End K (RootModule τ K)) ≤
        Finsupp.supported K K S := by
    intro u hu
    refine map_supported_le_of_entries _ fun a b hb hab => ?_
    obtain ⟨c, hc⟩ := exists_apply_single_of_mem_diagonalGroup hu b
    rw [hc, Finsupp.smul_apply, smul_eq_mul] at hab
    obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.1 (right_ne_zero_of_mul hab)
    exact hb
  refine le_antisymm (key t ht) ?_
  calc Finsupp.supported K K S
      = ((Finsupp.supported K K S).map (↑t⁻¹ : Module.End K (RootModule τ K))).map
          (t : Module.End K (RootModule τ K)) := by
        rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← Units.val_mul, mul_inv_cancel,
          Units.val_one, Module.End.one_eq_id, Submodule.map_id]
    _ ≤ (Finsupp.supported K K S).map (t : Module.End K (RootModule τ K)) :=
        Submodule.map_mono (key t⁻¹ (inv_mem ht))

end GroupTheory

section Datum

theorem exists_conj_mem_parabolic_sup_of_normalizes {k : Type} [Field k] (D : RootWeightDatum k)
    [Finite k] (r : ℕ) [Fact r.Prime] [CharP k r] {T : Subgroup (ModGL D.tag k)}
    (hTN : T ≤ Subgroup.normalizer (D.group : Set (ModGL D.tag k)))
    (hTD : T ≤ diagonalGroup) {R : Subgroup (ModGL D.tag k)} (hRC : R ≤ D.group)
    (hRr : IsPGroup r R) (hR : R ≠ ⊥) {A : Subgroup (ModGL D.tag k)} (hAC : A ≤ D.group ⊔ T)
    (hAR : A ≤ Subgroup.normalizer (R : Set (ModGL D.tag k))) :
    ∃ g ∈ D.group, ∃ l ∈ D.dominant, D.face l ≠ Set.univ ∧
      ∀ a ∈ A, g⁻¹ * a * g ∈ D.parabolic (D.face l) ⊔ T := by
  classical
  have := finite_modGL (τ := D.tag) (K := k)
  obtain ⟨M, -, -, -, F, hF1, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, hsemi⟩ :=
    D.root_p_subgroup_optimal_parabolic_containment r R hRC hRr hR
  obtain ⟨hJ, -, -, -, -⟩ := hdom g hg l hl hl1 hgl
  have hFg : ∀ c : ℝ, (D.filtration l c).map (g : Module.End k (RootModule D.tag k)) = F c :=
    hF1 g hg l hl1 hgl
  refine ⟨g, hg, l, hl, hJ, fun a ha => ?_⟩
  obtain ⟨d, hd, t, ht, rfl⟩ := exists_eq_mul_of_mem_sup_of_le_normalizer hTN (hAC ha)
  have htD := hTD ht
  set s : RootModule D.tag k ≃ₗ[k] RootModule D.tag k :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv k (RootModule D.tag k) t with hs
  have hsapp : ∀ v, s v = (t : Module.End k (RootModule D.tag k)) v := fun v => rfl
  have hssymm : ∀ v, s.symm v = ((t⁻¹ : ModGL D.tag k) : Module.End k (RootModule D.tag k)) v :=
    fun v => by
      rw [LinearEquiv.symm_apply_eq, hsapp, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_apply]
  have hconj : ∀ g : ModGL D.tag k, semilinearConjUnit s g = t * g * t⁻¹ := fun g =>
    Units.ext (LinearMap.ext fun v => by
      rw [coe_semilinearConjUnit, semilinearConj_apply, hssymm, hsapp]
      simp only [Units.val_mul, Module.End.mul_apply])
  have hnorm : ∀ g : ModGL D.tag k, semilinearConjUnit s g ∈ D.group ↔ g ∈ D.group := fun g => by
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.1 (hTN ht) g).symm
  have hs1 : (s.toLinearMap : Module.End k (RootModule D.tag k)) =
      (t : Module.End k (RootModule D.tag k)) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap t
  have hspace : ∀ χ ∈ D.weights, (D.weightSpace χ).map s.toLinearMap =
      D.weightSpace ((LinearIsometryEquiv.refl ℝ D.space) χ) := fun χ _ => by
    change (D.weightSpace χ).map s.toLinearMap = D.weightSpace χ
    rw [hs1, D.weightSpace_eq_supported]
    exact map_supported_eq_of_mem_diagonalGroup htD _
  have hat : d * t ∈ Subgroup.normalizer (R : Set (ModGL D.tag k)) := hAR ha
  have hQ' : ∀ x, x ∈ R ↔ ∃ q ∈ R, d * semilinearConjUnit s q * d⁻¹ = x := fun x => by
    have hmn := Subgroup.mem_normalizer_iff.1 hat
    constructor
    · intro hx
      refine ⟨(d * t)⁻¹ * x * (d * t), ?_, ?_⟩
      · rw [hmn, show (d * t) * ((d * t)⁻¹ * x * (d * t)) * (d * t)⁻¹ = x by group]
        exact hx
      · rw [hconj]
        group
    · rintro ⟨q, hq, rfl⟩
      rw [hconj]
      have := (hmn q).1 hq
      simpa [mul_assoc] using this
  have hmain := (hsemi (RingHom.id k) (RingHom.id k) s hnorm (LinearIsometryEquiv.refl ℝ D.space)
    (by simp) hspace d hd R hQ').2.2 g hg l hl1 hgl
  have hsmap : ∀ (a b : ModGL D.tag k) (X : Submodule k (RootModule D.tag k)),
      X.map ((a * b : ModGL D.tag k) : Module.End k (RootModule D.tag k)) =
        (X.map (b : Module.End k (RootModule D.tag k))).map
          (a : Module.End k (RootModule D.tag k)) := fun a b X => by
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  have hmapinv : ∀ (u : ModGL D.tag k) (X : Submodule k (RootModule D.tag k)),
      (X.map (u : Module.End k (RootModule D.tag k))).map
        ((u⁻¹ : ModGL D.tag k) : Module.End k (RootModule D.tag k)) = X := fun u X => by
    rw [← hsmap, inv_mul_cancel, Units.val_one, Module.End.one_eq_id, Submodule.map_id]
  have hFix : ∀ c : ℝ, (F c).map ((d * t : ModGL D.tag k) : Module.End k (RootModule D.tag k)) =
      F c := fun c => by
    rw [hsmap, ← hs1]
    exact ((hmain c).symm.trans (hFg c) : _)
  have hstab : g⁻¹ * (d * t) * g ∈ D.filtrationStab l := fun c => by
    rw [hsmap, hsmap, hFg c, hFix c, ← hFg c, hmapinv]
  have htstab : t ∈ D.filtrationStab l := fun c => by
    rw [D.filtration_eq_supported]
    exact map_supported_eq_of_mem_diagonalGroup htD _
  have hd₂C : g⁻¹ * d * (t * g * t⁻¹) ∈ D.group :=
    mul_mem (mul_mem (inv_mem hg) hd) ((Subgroup.mem_normalizer_iff.1 (hTN ht) g).1 hg)
  have hd₂F : g⁻¹ * d * (t * g * t⁻¹) ∈ D.filtrationStab l := by
    have : g⁻¹ * d * (t * g * t⁻¹) = (g⁻¹ * (d * t) * g) * t⁻¹ := by group
    rw [this]
    exact mul_mem hstab (inv_mem htstab)
  have hd₂P := (D.mem_group_and_filtrationStab_iff hl _).1 ⟨hd₂C, hd₂F⟩
  have e : g⁻¹ * (d * t) * g = (g⁻¹ * d * (t * g * t⁻¹)) * t := by group
  rw [e]
  exact Subgroup.mul_mem_sup hd₂P ht

end Datum

section Ordinary

variable {τ : Tag} {k : Type} [Field k]

private theorem rootDiagUnit_mem_normalizer_rootSpan (b : Fin τ.rank → kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) :
    rootDiagUnit τ b ∈ Subgroup.normalizer (rootSpan τ k S : Set (ModGL τ k)) :=
  mem_normalizer_of_map_eq (map_rootSpan_of_forall fun α hα =>
    map_conj_rootDiagUnit_rootSubgroup b (hS α hα))

theorem rootDiagUnit_mem_normalizer_parabolicRadical (b : Fin τ.rank → kˣ)
    (J : Set (Fin τ.rank)) :
    rootDiagUnit τ b ∈ Subgroup.normalizer (parabolicRadical τ k J : Set (ModGL τ k)) :=
  rootDiagUnit_mem_normalizer_rootSpan b fun _ hα => hα.1.1

@[expose] def innDiagGL (τ : Tag) (k : Type) [Field k] : Subgroup (ModGL τ k) :=
  adjointGroup τ k ⊔ (rootDiagUnitHom τ k).range

end Ordinary

end CFSG.LieType.SeitzGeneration.ExcWideThree
