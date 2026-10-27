module

public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.CatalogueBGeneralLinear
  (generalLinear_two_small_solvable specialLinear_quasisimple no_pComponent_of_solvable)
open CFSG.ComponentClassification.CatalogueBAlternating (pComponent_nontrivial pComponent_perfect)

variable {τ : Tag} {K : Type} [Field K]

theorem closure_xUnit_yUnit_eq_rootSubgroup_sup
    (i : Fin τ.rank) :
    Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) =
      rootSubgroup τ K (Pi.single i 1) ⊔ rootSubgroup τ K (-Pi.single i 1) := by
  rw [Subgroup.closure_union, rootSubgroup, rootSubgroup,
    show pinnedX τ K (Pi.single i 1) = xUnit τ K i from funext (pinnedX_single τ K i),
    show pinnedX τ K (-Pi.single i 1) = yUnit τ K i from funext (pinnedX_neg_single τ K i)]

theorem map_conj_canonicalRep_closure_xUnit_yUnit
    {w : WeylGroup τ} {i : Fin τ.rank}
    {α : Fin τ.rank → ℤ} (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = α) :
    (Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i))).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
      rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
  rw [closure_xUnit_yUnit_eq_rootSubgroup_sup, Subgroup.map_sup,
    (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i),
    (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ i), smul_neg, hw]

theorem exists_mulEquiv_rootSubgroup_sup
    (hK : ringChar K ≠ 2) {w : WeylGroup τ}
    {i : Fin τ.rank} {α : Fin τ.rank → ℤ} (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = α) :
    ∃ e : SL2 K ≃* (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
      ∀ A, (e A : ModGL τ K) = canonicalRep (coxeterSystem τ) K w * simpleRootSL2 τ K i A *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ := by
  set n := canonicalRep (coxeterSystem τ) K w
  set ρ : SL2 K →* ModGL τ K := (MulAut.conj n).toMonoidHom.comp (simpleRootSL2 τ K i)
  have hinj : Function.Injective ρ :=
    (MulAut.conj n).injective.comp (simpleRootSL2_injective hK i)
  have hrange : ρ.range = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
    rw [MonoidHom.range_comp, range_simpleRootSL2, map_conj_canonicalRep_closure_xUnit_yUnit hw]
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun A => rfl⟩

theorem odd_arbitrary_root_pair_SL2_p_components
    (τ : Tag) (K : Type) [Field K]
    (hK : ringChar K ≠ 2) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ≤ adjointGroup τ K ∧
    Nonempty (SL2 K ≃* (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K))) ∧
    (∀ (w : WeylGroup τ) (i : Fin τ.rank), w • (Pi.single i 1 : Fin τ.rank → ℤ) = α →
      (Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i))).map
          (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom =
        rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) ∧
      (∃ f : Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) ≃*
          (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
        ∀ g, (f g : ModGL τ K) = canonicalRep (coxeterSystem τ) K w * g *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) ∧
      ∃ e : SL2 K ≃* (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)),
        (∀ c, (e (uSL c) : ModGL τ K) = canonicalRep (coxeterSystem τ) K w * xUnit τ K i c *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) ∧
        ∀ c, (e (vSL c) : ModGL τ K) = canonicalRep (coxeterSystem τ) K w * yUnit τ K i c *
          (canonicalRep (coxeterSystem τ) K w)⁻¹) ∧
    ∀ [Finite K],
      (Nat.card K = 3 →
        Group.IsSolvable (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) ∧
        ∀ (p : ℕ) (L : Subgroup
          (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K))),
          ¬ CFSG.IsPComponent p L) ∧
      (5 ≤ Nat.card K →
        CFSG.IsQuasisimple (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) ∧
        ∀ (p : ℕ) (L : Subgroup
          (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K))),
          CFSG.IsPComponent p L → L = ⊤ ∧ CFSG.IsQuasisimple L) := by
  set Q : Subgroup (ModGL τ K) := rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)
  obtain ⟨w₀, i₀, hw₀⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨e₀, -⟩ := exists_mulEquiv_rootSubgroup_sup hK hw₀
  refine ⟨sup_le (rootSubgroup_le_adjointGroup α) (rootSubgroup_le_adjointGroup (-α)), ⟨e₀⟩,
    fun w i hw => ⟨map_conj_canonicalRep_closure_xUnit_yUnit hw, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ⟨((MulAut.conj (canonicalRep (coxeterSystem τ) K w)).subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_conj_canonicalRep_closure_xUnit_yUnit hw)), fun g => rfl⟩
  · obtain ⟨e, he⟩ := exists_mulEquiv_rootSubgroup_sup hK hw
    exact ⟨e, fun c => by rw [he, simpleRootSL2_uSL], fun c => by rw [he, simpleRootSL2_vSL]⟩
  · intro h3
    have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) K) :=
      generalLinear_two_small_solvable K (Or.inr h3)
    have : Group.IsSolvable (SL2 K) :=
      Group.isSolvable_of_isSolvable_injective Matrix.SpecialLinearGroup.toGL_injective
    have : Group.IsSolvable Q :=
      Group.isSolvable_of_isSolvable_injective (f := e₀.symm.toMonoidHom) e₀.symm.injective
    exact ⟨this, fun p L => no_pComponent_of_solvable p L⟩
  · intro h5
    have hquasi : CFSG.IsQuasisimple Q := (isQuasisimple_congr e₀).1
      (specialLinear_quasisimple 2 K le_rfl (Or.inr (by omega)) (Or.inr (by omega)))
    refine ⟨hquasi, fun p L hL => ?_⟩
    have := pComponent_nontrivial hL
    have := pComponent_perfect hL
    rcases quasisimple_subnormal_subgroups hquasi hL.choose_spec.2.1 with h | h
    · subst h
      exact ⟨rfl, (isQuasisimple_congr Subgroup.topEquiv).2 hquasi⟩
    · exfalso
      exact Group.IsPerfect.not_isMulCommutative L
        ⟨⟨fun x y => Subtype.ext (Subgroup.mem_center_iff.1 (h x.2) y).symm⟩⟩

end CFSG.LieType.Chevalley
