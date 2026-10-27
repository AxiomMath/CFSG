module

public import CFSG.LieType.Chevalley.CLSEvenCoordinateFieldsFourGroup
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial

@[expose] def d4TrialityHighestRoot : Fin TwistTag.D4.tag.rank → ℤ :=
  (![1, 1, 2, 1] : Fin 4 → ℤ)

@[expose] def d4CentralIndex : Fin TwistTag.D4.tag.rank :=
  ⟨2, by decide⟩

theorem isRoot_d4TrialityHighestRoot
    : IsRoot TwistTag.D4.tag d4TrialityHighestRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨22, by decide, by decide⟩

theorem height_d4TrialityHighestRoot : height d4TrialityHighestRoot = 5 := by
  decide

theorem height_le_five_of_isRoot_D4 {α : Fin TwistTag.D4.tag.rank → ℤ}
    (hα : IsRoot TwistTag.D4.tag α) : height α ≤ 5 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range TwistTag.D4.tag.rootCertificate.roots.length).all fun k =>
      decide (height (TwistTag.D4.tag.rootCertificate.root k) ≤ 5) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem forall_height_le_d4TrialityHighestRoot :
    ∀ γ, IsRoot TwistTag.D4.tag γ → height γ ≤ height d4TrialityHighestRoot := fun _ hγ => by
  rw [height_d4TrialityHighestRoot]
  exact height_le_five_of_isRoot_D4 hγ

theorem permLattice_d4TrialityHighestRoot :
    permLattice TwistTag.D4.perm d4TrialityHighestRoot = d4TrialityHighestRoot := by
  decide

theorem perm_d4CentralIndex : TwistTag.D4.perm d4CentralIndex = d4CentralIndex := by
  decide

theorem twistHom_pinnedX_one_of_fixed
    {t : TwistTag} {K : Type} [Field K] (h2 : (2 : K) = 0)
    (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hρ : permLattice t.perm α = α) :
    twistHom t K σ (pinnedX t.tag K α 1) = pinnedX t.tag K α 1 := by
  have hσ : Units.map (entrywiseHom σ) (pinnedX t.tag K α 1) = pinnedX t.tag K α 1 :=
    Units.ext (entrywise_pinnedX_one σ α)
  rw [twistHom_apply, hσ, ← twistHom_id_eq, twistHom_id_pinnedX h2 hα, hρ]

theorem pinnedX_one_mem_graphFixedRootGroup
    {t : TwistTag} {K : Type} [Field K]
    (h2 : (2 : K) = 0) (σ : K →+* K) {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α)
    (hpos : 0 < height α) (hρ : permLattice t.perm α = α) :
    pinnedX t.tag K α 1 ∈ graphFixedRootGroup t K σ :=
  Subgroup.mem_sup_left (Subgroup.mem_inf.2
    ⟨pinnedX_mem_rootSpan (S := {β | IsRoot t.tag β ∧ 0 < height β}) ⟨hα, hpos⟩ 1,
      pinnedX_mem_adjointGroup α 1, twistHom_pinnedX_one_of_fixed h2 σ hα hρ⟩)

theorem even_triality_coordinate_fields_fixed_four_group
    (K : Type) [Field K]
    (hK : ringChar K = 2) (σ : K →+* K) :
    CFSG.IsElementaryAbelian 2 (Subgroup.closure
      ({pinnedX TwistTag.D4.tag K d4TrialityHighestRoot 1,
        xUnit TwistTag.D4.tag K d4CentralIndex 1} : Set (ModGL TwistTag.D4.tag K))) ∧
    Nat.card (Subgroup.closure
      ({pinnedX TwistTag.D4.tag K d4TrialityHighestRoot 1,
        xUnit TwistTag.D4.tag K d4CentralIndex 1} : Set (ModGL TwistTag.D4.tag K))) = 4 ∧
    Subgroup.closure
      ({pinnedX TwistTag.D4.tag K d4TrialityHighestRoot 1,
        xUnit TwistTag.D4.tag K d4CentralIndex 1} : Set (ModGL TwistTag.D4.tag K)) ≤
      graphFixedRootGroup TwistTag.D4 K σ ∧
    ∀ δ : K →+* K, ∀ g ∈ Subgroup.closure
      ({pinnedX TwistTag.D4.tag K d4TrialityHighestRoot 1,
        xUnit TwistTag.D4.tag K d4CentralIndex 1} : Set (ModGL TwistTag.D4.tag K)),
      entrywise δ (g : Module.End K (RootModule TwistTag.D4.tag K)) = g := by
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := ringChar.of_eq hK
    exact_mod_cast CharP.cast_eq_zero K 2
  set θ := d4TrialityHighestRoot
  set β : Fin TwistTag.D4.tag.rank → ℤ := Pi.single d4CentralIndex 1 with hβdef
  have hb : xUnit TwistTag.D4.tag K d4CentralIndex 1 = pinnedX TwistTag.D4.tag K β 1 :=
    (pinnedX_single TwistTag.D4.tag K d4CentralIndex 1).symm
  rw [hb]
  have hθ : IsRoot TwistTag.D4.tag θ ∧ 0 < height θ :=
    ⟨isRoot_d4TrialityHighestRoot, by rw [height_d4TrialityHighestRoot]; norm_num⟩
  have hβ : IsRoot TwistTag.D4.tag β ∧ 0 < height β :=
    ⟨isRoot_single _ _, by rw [height_single]; norm_num⟩
  have hθβ : θ ≠ β := by decide
  have hxy : pinnedX TwistTag.D4.tag K θ 1 * pinnedX TwistTag.D4.tag K β 1 =
      pinnedX TwistTag.D4.tag K β 1 * pinnedX TwistTag.D4.tag K θ 1 :=
    commute_pinnedX_of_forall_height_le K hθ.1 forall_height_le_d4TrialityHighestRoot hβ.1 hβ.2
      1 1
  have hx := pinnedX_one_mul_self h2 (τ := TwistTag.D4.tag) θ
  have hy := pinnedX_one_mul_self h2 (τ := TwistTag.D4.tag) β
  have hcl : Subgroup.closure ({pinnedX TwistTag.D4.tag K θ 1, pinnedX TwistTag.D4.tag K β 1} :
      Set (ModGL TwistTag.D4.tag K)) = FourGroup.kleinFourOf _ _ hx hy hxy := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_)
      (FourGroup.kleinFourOf_le (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
    rintro _ (rfl | rfl)
    · exact FourGroup.left_mem_kleinFourOf
    · exact FourGroup.right_mem_kleinFourOf
  rw [hcl]
  have hβρ : permLattice TwistTag.D4.perm β = β := by
    rw [hβdef, permLattice_single, perm_d4CentralIndex]
  refine ⟨FourGroup.isElementaryAbelian_kleinFourOf,
    FourGroup.card_kleinFourOf (pinnedX_one_ne_one θ) (pinnedX_one_ne_one β)
      (pinnedX_one_ne_pinnedX_one hθ hβ hθβ),
    FourGroup.kleinFourOf_le
      (pinnedX_one_mem_graphFixedRootGroup h2 σ hθ.1 hθ.2 permLattice_d4TrialityHighestRoot)
      (pinnedX_one_mem_graphFixedRootGroup h2 σ hβ.1 hβ.2 hβρ),
    fun δ g hg => entrywise_eq_of_mem_kleinFourOf δ (entrywise_pinnedX_one δ θ)
      (entrywise_pinnedX_one δ β) hg⟩

end CFSG.LieType.Chevalley
