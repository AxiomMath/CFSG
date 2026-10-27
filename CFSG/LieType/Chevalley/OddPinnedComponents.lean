module

public import CFSG.LieType.Chevalley.PerfectSimpleRoot
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Chevalley.NoncentralNormalSolvable
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial (isQuasisimple_congr quasisimple_subnormal_subgroups)

theorem odd_pinned_Chevalley_p_components
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : ringChar K ≠ 2) :
    IsSimpleGroup (adjointGroup τ K) ∧ (∃ x y : adjointGroup τ K, x * y ≠ y * x) ∧
    ∀ (p : ℕ) (L : Subgroup (adjointGroup τ K)), CFSG.IsPComponent p L →
      CFSG.IsQuasisimple L ∧ L = ⊤ := by
  have hnc := (opposite_simple_root_noncommutativity τ K).2.2.1
  have : Group.IsPerfect (adjointGroup τ K) := ⟨odd_characteristic_perfect τ K hK⟩
  have : Nontrivial (adjointGroup τ K) := by
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨⟨a * b, b * a, hab⟩⟩
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  have hsimple : IsSimpleGroup (adjointGroup τ K) := by
    refine IsSimpleGroup.mk fun M hM => ?_
    by_cases hbot : M = ⊥
    · exact Or.inl hbot
    · right
      have hnot : ¬ M ≤ Subgroup.center (adjointGroup τ K) := by
        rw [hZ]
        exact fun h => hbot (le_bot_iff.1 h)
      have hsolv := (noncentral_normal_solvable_quotient τ K M hnot).2.1
      by_contra htop
      have : Nontrivial (adjointGroup τ K ⧸ M) := by
        rw [← not_subsingleton_iff_nontrivial, QuotientGroup.subsingleton_iff]
        exact htop
      exact Group.IsPerfect.not_isSolvable _ hsolv
  have hquasi := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  refine ⟨hsimple, hnc, fun p L hL => ?_⟩
  have hLnt := CFSG.ComponentClassification.CatalogueBAlternating.pComponent_nontrivial hL
  obtain ⟨-, -, hLsub, -, -⟩ := hL
  rcases quasisimple_subnormal_subgroups hquasi hLsub with h | h
  · subst h
    exact ⟨(isQuasisimple_congr Subgroup.topEquiv).2 hquasi, rfl⟩
  · rw [hZ] at h
    exfalso
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hLnt
    apply hab
    have ha' := le_bot_iff.1 h ▸ ha
    have hb' := le_bot_iff.1 h ▸ hb
    rw [Subgroup.mem_bot] at ha' hb'
    exact Subtype.ext (ha'.trans hb'.symm)

end CFSG.LieType.Chevalley
