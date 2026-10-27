module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassListBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInner
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6ClassesReps
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

variable {K : Type} [Field K]

@[expose] def e6CascR17 : Fin TwistTag.E6.tag.rank → ℤ := (![1, 0, 1, 1, 1, 1] : Fin 6 → ℤ)
@[expose] def e6CascC : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 1, 1, 1, 0] : Fin 6 → ℤ)
@[expose] def e6RootA4 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 1, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA3 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 1, 0, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA5 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 0, 1, 0] : Fin 6 → ℤ)
@[expose] def e6RootA34 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 1, 1, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootA45 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 1, 1, 0] : Fin 6 → ℤ)
@[expose] def e6RootNA3 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, -1, 0, 0, 0] : Fin 6 → ℤ)
@[expose] def e6RootNA5 : Fin TwistTag.E6.tag.rank → ℤ := (![0, 0, 0, 0, -1, 0] : Fin 6 → ℤ)

@[expose] def e6D4CD : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 0, 1, 0, 0] : Fin 6 → ℤ)
@[expose] def e6D4BC : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 1, 1, 0] : Fin 6 → ℤ)
@[expose] def e6D4AC : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 1, 1, 1, 1] : Fin 6 → ℤ)
@[expose] def e6D4BCD : Fin TwistTag.E6.tag.rank → ℤ := (![0, 1, 1, 2, 1, 0] : Fin 6 → ℤ)
@[expose] def e6D4ABC : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ)
@[expose] def e6D4ACD : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 1, 2, 1, 1] : Fin 6 → ℤ)
@[expose] def e6D4ABCD : Fin TwistTag.E6.tag.rank → ℤ := (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem e6HighestRoot_eq_vec : e6HighestRoot = (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) := rfl

theorem twistedE6Cascade_eq :
    twistedE6Cascade = [e6HighestRoot, e6CascR17, e6CascC, e6RootA4] := rfl

@[expose] def twistedE6CascTable :
    List (List (Fin TwistTag.E6.tag.rank → ℤ) × List (Fin TwistTag.E6.foldedTag.rank)) :=
  [([e6HighestRoot], []), ([e6CascR17], ([3, 2, 1, 2, 3] : List (Fin 4))), ([e6CascC], ([3, 2, 1, 0, 2, 3] : List (Fin 4))),
    ([e6RootA4], ([3, 2, 1, 0, 2, 1, 3] : List (Fin 4))), ([e6HighestRoot, e6CascR17], []),
    ([e6HighestRoot, e6CascC], ([0] : List (Fin 4))), ([e6HighestRoot, e6RootA4], ([0, 1] : List (Fin 4))),
    ([e6CascR17, e6CascC], ([0, 3, 2, 1, 2, 3] : List (Fin 4))), ([e6CascR17, e6RootA4], ([0, 1, 3, 2, 1, 2, 3] : List (Fin 4))),
    ([e6CascC, e6RootA4], ([0, 1, 3, 2, 1, 0, 2, 3] : List (Fin 4))), ([e6HighestRoot, e6CascR17, e6CascC], []),
    ([e6HighestRoot, e6CascR17, e6RootA4], ([1] : List (Fin 4))), ([e6HighestRoot, e6CascC, e6RootA4], ([1, 0] : List (Fin 4))),
    ([e6CascR17, e6CascC, e6RootA4], ([1, 0, 3, 2, 1, 2, 3] : List (Fin 4))),
    ([e6HighestRoot, e6CascR17, e6CascC, e6RootA4], [])]

theorem twistedE6CascTable_check :
    (∀ S ∈ twistedE6Cascade.sublists, S ≠ [] → ∃ e ∈ twistedE6CascTable, e.1 = S) ∧
      ∀ e ∈ twistedE6CascTable,
        (e.1.map (twistedE6RelAct e.2)).Perm (twistedE6Cascade.take e.1.length) := by
  refine ⟨by decide, ?_⟩
  intro e he
  have h : ∀ e ∈ twistedE6CascTable,
      (e.1.map (twistedE6RelAct e.2)).isPerm (twistedE6Cascade.take e.1.length) = true := by
    decide
  exact List.isPerm_iff.1 (h e he)

theorem twistedE6_mulAutConj_mul {G : Type*} [Group G] (a b x : G) :
    MulAut.conj (a * b) x = MulAut.conj a (MulAut.conj b x) := by
  simp only [MulAut.conj_apply]
  group


theorem twistedE6_conj_pinnedX_add [CharP K 2] {α β γ : Fin TwistTag.E6.tag.rank → ℤ}
    (h : (twistedE6TwoRootB α && twistedE6TwoRootB β && twistedE6TwoRootB γ &&
      !twistedE6TwoVecB α β && twistedE6TwoVecB (α + β) γ) = true) (c d : K) :
    pinnedX TwistTag.E6.tag K α c * pinnedX TwistTag.E6.tag K β d *
        (pinnedX TwistTag.E6.tag K α c)⁻¹ =
      pinnedX TwistTag.E6.tag K γ (c * d) * pinnedX TwistTag.E6.tag K β d := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hα, hβ⟩, hγ⟩, hne⟩, hsum⟩ := h
  rw [← isRoot_iff_twistedE6TwoRootB] at hα hβ hγ
  rw [twistedE6TwoVecB_iff] at hsum
  have hne' : α ≠ β := fun e => by rw [e, ← Bool.not_eq_true, twistedE6TwoVecB_iff] at hne; exact hne rfl
  subst hsum
  have hc := commutator_pinnedX_of_isRoot_add_E6 (K := K) hα hβ hne' hγ c d
  rw [commutatorElement_def] at hc
  rw [← hc]
  group

theorem twistedE6_conj_pinnedX_fix {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : (twistedE6TwoRootB α && twistedE6TwoRootB β && !twistedE6TwoVecB α β &&
      !twistedE6TwoVecB (α + β) 0 && !twistedE6TwoRootB (α + β)) = true) (c d : K) :
    pinnedX TwistTag.E6.tag K α c * pinnedX TwistTag.E6.tag K β d *
        (pinnedX TwistTag.E6.tag K α c)⁻¹ = pinnedX TwistTag.E6.tag K β d := by
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hα, hβ⟩, hne⟩, h0⟩, hn⟩ := h
  rw [← isRoot_iff_twistedE6TwoRootB] at hα hβ
  have hne' : α ≠ β := fun e => by rw [e, ← Bool.not_eq_true, twistedE6TwoVecB_iff] at hne; exact hne rfl
  have h0' : α ≠ -β := fun e => by
    rw [e, neg_add_cancel, ← Bool.not_eq_true, twistedE6TwoVecB_iff] at h0
    exact h0 rfl
  have hn' : ¬IsRoot TwistTag.E6.tag (α + β) := by
    rw [isRoot_iff_twistedE6TwoRootB, hn]
    exact Bool.false_ne_true
  rw [(commute_pinnedX_of_not_isRoot_add_E6 hα hβ hne' h0' hn' c d).eq, mul_inv_cancel_right]

theorem twistedE6_commute_pinnedX {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : (twistedE6TwoRootB α && twistedE6TwoRootB β && !twistedE6TwoVecB α β &&
      !twistedE6TwoVecB (α + β) 0 && !twistedE6TwoRootB (α + β)) = true) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) := by
  exact mul_inv_eq_iff_eq_mul.1 (twistedE6_conj_pinnedX_fix (K := K) h c d)

theorem twistedE6_pinnedX_one_mul_self [CharP K 2] (ε : Fin TwistTag.E6.tag.rank → ℤ) :
    pinnedX TwistTag.E6.tag K ε 1 * pinnedX TwistTag.E6.tag K ε 1 = 1 := by
  rw [← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

theorem twistedE6_commute_cascade {γ δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hγ : γ ∈ twistedE6Cascade) (hδ : δ ∈ twistedE6Cascade) (hne : γ ≠ δ) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K γ c) (pinnedX TwistTag.E6.tag K δ d) := by
  have h : ∀ γ ∈ twistedE6Cascade, ∀ δ ∈ twistedE6Cascade, γ ≠ δ →
      (twistedE6TwoRootB γ && twistedE6TwoRootB δ && !twistedE6TwoVecB γ δ &&
        !twistedE6TwoVecB (γ + δ) 0 && !twistedE6TwoRootB (γ + δ)) = true := by
    decide
  exact twistedE6_commute_pinnedX (h γ hγ δ hδ hne) c d

theorem exists_conj_cascade_sublist_eq_take [CharP K 2] (σ : K →+* K)
    {S : List (Fin TwistTag.E6.tag.rank → ℤ)} (hS : S.Sublist twistedE6Cascade) (hS0 : S ≠ []) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ =
        ((twistedE6Cascade.take S.length).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod := by
  obtain ⟨⟨S', ω⟩, he, rfl⟩ := twistedE6CascTable_check.1 S (List.mem_sublists.2 hS) hS0
  have hperm := twistedE6CascTable_check.2 _ he
  have hSr : ∀ β ∈ S', IsRoot TwistTag.E6.tag β := fun β hβ =>
    isRoot_of_mem_twistedE6Cascade (hS.subset hβ)
  refine ⟨twistedE6RelWeyl K ω, twistedE6RelWeyl_mem σ ω, ?_⟩
  rw [twistedE6RelWeyl_conj_list_prod ω hSr fun _ => (1 : K)]
  have e : (S'.map fun β => pinnedX TwistTag.E6.tag K (twistedE6RelAct ω β) 1) =
      ((S'.map (twistedE6RelAct ω)).map fun γ => pinnedX TwistTag.E6.tag K γ 1) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine (hperm.map _).prod_eq' ?_
  have hnd : (S'.map (twistedE6RelAct ω)).Nodup :=
    hperm.nodup_iff.2 (twistedE6Cascade_facts.1.sublist (List.take_sublist _ _))
  have hmem : ∀ γ ∈ S'.map (twistedE6RelAct ω), γ ∈ twistedE6Cascade := fun γ hγ =>
    List.mem_of_mem_take (hperm.subset hγ)
  exact List.pairwise_map.2 (hnd.pairwise_of_forall_ne fun γ hγ δ hδ hne =>
    twistedE6_commute_cascade (hmem γ hγ) (hmem δ hδ) hne 1 1)

theorem twistedE6_mulAutConj_add [CharP K 2] {α β γ : Fin TwistTag.E6.tag.rank → ℤ}
    (h : (twistedE6TwoRootB α && twistedE6TwoRootB β && twistedE6TwoRootB γ &&
      !twistedE6TwoVecB α β && twistedE6TwoVecB (α + β) γ) = true) (c d : K) :
    MulAut.conj (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) =
      pinnedX TwistTag.E6.tag K γ (c * d) * pinnedX TwistTag.E6.tag K β d :=
  twistedE6_conj_pinnedX_add h c d

theorem twistedE6_mulAutConj_fix {α β : Fin TwistTag.E6.tag.rank → ℤ}
    (h : (twistedE6TwoRootB α && twistedE6TwoRootB β && !twistedE6TwoVecB α β &&
      !twistedE6TwoVecB (α + β) 0 && !twistedE6TwoRootB (α + β)) = true) (c d : K) :
    MulAut.conj (pinnedX TwistTag.E6.tag K α c) (pinnedX TwistTag.E6.tag K β d) =
      pinnedX TwistTag.E6.tag K β d :=
  twistedE6_conj_pinnedX_fix h c d

theorem twistedE6_conj_h1 [CharP K 2] :
    MulAut.conj (pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1)
        (pinnedX TwistTag.E6.tag K e6RootA4 1 * pinnedX TwistTag.E6.tag K e6CascC 1) =
      pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1 := by
  simp only [map_mul, MulAut.mul_apply,
    twistedE6_mulAutConj_add (α := e6RootA5) (β := e6RootA4) (γ := e6RootA45) (by decide),
    twistedE6_mulAutConj_fix (α := e6RootA5) (β := e6CascC) (by decide), one_mul,
    twistedE6_mulAutConj_add (α := e6RootA3) (β := e6RootA45) (γ := e6CascC) (by decide),
    twistedE6_mulAutConj_add (α := e6RootA3) (β := e6RootA4) (γ := e6RootA34) (by decide),
    twistedE6_mulAutConj_fix (α := e6RootA3) (β := e6CascC) (by decide)]
  have hc : Commute (pinnedX TwistTag.E6.tag K e6CascC 1)
      (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1) :=
    ((twistedE6_commute_pinnedX (by decide) 1 1).mul_right
      (twistedE6_commute_pinnedX (by decide) 1 1)).mul_right
        (twistedE6_commute_pinnedX (by decide) 1 1)
  calc pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA45 1 *
          (pinnedX TwistTag.E6.tag K e6RootA34 1 * pinnedX TwistTag.E6.tag K e6RootA4 1) *
          pinnedX TwistTag.E6.tag K e6CascC 1
        = pinnedX TwistTag.E6.tag K e6CascC 1 *
            (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
              pinnedX TwistTag.E6.tag K e6RootA4 1) * pinnedX TwistTag.E6.tag K e6CascC 1 := by
          group
      _ = (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
              pinnedX TwistTag.E6.tag K e6RootA4 1) *
            (pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6CascC 1) := by
          rw [hc.eq]
          group
      _ = _ := by rw [twistedE6_pinnedX_one_mul_self, mul_one]

theorem twistedE6_conj_h2 [CharP K 2] (σ : K →+* K) {δ : K} (hδ : δ + σ δ = 1) :
    MulAut.conj (pinnedX TwistTag.E6.tag K e6RootNA3 δ *
        pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ))
        (pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
          pinnedX TwistTag.E6.tag K e6RootA4 1) =
      pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 := by
  simp only [map_mul, MulAut.mul_apply,
    twistedE6_mulAutConj_add (α := e6RootNA5) (β := e6RootA45) (γ := e6RootA4) (by decide),
    twistedE6_mulAutConj_fix (α := e6RootNA5) (β := e6RootA34) (by decide),
    twistedE6_mulAutConj_fix (α := e6RootNA5) (β := e6RootA4) (by decide), mul_one,
    twistedE6_mulAutConj_fix (α := e6RootNA3) (β := e6RootA4) (by decide),
    twistedE6_mulAutConj_fix (α := e6RootNA3) (β := e6RootA45) (by decide),
    twistedE6_mulAutConj_add (α := e6RootNA3) (β := e6RootA34) (γ := e6RootA4) (by decide)]
  have h1 : Commute (pinnedX TwistTag.E6.tag K e6RootA4 (σ δ))
      (pinnedX TwistTag.E6.tag K e6RootA45 1) := twistedE6_commute_pinnedX (by decide) _ _
  have h2 : Commute (pinnedX TwistTag.E6.tag K e6RootA4 (σ δ + δ))
      (pinnedX TwistTag.E6.tag K e6RootA34 1) := twistedE6_commute_pinnedX (by decide) _ _
  have hsum : σ δ + δ + 1 = 0 := by
    rw [add_comm (σ δ), hδ, CharTwo.add_self_eq_zero]
  calc pinnedX TwistTag.E6.tag K e6RootA4 (σ δ) * pinnedX TwistTag.E6.tag K e6RootA45 1 *
          (pinnedX TwistTag.E6.tag K e6RootA4 δ * pinnedX TwistTag.E6.tag K e6RootA34 1) *
          pinnedX TwistTag.E6.tag K e6RootA4 1
        = pinnedX TwistTag.E6.tag K e6RootA45 1 *
            (pinnedX TwistTag.E6.tag K e6RootA4 (σ δ) * pinnedX TwistTag.E6.tag K e6RootA4 δ) *
            pinnedX TwistTag.E6.tag K e6RootA34 1 * pinnedX TwistTag.E6.tag K e6RootA4 1 := by
          rw [h1.eq]
          group
      _ = pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 *
            (pinnedX TwistTag.E6.tag K e6RootA4 (σ δ + δ) * pinnedX TwistTag.E6.tag K e6RootA4 1) := by
          rw [← pinnedX_add, mul_assoc (pinnedX TwistTag.E6.tag K e6RootA45 1), h2.eq]
          group
      _ = _ := by rw [← pinnedX_add, hsum, pinnedX_zero, mul_one]

theorem twistedE6RelWeyl_mulAutConj [CharP K 2] (ω : List (Fin TwistTag.E6.foldedTag.rank))
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : twistedE6TwoRootB β = true) (c : K) :
    MulAut.conj (twistedE6RelWeyl K ω) (pinnedX TwistTag.E6.tag K β c) =
      pinnedX TwistTag.E6.tag K (twistedE6RelAct ω β) c :=
  twistedE6RelWeyl_conj_pinnedX ω (isRoot_iff_twistedE6TwoRootB.2 hβ) c

theorem twistedE6_h1_mem [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) :
    pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have h := twistedE6PairX_mem_graphFixedRootGroup hσσ
    (isRoot_iff_twistedE6TwoRootB.2 (by decide : twistedE6TwoRootB e6RootA3 = true)) (1 : K)
  rwa [twistedE6PairX, show permLattice TwistTag.E6.perm e6RootA3 = e6RootA5 by decide,
    map_one] at h

theorem twistedE6_h2_mem [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x) (δ : K) :
    pinnedX TwistTag.E6.tag K e6RootNA3 δ * pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ) ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have h := twistedE6PairX_mem_graphFixedRootGroup hσσ
    (isRoot_iff_twistedE6TwoRootB.2 (by decide : twistedE6TwoRootB e6RootNA3 = true)) δ
  rwa [twistedE6PairX, show permLattice TwistTag.E6.perm e6RootNA3 = e6RootNA5 by decide] at h

@[expose] def twistedE6WordW1 : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([0, 1, 3, 2, 1, 0, 1, 2, 1, 3] : List (Fin 4))

@[expose] def twistedE6WordW2 : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([0, 1, 2, 1, 0, 3] : List (Fin 4))

@[expose] def twistedE6WordW3 : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([2, 1, 2, 0, 1, 2, 3] : List (Fin 4))

@[expose] def twistedE6WordW4 : List (Fin TwistTag.E6.foldedTag.rank) :=
  ([1, 0, 3, 2, 1, 2, 3] : List (Fin 4))

theorem conj_y1_eq [CharP K 2] (σ : K →+* K) {δ : K} (hδ : δ + σ δ = 1) :
    MulAut.conj ((pinnedX TwistTag.E6.tag K e6RootNA3 δ *
          pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ)) *
        (pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1) *
        twistedE6RelWeyl K twistedE6WordW1)
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1) =
      pinnedX TwistTag.E6.tag K e6RootA45 1 * pinnedX TwistTag.E6.tag K e6RootA34 1 ∧
    MulAut.conj ((pinnedX TwistTag.E6.tag K e6RootNA3 δ *
          pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ)) *
        (pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1) *
        twistedE6RelWeyl K twistedE6WordW1) (pinnedX TwistTag.E6.tag K e6CascC 1) =
      pinnedX TwistTag.E6.tag K e6CascR17 1 := by
  have e1 : MulAut.conj (twistedE6RelWeyl K twistedE6WordW1)
      (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1) =
        pinnedX TwistTag.E6.tag K e6RootA4 1 * pinnedX TwistTag.E6.tag K e6CascC 1 := by
    rw [map_mul, twistedE6RelWeyl_mulAutConj _ (by decide), twistedE6RelWeyl_mulAutConj _ (by decide),
      show twistedE6RelAct twistedE6WordW1 e6HighestRoot = e6RootA4 by decide,
      show twistedE6RelAct twistedE6WordW1 e6CascR17 = e6CascC by decide]
  refine ⟨?_, ?_⟩
  · rw [twistedE6_mulAutConj_mul, twistedE6_mulAutConj_mul, e1, twistedE6_conj_h1,
      twistedE6_conj_h2 σ hδ]
  · rw [twistedE6_mulAutConj_mul, twistedE6_mulAutConj_mul,
      twistedE6RelWeyl_mulAutConj _ (by decide),
      show twistedE6RelAct twistedE6WordW1 e6CascC = e6CascR17 by decide]
    simp only [map_mul, MulAut.mul_apply,
      twistedE6_mulAutConj_fix (α := e6RootA5) (β := e6CascR17) (by decide),
      twistedE6_mulAutConj_fix (α := e6RootA3) (β := e6CascR17) (by decide),
      twistedE6_mulAutConj_fix (α := e6RootNA5) (β := e6CascR17) (by decide),
      twistedE6_mulAutConj_fix (α := e6RootNA3) (β := e6CascR17) (by decide)]

theorem exists_conj_y1_eq_twistedE6ClassU [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {δ : K} (hδ : δ + σ δ = 1) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1) *
        g⁻¹ = twistedE6ClassU K := by
  refine ⟨twistedE6RelWeyl K twistedE6WordW2 * ((pinnedX TwistTag.E6.tag K e6RootNA3 δ *
      pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ)) *
        (pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1) *
        twistedE6RelWeyl K twistedE6WordW1),
    mul_mem (twistedE6RelWeyl_mem σ _) (mul_mem (mul_mem (twistedE6_h2_mem hσσ δ)
      (twistedE6_h1_mem hσσ)) (twistedE6RelWeyl_mem σ _)), ?_⟩
  rw [← MulAut.conj_apply, twistedE6_mulAutConj_mul, (conj_y1_eq σ hδ).1, map_mul,
    twistedE6RelWeyl_mulAutConj _ (by decide), twistedE6RelWeyl_mulAutConj _ (by decide),
    show twistedE6RelAct twistedE6WordW2 e6RootA45 = twistedE6ClassRootU by decide,
    show twistedE6RelAct twistedE6WordW2 e6RootA34 = twistedE6ClassRootU' by decide]
  rfl

theorem exists_conj_y2_eq_twistedE6ClassV [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {δ : K} (hδ : δ + σ δ = 1) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
        pinnedX TwistTag.E6.tag K e6CascC 1) * g⁻¹ = twistedE6ClassV K := by
  refine ⟨twistedE6RelWeyl K twistedE6WordW3 * ((pinnedX TwistTag.E6.tag K e6RootNA3 δ *
      pinnedX TwistTag.E6.tag K e6RootNA5 (σ δ)) *
        (pinnedX TwistTag.E6.tag K e6RootA3 1 * pinnedX TwistTag.E6.tag K e6RootA5 1) *
        twistedE6RelWeyl K twistedE6WordW1),
    mul_mem (twistedE6RelWeyl_mem σ _) (mul_mem (mul_mem (twistedE6_h2_mem hσσ δ)
      (twistedE6_h1_mem hσσ)) (twistedE6RelWeyl_mem σ _)), ?_⟩
  rw [← MulAut.conj_apply, twistedE6_mulAutConj_mul, map_mul (MulAut.conj _) _ (pinnedX _ _ _ _),
    (conj_y1_eq σ hδ).1, (conj_y1_eq σ hδ).2, map_mul, map_mul,
    twistedE6RelWeyl_mulAutConj _ (by decide), twistedE6RelWeyl_mulAutConj _ (by decide),
    twistedE6RelWeyl_mulAutConj _ (by decide),
    show twistedE6RelAct twistedE6WordW3 e6RootA45 = twistedE6ClassRootA by decide,
    show twistedE6RelAct twistedE6WordW3 e6RootA34 = twistedE6ClassRootA' by decide,
    show twistedE6RelAct twistedE6WordW3 e6CascR17 = twistedE6ClassRootB by decide]
  rfl

theorem twistedE6_d4_conj [CharP K 2] :
    (pinnedX TwistTag.E6.tag K e6D4CD 1 * pinnedX TwistTag.E6.tag K e6D4BC 1 *
        pinnedX TwistTag.E6.tag K e6D4AC 1 * pinnedX TwistTag.E6.tag K e6D4BCD 1) *
      (pinnedX TwistTag.E6.tag K e6CascR17 1 * pinnedX TwistTag.E6.tag K e6CascC 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1 * pinnedX TwistTag.E6.tag K e6HighestRoot 1) *
      (pinnedX TwistTag.E6.tag K e6D4CD 1 * pinnedX TwistTag.E6.tag K e6D4BC 1 *
        pinnedX TwistTag.E6.tag K e6D4AC 1 * pinnedX TwistTag.E6.tag K e6D4BCD 1)⁻¹ =
      pinnedX TwistTag.E6.tag K e6CascR17 1 * pinnedX TwistTag.E6.tag K e6CascC 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1 := by
  have cj : ∀ {α β γ : Fin TwistTag.E6.tag.rank → ℤ},
      (twistedE6TwoRootB α && twistedE6TwoRootB β && twistedE6TwoRootB γ &&
        !twistedE6TwoVecB α β && twistedE6TwoVecB (α + β) γ) = true →
      pinnedX TwistTag.E6.tag K α 1 * pinnedX TwistTag.E6.tag K β 1 *
          (pinnedX TwistTag.E6.tag K α 1)⁻¹ =
        pinnedX TwistTag.E6.tag K γ 1 * pinnedX TwistTag.E6.tag K β 1 := fun h => by
    rw [twistedE6_conj_pinnedX_add h, one_mul]
  have cm : ∀ {α β : Fin TwistTag.E6.tag.rank → ℤ},
      (twistedE6TwoRootB α && twistedE6TwoRootB β && !twistedE6TwoVecB α β &&
        !twistedE6TwoVecB (α + β) 0 && !twistedE6TwoRootB (α + β)) = true →
      Commute (pinnedX TwistTag.E6.tag K α 1) (pinnedX TwistTag.E6.tag K β 1) := fun h =>
    twistedE6_commute_pinnedX h 1 1
  exact d4_conj_identity (xa := pinnedX TwistTag.E6.tag K e6CascR17 1)
    (xb := pinnedX TwistTag.E6.tag K e6CascC 1) (xd := pinnedX TwistTag.E6.tag K e6RootA4 1)
    (xac := pinnedX TwistTag.E6.tag K e6D4AC 1) (xbc := pinnedX TwistTag.E6.tag K e6D4BC 1)
    (xcd := pinnedX TwistTag.E6.tag K e6D4CD 1) (xabc := pinnedX TwistTag.E6.tag K e6D4ABC 1)
    (xacd := pinnedX TwistTag.E6.tag K e6D4ACD 1) (xbcd := pinnedX TwistTag.E6.tag K e6D4BCD 1)
    (xabcd := pinnedX TwistTag.E6.tag K e6D4ABCD 1)
    (xθ := pinnedX TwistTag.E6.tag K e6HighestRoot 1)
    (cj (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cj (by decide)) (cj (by decide)) (cm (by decide)) (cm (by decide))
    (cj (by decide)) (cm (by decide)) (cm (by decide)) (cj (by decide)) (cj (by decide))
    (cm (by decide)) (cm (by decide)) (cj (by decide)) (cj (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (cj (by decide)) (cm (by decide)) (cm (by decide))
    (cm (by decide)) (cm (by decide)) (twistedE6_pinnedX_one_mul_self _)
    (twistedE6_pinnedX_one_mul_self _) (twistedE6_pinnedX_one_mul_self _)
    (twistedE6_pinnedX_one_mul_self _) (twistedE6_pinnedX_one_mul_self _)

theorem twistedE6_d4_mem [CharP K 2] (σ : K →+* K) :
    pinnedX TwistTag.E6.tag K e6D4CD 1 * pinnedX TwistTag.E6.tag K e6D4BC 1 *
        pinnedX TwistTag.E6.tag K e6D4AC 1 * pinnedX TwistTag.E6.tag K e6D4BCD 1 ∈
      graphFixedRootGroup TwistTag.E6 K σ := by
  have k : ∀ {β : Fin TwistTag.E6.tag.rank → ℤ}, twistedE6TwoRootB β = true →
      permLattice TwistTag.E6.perm β = β →
      pinnedX TwistTag.E6.tag K β 1 ∈ graphFixedRootGroup TwistTag.E6 K σ := fun hβ hρ =>
    pinnedX_mem_graphFixedRootGroup_of_fixed σ (isRoot_iff_twistedE6TwoRootB.2 hβ) hρ (map_one σ)
  exact mul_mem (mul_mem (mul_mem (k (by decide) (by decide)) (k (by decide) (by decide)))
    (k (by decide) (by decide))) (k (by decide) (by decide))

theorem exists_conj_y3_eq_twistedE6ClassV [CharP K 2] {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    {δ : K} (hδ : δ + σ δ = 1) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
        pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA4 1) * g⁻¹ =
        twistedE6ClassV K := by
  obtain ⟨g₂, hg₂, he₂⟩ := exists_conj_y2_eq_twistedE6ClassV hσσ hδ
  have hr : ∀ γ ∈ ([e6CascR17, e6CascC, e6RootA4] : List (Fin TwistTag.E6.tag.rank → ℤ)),
      Commute (pinnedX TwistTag.E6.tag K e6HighestRoot 1) (pinnedX TwistTag.E6.tag K γ 1) := by
    intro γ hγ
    refine twistedE6_commute_cascade (by decide) ?_ ?_ 1 1
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
      rcases hγ with rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
      rcases hγ with rfl | rfl | rfl <;> decide
  have hy3 : pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
      pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA4 1 =
      pinnedX TwistTag.E6.tag K e6CascR17 1 * pinnedX TwistTag.E6.tag K e6CascC 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1 * pinnedX TwistTag.E6.tag K e6HighestRoot 1 := by
    have h := ((hr e6CascR17 (by simp)).mul_right (hr e6CascC (by simp))).mul_right
      (hr e6RootA4 (by simp))
    calc pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA4 1 =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * (pinnedX TwistTag.E6.tag K e6CascR17 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA4 1) := by group
      _ = _ := h.eq
  have hw4 : MulAut.conj (twistedE6RelWeyl K twistedE6WordW4)
      (pinnedX TwistTag.E6.tag K e6CascR17 1 * pinnedX TwistTag.E6.tag K e6CascC 1 *
        pinnedX TwistTag.E6.tag K e6RootA4 1) =
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
        pinnedX TwistTag.E6.tag K e6CascC 1 := by
    rw [map_mul, map_mul, twistedE6RelWeyl_mulAutConj _ (by decide),
      twistedE6RelWeyl_mulAutConj _ (by decide), twistedE6RelWeyl_mulAutConj _ (by decide),
      show twistedE6RelAct twistedE6WordW4 e6CascR17 = e6HighestRoot by decide,
      show twistedE6RelAct twistedE6WordW4 e6CascC = e6CascR17 by decide,
      show twistedE6RelAct twistedE6WordW4 e6RootA4 = e6CascC by decide]
  refine ⟨g₂ * (twistedE6RelWeyl K twistedE6WordW4 *
      (pinnedX TwistTag.E6.tag K e6D4CD 1 * pinnedX TwistTag.E6.tag K e6D4BC 1 *
        pinnedX TwistTag.E6.tag K e6D4AC 1 * pinnedX TwistTag.E6.tag K e6D4BCD 1)),
    mul_mem hg₂ (mul_mem (twistedE6RelWeyl_mem σ _) (twistedE6_d4_mem σ)), ?_⟩
  rw [← MulAut.conj_apply, twistedE6_mulAutConj_mul, twistedE6_mulAutConj_mul, hy3,
    MulAut.conj_apply (pinnedX TwistTag.E6.tag K e6D4CD 1 * _ * _ * _), twistedE6_d4_conj, hw4,
    MulAut.conj_apply, he₂]

theorem twistedE6Cascade_take_prod :
    ((twistedE6Cascade.take 1).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∧
      ((twistedE6Cascade.take 2).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 ∧
      ((twistedE6Cascade.take 3).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1 ∧
      ((twistedE6Cascade.take 4).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6CascR17 1 *
          pinnedX TwistTag.E6.tag K e6CascC 1 * pinnedX TwistTag.E6.tag K e6RootA4 1 := by
  simp only [twistedE6Cascade_eq, List.take, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, mul_assoc]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem exists_conj_mem_twistedE6Reps_of_cascade_sublist [CharP K 2] {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) {δ : K} (hδ : δ + σ δ = 1)
    {S : List (Fin TwistTag.E6.tag.rank → ℤ)} (hS : S.Sublist twistedE6Cascade) (hS0 : S ≠ []) :
    ∃ g ∈ graphFixedRootGroup TwistTag.E6 K σ,
      g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∨
        g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ = twistedE6ClassU K ∨
          g * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * g⁻¹ = twistedE6ClassV K := by
  obtain ⟨g₁, hg₁, he₁⟩ := exists_conj_cascade_sublist_eq_take σ hS hS0
  have hlen : S.length ≤ 4 := hS.length_le
  have hpos : 0 < S.length := List.length_pos_iff.2 hS0
  obtain ⟨t1, t2, t3, t4⟩ := twistedE6Cascade_take_prod (K := K)
  have comp : ∀ {g₂ y z : ModGL TwistTag.E6.tag K}, g₂ ∈ graphFixedRootGroup TwistTag.E6 K σ →
      ((twistedE6Cascade.take S.length).map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod = y →
      g₂ * y * g₂⁻¹ = z →
      g₂ * g₁ ∈ graphFixedRootGroup TwistTag.E6 K σ ∧
        g₂ * g₁ * (S.map fun γ => pinnedX TwistTag.E6.tag K γ 1).prod * (g₂ * g₁)⁻¹ = z := by
    intro g₂ y z hg₂ hy hz
    refine ⟨mul_mem hg₂ hg₁, ?_⟩
    rw [← hz, ← hy, ← he₁]
    group
  interval_cases h : S.length
  · obtain ⟨hm, he⟩ := comp (one_mem _) t1 (by rw [one_mul, inv_one, mul_one])
    exact ⟨_, hm, Or.inl he⟩
  · obtain ⟨g, hg, hu⟩ := exists_conj_y1_eq_twistedE6ClassU hσσ hδ
    obtain ⟨hm, he⟩ := comp hg t2 hu
    exact ⟨_, hm, Or.inr (Or.inl he)⟩
  · obtain ⟨g, hg, hv⟩ := exists_conj_y2_eq_twistedE6ClassV hσσ hδ
    obtain ⟨hm, he⟩ := comp hg t3 hv
    exact ⟨_, hm, Or.inr (Or.inr he)⟩
  · obtain ⟨g, hg, hv⟩ := exists_conj_y3_eq_twistedE6ClassV hσσ hδ
    obtain ⟨hm, he⟩ := comp hg t4 hv
    exact ⟨_, hm, Or.inr (Or.inr he)⟩

end CFSG.SeitzReduction
