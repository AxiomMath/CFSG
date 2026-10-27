module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SStdInputs
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolMirror
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Steps

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

@[expose] def L34SuzONanFieldCoreStepMirror : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G → ∀ J : Subgroup G,
    FooteLit.GSMirrorMaximal J → SuzONanFieldType (J ⧸ Open.fusionZStar J) →
    ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype

@[expose] def L34CoreStepMirrorAt (τ : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], L34BaseSetting G → ∀ J : Subgroup G,
    FooteLit.GSMirrorMaximal J → τ (J ⧸ Open.fusionZStar J) →
    ∀ b t : G, orderOf b = 2 → J ≤ centralizer ({b} : Set G) →
      IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))) → orderOf t = 2 →
      b * t = t * b → J ≤ centralizer ({t} : Set G) →
      oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype

@[expose] def L34SuzCoreStepMirror : Prop :=
  L34CoreStepMirrorAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .Suz

@[expose] def L34ONanCoreStepMirror : Prop :=
  L34CoreStepMirrorAt fun X _ => Blueprint.NativeSporadic.IsSporadic X .ONan

@[expose] def L34FieldCoreStepMirror : Prop :=
  L34CoreStepMirrorAt fun X _ => ∃ n : ℕ, 4 ≤ n ∧ Even n ∧ Blueprint.LieModel X .PSL 3 2 n

theorem l34SuzONanFieldCoreStepMirror_of_split (hSuz : L34SuzCoreStepMirror)
    (hON : L34ONanCoreStepMirror) (hField : L34FieldCoreStepMirror) :
    L34SuzONanFieldCoreStepMirror := by
  intro G _ _ hG J hJ hτ b t hb hJb hJp ht hbt hJt
  rcases hτ with h | h | h
  · exact hSuz G hG J hJ h b t hb hJb hJp ht hbt hJt
  · exact hON G hG J hJ h b t hb hJb hJp ht hbt hJt
  · exact hField G hG J hJ h b t hb hJb hJp ht hbt hJt

end CFSG.ComponentClassification.GrSLit.L34Sec5S
