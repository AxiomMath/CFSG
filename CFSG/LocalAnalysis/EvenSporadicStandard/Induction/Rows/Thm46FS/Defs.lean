module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.LitStd

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def Sol78Thm46CatFS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → CFSG.Blueprint.Catalog ↥N' →
    ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P →
      ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 n) ∨
        IsSporadic (↥P ⧸ center ↥P) .Suz ∨ IsSporadic (↥P ⧸ center ↥P) .He) →
      (IsSporadic (↥P ⧸ center ↥P) .Suz → Even (Nat.card ↥(center ↥P))) →
        (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .PSL 3 2 (2 * m)) ∨
          (LieModel ↥P .PSL 3 2 2 ∧ IsSporadic ↥N' .Suz) ∨
          (IsKleinFour ↥(center ↥P) ∧ LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧
            IsSporadic ↥N' .He) ∨
          (Nonempty (↥(center ↥P) ≃* Multiplicative (ZMod 4)) ∧
            LieModel (↥P ⧸ center ↥P) .PSL 3 2 2 ∧ IsSporadic ↥N' .ONan ∧ P ≤ N')

@[expose] def Sol78Thm412CatFS : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (N' : Subgroup Y), FStarSimple N' → N'.index ≤ 2 →
    CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y → CFSG.Blueprint.Catalog ↥N' →
    ∀ P : Subgroup Y, SolStd P →
      CFSG.IsQuasisimple ↥P → (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥P ⧸ center ↥P) .G2 0 2 n) →
        (∃ m : ℕ, 2 ≤ m ∧ LieModel ↥N' .G2 0 2 (2 * m)) ∨
          (LieModel ↥P .G2 0 2 2 ∧ IsSporadic ↥N' .Co1)

theorem catalog_or_top {Y : Type} [Group Y] [Finite Y] {N' : Subgroup Y} (hN : FStarSimple N')
    (hidx : N'.index ≤ 2) (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog Y)
    (hcat : ¬ CFSG.Blueprint.Catalog ↥N') : N' = ⊤ := by
  by_contra hne
  apply hcat
  haveI := hN.isSimpleGroup
  exact catalog_of_kProper_of_surjective hkp N' hne ↥N' hN.nonabelian (MonoidHom.id _)
    Function.surjective_id

end CFSG.EvenSporadicStandard.Induction
