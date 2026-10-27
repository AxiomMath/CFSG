module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviPackage
public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevLeviVacuous
public import CFSG.LieType.ChevTwo.ModelSplit
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevCentralQuotient
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.Chev

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools Subgroup

@[expose] def GomiChevLeviPackageModel (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L U P : Subgroup G) (f : ℕ), LieModel ↥L t n 2 f →
    IsGomiChevTwo ↥L → center ↥L = ⊥ → IsSylowOf 2 U L → L ⊓ normalizer (U : Set G) < P →
    P < L → ¬ IsGomiAtom L U P → ∃ ℳ : Set (Subgroup G), IsGomiLeviPackage L U P ℳ

theorem gomiChevLeviPackageModel_of_gomiAtomsOnlyTop {t : StatedLieTag} {n : ℕ}
    (h : ∀ (X : Type) [Group X] [Finite X] (f : ℕ), LieModel X t n 2 f → GomiAtomsOnlyTop X) :
    GomiChevLeviPackageModel t n := fun _ _ _ L _ _ f hm _ _ hU hBP hPL hat =>
  absurd (isGomiAtom_of_gomiAtomsOnlyTop (h ↥L f hm) hU hBP hPL) hat

theorem gomiChevLeviPackageModel_of_forall_not_admissible {t : StatedLieTag} {n : ℕ}
    (h : ∀ f : ℕ, ¬ StatedLieAdmissible t n 2 f) : GomiChevLeviPackageModel t n :=
  fun _ _ _ _ _ _ f hm _ _ _ _ _ _ => absurd hm.admissible (h f)

theorem gomiChevLeviPackageModel_pOmegaOdd (n : ℕ) : GomiChevLeviPackageModel .POmegaOdd n :=
  gomiChevLeviPackageModel_of_forall_not_admissible fun _ h => h.2.2.2 rfl

theorem gomiChevLeviPackageModel_twistedG2 (n : ℕ) : GomiChevLeviPackageModel .twistedG2 n :=
  gomiChevLeviPackageModel_of_forall_not_admissible fun _ h => absurd h.2.2.2.1 (by decide)

theorem gomiChevLeviPackage_of_models (hsplit : CFSG.LieType.ChevTwo.ChevTwoModelSplit)
    (hmodel : ∀ (t : StatedLieTag) (n : ℕ), t ≠ .Tits → GomiChevLeviPackageModel t n)
    (hTits : ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), LieModel X .Tits n 2 f →
      GomiAtomsOnlyTop X)
    (hA6 : ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* alternatingGroup (Fin 6)) →
      GomiAtomsOnlyTop X)
    (hU33 : ∀ (X : Type) [Group X] [Finite X], StatedClassicalModel X .PSU 3 3 1 →
      GomiAtomsOnlyTop X) :
    GomiChevLeviPackage := by
  intro G _ _ L U P hL hZ hU hBP hPL hat
  have hC : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo ↥L :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.isChevTwo_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hL.isChevTwo
  rcases hsplit ↥L hC with ⟨t, n, f, ht, hm⟩ | ⟨n, f, hm⟩ | he | hm
  · exact hmodel t n ht G L U P f hm hL hZ hU hBP hPL hat
  · exact absurd (isGomiAtom_of_gomiAtomsOnlyTop (hTits ↥L n f hm) hU hBP hPL) hat
  · exact absurd (isGomiAtom_of_gomiAtomsOnlyTop (hA6 ↥L he) hU hBP hPL) hat
  · exact absurd (isGomiAtom_of_gomiAtomsOnlyTop (hU33 ↥L hm) hU hBP hPL) hat

end CFSG.GroupTheory
