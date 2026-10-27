module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FExc
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33All
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33Alt
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33NonB

public section

namespace CFSG.ComponentClassification.HarrisLit.L33

open CFSG Subgroup Assembly.LowTwoRank

@[expose] def L33For' (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], C Y → HarrisF 3 Y →
    (∃ (Q : Type) (_ : Group Q) (_ : Finite Q), IsQuasisimple Q ∧ center Q ≠ ⊥ ∧
      IsPGroup 2 ↥(center Q) ∧ Nonempty (Q ⧸ center Q ≃* Y)) →
    ∀ a : MulAut Y, orderOf a = 2 →
      IsPGroup 2 (↥(fixedPoints a) ⧸ pPrimeCore 2 ↥(fixedPoints a)) →
        ∃ m : ℕ, 2 ≤ m ∧ Blueprint.LieModel Y .PSL 2 3 m

theorem harris81Lemma33Simple_of_rows'
    (hA : L33For' fun Y _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (Y ≃* alternatingGroup (Fin n)))
    (hC : L33For' fun Y _ => Milestones.ClassicalRep Y)
    (hE : L33For' fun Y _ => Blueprint.ExceptionalRep Y)
    (hS : L33For' fun Y _ => Blueprint.NativeSporadic.SporadicRep Y) :
    Harris81Lemma33Simple := by
  intro Y _ _ hY hcov a ha hP
  rcases C311.catalog_of_harrisF hY with ⟨q, -, ⟨e⟩⟩ | hY' | hY' | hY' | hY'
  · obtain ⟨x, y, hxy⟩ := C311.nonabelian_of_harrisF hY
    exact (hxy (e.injective (by rw [map_mul, map_mul, mul_comm]))).elim
  · exact hA Y hY' hY hcov a ha hP
  · exact hC Y hY' hY hcov a ha hP
  · exact hE Y hY' hY hcov a ha hP
  · exact hS Y hY' hY hcov a ha hP

theorem l33For'_of_twoNilpFor'
    (hGA : TBLit.GriessMultipliersAllModels) {C : (Y : Type) → [Group Y] → Prop}
    (h : TwoNilpFor' C) : L33For' C := by
  intro Y _ _ hC hY hcov a ha hP
  rcases h Y hC (isSimpleGroup_of_harrisF hY) (C311.nonabelian_of_harrisF hY) a ha hP with
    hexc | ⟨f, hf, hm⟩
  · exact l33For_of_twoNilpFor (C := fun Y _ => IsTwoNilpExc Y)
      (fun _ _ _ hE _ _ _ _ _ => hE) Y hexc hY a ha hP
  · exfalso
    obtain ⟨Q, _, _, hQ, hZ1, hZ, ⟨e⟩⟩ := hcov
    obtain ⟨h1, h2, h3, h4⟩ := odd_orders_psp_two_two hf
    exact hZ1 (GH74.Generic.noTwoCover_of_griess hGA
      (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hm) h1 h2 h3 h4 Q hQ hZ ⟨e⟩)

theorem twoNilpFor_exceptionalRep'
    (hChev : TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel Y t p f)
    (hRee : TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.reeTitsTags ∧ Blueprint.ReeTitsModel Y t p f) :
    TwoNilpFor' fun Y _ => Blueprint.ExceptionalRep Y :=
  (hChev.or (hRee.or twoNilpFor_suzuki.weaken)).mono fun _ _ hY => hY

theorem twoNilpFor_sporadicRep'
    (h : ∀ s : TauCeti.SporadicName,
      TwoNilpFor' fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s) :
    TwoNilpFor' fun Y _ => Blueprint.NativeSporadic.SporadicRep Y := by
  intro Y _ _ hY
  obtain ⟨s, hs⟩ := hY
  exact h s Y hs

theorem harris81Lemma33Simple_of_twoNilp'
    (hGA : TBLit.GriessMultipliersAllModels)
    (hOdd : TwoNilpFor' fun Y _ => ∃ t n p f, p ≠ 2 ∧ StatedClassicalModel Y t n p f)
    (hTwo : TwoNilpFor' fun Y _ => ∃ t n f, StatedClassicalModel Y t n 2 f)
    (hChev : TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.chevalleyExceptionalTags ∧ Blueprint.ChevalleyExceptionalModel Y t p f)
    (hRee : TwoNilpFor' fun Y _ => ∃ (t : StatedLieTag) (p f : ℕ),
      t ∈ Blueprint.reeTitsTags ∧ Blueprint.ReeTitsModel Y t p f)
    (hSpor : ∀ s : TauCeti.SporadicName,
      TwoNilpFor' fun Y _ => Blueprint.NativeSporadic.IsSporadic Y s) :
    Harris81Lemma33Simple :=
  harris81Lemma33Simple_of_rows' (l33For'_of_twoNilpFor' hGA twoNilpFor_alt.weaken)
    (l33For'_of_twoNilpFor' hGA (twoNilpFor_classicalRep' hOdd hTwo))
    (l33For'_of_twoNilpFor' hGA (twoNilpFor_exceptionalRep' hChev hRee))
    (l33For'_of_twoNilpFor' hGA (twoNilpFor_sporadicRep' hSpor))

end CFSG.ComponentClassification.HarrisLit.L33
