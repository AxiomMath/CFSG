module

public import CFSG.ClassicalInvolution.Q3.TL4StepNoTri
public import CFSG.ClassicalInvolution.Q3.TL4OddMu9L
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Defs

variable {Y : Type} [Group Y]

abbrev linkFam (R : Subgroup Y) (t : Y) : Set (Subgroup ↥(linkGrp R t)) :=
  restrictFamily (coreLinkFam R t) (linkGrp R t)

@[expose] def LinkTrans (R : Subgroup Y) (t : Y) : Prop :=
  ∀ L ∈ linkFam R t, ∀ L' ∈ linkFam R t, ∃ g : ↥(linkGrp R t), conjSub g L = L'

end Defs

section Cit3


@[expose] def TightLinkTransR (r n : ℕ) : Prop :=
  Thm4RBelow r n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → ¬ DConnected (linkFam R t) → LinkTrans R t

@[expose] def TightLinkDiscR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → ¬ DConnected (linkFam R t)

@[expose] def TightLinkDatumR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkTrans R t →
        ∃ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 R') (t' : ↥(linkGrp R t)),
          TightDatum R' S' t' ∧ TightCls ↥(linkGrp R t) R' S' t' ∧
            CoreAssembly.conjClass (tightCore R') = linkFam R t

@[expose] def TightLinkE2R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkTrans R t → ¬ DConnected (linkFam R t) →
      ∀ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 R') (t' : ↥(linkGrp R t)),
        TightDatum R' S' t' → TightCls ↥(linkGrp R t) R' S' t' →
        CoreAssembly.conjClass (tightCore R') = linkFam R t → TightInO2 t' →
          LinkS3S4 R t ∨ LinkAEAt R t

@[expose] def TightLinkExitR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkTrans R t → ¬ DConnected (linkFam R t) →
      ∀ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 R') (t' : ↥(linkGrp R t)),
        TightDatum R' S' t' → TightCls ↥(linkGrp R t) R' S' t' →
        CoreAssembly.conjClass (tightCore R') = linkFam R t → ¬ TightInO2 t' →
        ((TightEdgeless R' ∧ ¬ TightActs3 R' t' ∧
            (Thm6Exit ↥(linkGrp R t) ∨ TightTwisted ↥(linkGrp R t) t')) ∨
          (TightEdgeless R' ∧ Nonempty (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t) ≃*
            NativeSporadic.Carrier .M12))) →
          LinkS3S4 R t

@[expose] def TightLinkE4R (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkTrans R t → ¬ DConnected (linkFam R t) →
      ∀ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 R') (t' : ↥(linkGrp R t)),
        TightDatum R' S' t' → TightCls ↥(linkGrp R t) R' S' t' →
        CoreAssembly.conjClass (tightCore R') = linkFam R t → ¬ TightInO2 t' →
        Subgroup.center ↥(linkGrp R t) ≠ ⊥ →
        (LieModel (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t)) .PSp 3 2 1 ∨
          LieModel (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t)) .POmegaPlus 4 2 1) →
          LinkS3S4 R t

@[expose] def TightLinkLieR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightLargeHypR r n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
      ¬ TriNbrAll R t → LinkAlphaBad R t → LinkTrans R t → ¬ DConnected (linkFam R t) →
      ∀ (R' : Subgroup ↥(linkGrp R t)) (S' : Sylow 2 R') (t' : ↥(linkGrp R t)),
        TightDatum R' S' t' → TightCls ↥(linkGrp R t) R' S' t' →
        CoreAssembly.conjClass (tightCore R') = linkFam R t → ¬ TightInO2 t' →
        SecIdLie3 R' t' →
          LinkS3S4 R t ∨ LinkE4 R t

variable {n : ℕ}

theorem tightLinkCasesR_of (htr : TightLinkTransR 3 n) (hdisc : TightLinkDiscR 3 n)
    (hdat : TightLinkDatumR 3 n) (he2 : TightLinkE2R 3 n) (hex : TightLinkExitR 3 n)
    (he4 : TightLinkE4R 3 n) (hlie : TightLinkLieR 3 n) (h4 : Thm4RBelow 3 n)
    (hA : CIT3Below n) (hP : TightBelowRPlus 3 n) : TightLinkCasesR 3 n := by
  intro Y _ _ R S t hL hc hT hα
  have hnc := hdisc Y R S t hL hc hT hα
  have hT' := htr h4 Y R S t hL hc hT hnc
  obtain ⟨R', S', t', hd', hc', heq⟩ := hdat Y R S t hL hc hT hT'
  have hlt : Nat.card ↥(linkGrp R t) < n := by
    have hz := hL.datum.isUniqueInvolution_core
    have hx : ∃ g : Y, g * t ≠ t * g := by
      by_contra hcon
      have htc : t ∈ Subgroup.center Y :=
        Subgroup.mem_center_iff.mpr fun g => by
          by_contra h
          exact hcon ⟨g, h⟩
      rw [hL.center, Subgroup.mem_bot] at htc
      exact hz.ne_one htc
    exact (Subgroup.card_le_card_group _).trans_lt
      ((natCard_secQuot_lt (Ω := CoreAssembly.conjClass (tightCore R)) hx).trans_eq hL.card)
  by_cases hO2 : TightInO2 t'
  · rcases he2 Y R S t hL hc hT hT' hnc R' S' t' hd' hc' heq hO2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  rcases secIdentDatum3_of hP hA ↥(linkGrp R t) hlt R' S' t' hd' hc' with
    h2 | h3a | h3b | ⟨hZ, hE4⟩ | hLie
  · exact absurd h2 hO2
  · exact Or.inl (hex Y R S t hL hc hT hα hT' hnc R' S' t' hd' hc' heq hO2 (Or.inl h3a))
  · exact Or.inl (hex Y R S t hL hc hT hα hT' hnc R' S' t' hd' hc' heq hO2 (Or.inr h3b))
  · exact Or.inl (he4 Y R S t hL hc hT hα hT' hnc R' S' t' hd' hc' heq hO2 hZ hE4)
  · rcases hlie Y R S t hL hc hT hα hT' hnc R' S' t' hd' hc' heq hO2 hLie with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
