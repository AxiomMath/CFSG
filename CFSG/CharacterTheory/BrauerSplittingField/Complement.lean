module

public import CFSG.CharacterTheory.BrauerSplittingField.DirectDescent
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Iso
public import Mathlib.Combinatorics.Quiver.ReflQuiver

public section

namespace CFSG

open CategoryTheory CategoryTheory.Limits

namespace BrauerSplittingField.Helpers

noncomputable section

universe u

lemma exists_injective_fdrep_hom_of_baseChange
    {K L G : Type u}
    [Field K] [Field L] [Algebra K L] [Infinite K] [CharZero L]
    [Group G] [Fintype G]
    (N P : FDRep K G)
    (j : FDRep.baseChange (A := L) N ⟶ FDRep.baseChange (A := L) P)
    (hj : Function.Injective (FDRep.homToLinearMap j)) :
    ∃ q : N ⟶ P, Function.Injective (FDRep.homToLinearMap q) := by
  let jr :
      (baseChangeRep (A := L) N.ρ).IntertwiningMap
      (baseChangeRep (A := L) P.ρ) :=
    { toLinearMap := FDRep.homToLinearMap j
      isIntertwining' := by
        intro g
        exact FDRep.hom_comp_ρ j g }
  obtain ⟨q, hq⟩ :=
    exists_injective_intertwiningMap_of_baseChange N.ρ P.ρ jr hj
  let m : N ⟶ P := FDRep.homOfLinearMap q.toLinearMap q.isIntertwining'
  refine ⟨m, ?_⟩
  change Function.Injective q.toLinearMap
  exact hq

lemma exists_character_complement
    {K G : Type u} [Field K] [Group G] [Finite G] [CharZero K]
    (N P : FDRep K G) (j : N ⟶ P)
    (hj : Function.Injective (FDRep.homToLinearMap j)) :
    ∃ W : FDRep K G, P.character = N.character + W.character := by
  have : Mono j := (FDRep.mono_iff_injective j).2 hj
  have : NeZero (Nat.card G : K) :=
    ⟨One.natCast_natCard_ne_zero_of_finite G K⟩
  let sj : SplitMono j := FDRep.splitMono_of_mono j
  obtain ⟨e⟩ := FDRep.exists_iso_biprod_of_splitMono j sj
  refine ⟨cokernel j, ?_⟩
  simpa only [FDRep.char_biprod_eq_add] using FDRep.char_eq_of_iso e

noncomputable def baseChangeComplementIso
    {K L G : Type u}
    [Field K] [Field L] [Algebra K L]
    [Group G] [Finite G] [CharZero L] [IsAlgClosed L]
    (V : FDRep L G) (N P W : FDRep K G)
    (hvirtual :
      (V ⊞ FDRep.baseChange (A := L) N).character =
        (FDRep.baseChange (A := L) P).character)
    (hcomplement : P.character = N.character + W.character) :
    FDRep.baseChange (A := L) W ≅ V := by
  apply FDRep.iso_of_char_eq
  ext g
  have hv := congrFun hvirtual g
  have hc := congrArg (algebraMap K L) (congrFun hcomplement g)
  simp only [FDRep.char_biprod_eq_add, Pi.add_apply, FDRep.baseChange_character,
    map_add] at hv hc ⊢
  rw [hc] at hv
  have hv' :
      algebraMap K L (N.character g) + V.character g =
        algebraMap K L (N.character g) + algebraMap K L (W.character g) :=
    (add_comm _ _).trans hv
  exact (add_left_cancel hv').symm

end

end BrauerSplittingField.Helpers

end CFSG
