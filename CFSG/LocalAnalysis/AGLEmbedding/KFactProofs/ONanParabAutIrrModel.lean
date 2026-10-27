module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.Assembly.LowTwoRank

@[expose] def ClassicalTag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus

theorem classical_model_or_g2 {X : Type} [Group X] (d : TauCeti.ValidLieTypeIndex)
    (hd : IsClassicalOrG2Index d.1) (e : X ≃* (TauCeti.CFSGIndex.lie d).Group) :
    (∃ (t : StatedLieTag) (n f : ℕ), ClassicalTag t ∧ StatedClassicalModel X t n 2 f) ∨
      ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 ∧
        d = ⟨TauCeti.LieTypeIndex.G2 q, hv⟩ := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | A r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    rw [hd] at h
    exact Or.inl ⟨.PSL, _, _, Or.inl rfl, h⟩
  | twistedA r q =>
    change q.p = 2 at hd
    have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at h
    exact Or.inl ⟨.PSU, _, _, Or.inr (Or.inl rfl), h⟩
  | B r q =>
    change q.p = 2 at hd
    have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    by_cases h2 : r = 2
    · subst h2
      have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hd] at h
      exact Or.inl ⟨.PSp, _, _, Or.inr (Or.inr (Or.inl rfl)), h⟩
    · have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hd
        (by omega) e
      rw [hd] at h
      exact Or.inl ⟨.PSp, _, _, Or.inr (Or.inr (Or.inl rfl)), h⟩
  | C r q => exact hd.elim
  | D r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hd e
    rw [hd] at h
    exact Or.inl ⟨.POmegaPlus, _, _, Or.inr (Or.inr (Or.inr (Or.inl rfl))), h⟩
  | twistedD r q =>
    change q.p = 2 at hd
    have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hd e
    rw [hd] at h
    exact Or.inl ⟨.POmegaMinus, _, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), h⟩
  | G2 q =>
    change q.p = 2 at hd
    exact Or.inr ⟨q, hv, hd, rfl⟩
  | _ => exact hd.elim

end CFSG.AGLEmbedding.ParabAutIrr
