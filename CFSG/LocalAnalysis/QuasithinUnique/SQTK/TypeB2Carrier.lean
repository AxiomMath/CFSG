module

public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeCCarrier
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.SpinAgreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Two.SpinAgreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti CFSG.Assembly.LowTwoRank

noncomputable section

def typeB2GroupEquivStatedProj (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩ ≃*
      StatedProj (StatedSp 2 ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)) :=
  let d : TypeB2LieIndex := TypeB2LieIndex.of q hv
  have hψ : (d.spinEquivCarrier : d.toTypeBLieIndex.AmbientGroup →* d.1.AmbientGroup).comp
        d.toTypeBLieIndex.steinberg =
      d.1.frobenius.comp
        (d.spinEquivCarrier : d.toTypeBLieIndex.AmbientGroup →* d.1.AmbientGroup) :=
    MonoidHom.ext fun g => d.spinEquivCarrier_frobenius g
  have h4 : 4 ≤ Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) := by
    rw [ValidLieTypeIndex.card_fixedField]
    exact d.four_le_fieldOrder
  (FixedPointCandidate.congr d.spinEquivCarrier hψ).trans
    (spStdCandidateEquivStatedProj 1 (ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩)
      (ValidLieTypeIndex.Closure ⟨.B 2 q, hv⟩)
      (CFSG.ClassicalGroups.Symplectic.isPerfect_GLSymplecticFin _ 2 (Or.inl (Or.inr h4))))

theorem statedClassicalModel_typeB2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) :
    StatedClassicalModel G .PSp 2 q.p q.exponent := by
  have h4 : 4 ≤ q.p ^ q.exponent := by
    have := (TypeB2LieIndex.of q hv).four_le_fieldOrder
    simpa [ValidLieTypeIndex.fieldOrder] using this
  refine ⟨⟨q.prime_p, q.exponent_pos, le_rfl, ?_⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩), inferInstance,
    finite_validIndex_fixedField _, ?_, ⟨e.trans (typeB2GroupEquivStatedProj q hv)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]

theorem blueprintCatalog_of_typeB2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) :
    CFSG.Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeB2 q hv e⟩))

end

end CFSG.QuasithinUnique.SQTK
