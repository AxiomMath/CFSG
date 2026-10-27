module

public import CFSG.Adapters.TypeALinearCandidate
public import CFSG.Blueprint.Catalog
public import CFSG.ClassicalGroups.Symplectic.Perfect
public import CFSG.LieType.Universal.SymplecticRoots
public import TauCeti.Algebra.Lie.Symplectic.StandardCarrier.FixedPoints
import all TauCeti.Algebra.CharP.Frobenius.Fixed
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Frobenius

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti CFSG.Assembly.LowTwoRank

noncomputable section

def spStdFixedEquiv (n p k : ℕ) [Fact p.Prime] (A : Type) [Field A] [CharP A p] :
    ↥(fixedSubgroup (SpStd.frobenius n p k A)) ≃*
      GLSymplecticFin (n + 1) ↥(frobeniusFixedSubfield A p k) :=
  (SpStd.pointsMulEquivFixedSubgroupFrobenius n p k A).symm.trans
    (SpStd.pointsMulEquivGLSymplecticFin n ↥(frobeniusFixedSubfield A p k))

def spStdCandidateEquivStatedProj (n p k : ℕ) [Fact p.Prime] (A : Type) [Field A] [CharP A p]
    (hperf : Group.IsPerfect ↥(GLSymplecticFin (n + 1) ↥(frobeniusFixedSubfield A p k))) :
    FixedPointCandidate (SpStd.frobenius n p k A) ≃*
      StatedProj (StatedSp (n + 1) ↥(frobeniusFixedSubfield A p k)) :=
  letI := hperf
  (DerivedCentralQuotient.congr (spStdFixedEquiv n p k A)).trans
    ((CFSG.ClassicalModels.derivedCentralQuotientEquivCenterQuotient
        (GLSymplecticFin (n + 1) ↥(frobeniusFixedSubfield A p k))).trans
      ((QuotientGroup.congr _ _
          (CFSG.LieType.Universal.Symplectic.equivStatedSp (n + 1)
            ↥(frobeniusFixedSubfield A p k))
          (Subgroup.map_center_eq _)).trans
        (CFSG.LieType.Universal.Symplectic.centerQuotientEquiv (n + 1)
          ↥(frobeniusFixedSubfield A p k))))

theorem finite_validIndex_fixedField (d : ValidLieTypeIndex) :
    Finite ↥(ValidLieTypeIndex.fixedField d) :=
  inferInstance

def typeCGroupEquivStatedProj (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    ValidLieTypeIndex.Group ⟨.C r q, hv⟩ ≃*
      StatedProj (StatedSp r ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩)) := by
  have hr : 3 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
  cases r with
  | zero => exact absurd hr (by omega)
  | succ m =>
    exact spStdCandidateEquivStatedProj m (ValidLieTypeIndex.characteristic ⟨.C (m + 1) q, hv⟩)
      (ValidLieTypeIndex.fieldExponent ⟨.C (m + 1) q, hv⟩)
      (ValidLieTypeIndex.Closure ⟨.C (m + 1) q, hv⟩)
      ⟨CFSG.ClassicalGroups.Symplectic.commutator_GLSymplecticFin_eq_top_of_three_le _ _ hr⟩

theorem statedClassicalModel_typeC (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    StatedClassicalModel G .PSp r q.p q.exponent := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := hrange.1
  refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_⟩,
    ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩), inferInstance,
    finite_validIndex_fixedField _, ?_, ⟨e.trans (typeCGroupEquivStatedProj r q hv)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    omega
  · rw [ValidLieTypeIndex.card_fixedField]
    simp [ValidLieTypeIndex.fieldOrder]

theorem blueprintCatalog_of_typeC (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid)
    {G : Type} [Group G] (e : G ≃* ValidLieTypeIndex.Group ⟨.C r q, hv⟩) :
    CFSG.Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_typeC r q hv e⟩))

end

end CFSG.QuasithinUnique.SQTK
