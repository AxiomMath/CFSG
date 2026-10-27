module

public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryCarrier
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import all TauCeti.LinearAlgebra.RootSystem.DynkinType

public section

namespace CFSG.QuasithinUnique.SQTK

open TauCeti CFSG.Assembly.LowTwoRank

noncomputable section

theorem specialLinearSteinberg_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    (TypeALieIndex.ofTwistedA r q hv).specialLinearSteinberg =
      unitarySteinberg r (TypeALieIndex.ofTwistedA r q hv).1.characteristic
        (TypeALieIndex.ofTwistedA r q hv).1.fieldExponent
        (TypeALieIndex.ofTwistedA r q hv).1.Closure := by
  rw [TypeALieIndex.specialLinearSteinberg, TypeALieIndex.specialLinearGraphAut_ofTwistedA]
  rfl

def typeTwistedAGroupEquivStatedProj (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩ ≃*
      StatedProj (StatedSU (r + 1)
        (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
          ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩)
        (GaloisField (ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩)
          (2 * ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩))) :=
  let d := TypeALieIndex.ofTwistedA r q hv
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hdup := ((LieTypeIndex.valid_iff _).1 hv).2
  have hr : 2 ≤ r := hrange.1
  have hk : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ ≠ 0 :=
    (ValidLieTypeIndex.fieldExponent_pos _).ne'
  have hnq : (r + 1, ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ ^
      ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩) ≠ (3, 2) := by
    intro h
    simp only [Prod.mk.injEq] at h
    have h3 := hrange.2 (by omega)
    have h2 : q.p ^ q.exponent = 2 := h.2
    simp only [PrimePower.card_def] at h3
    omega
  have hψ : (d.carrierEquivSpecialLinear : d.AmbientGroup →* d.StandardGroup).comp d.steinberg =
      (unitarySteinberg r d.1.characteristic d.1.fieldExponent d.1.Closure).comp
        (d.carrierEquivSpecialLinear : d.AmbientGroup →* d.StandardGroup) := by
    refine MonoidHom.ext fun g => ?_
    have key := d.carrierEquivSpecialLinear_steinberg g
    rw [specialLinearSteinberg_ofTwistedA r q hv] at key
    exact key
  (FixedPointCandidate.congr d.carrierEquivSpecialLinear hψ).trans
    (unitaryCandidateEquivStatedProj hk (by omega) hnq)

theorem statedClassicalModel_twistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    StatedClassicalModel G .PSU (r + 1) q.p q.exponent := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hr : 2 ≤ r := hrange.1
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine ⟨⟨q.prime_p, q.exponent_pos, by omega, ?_⟩, GaloisField q.p (2 * q.exponent),
    inferInstance, inferInstance, ?_, ⟨e.trans (typeTwistedAGroupEquivStatedProj r q hv)⟩⟩
  · intro h
    simp only [Prod.mk.injEq] at h
    have h3 := hrange.2 (by omega)
    simp only [PrimePower.card_def] at h3
    omega
  · rw [GaloisField.card q.p (2 * q.exponent) (by have := q.exponent_pos; omega), pow_mul']

theorem blueprintCatalog_of_twistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) {G : Type} [Group G]
    (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) : CFSG.Blueprint.Catalog G :=
  Or.inr (Or.inr (Or.inl ⟨_, _, _, _, statedClassicalModel_twistedA r q hv e⟩))

end

end CFSG.QuasithinUnique.SQTK
