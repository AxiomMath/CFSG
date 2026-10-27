module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockAnCatalogue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockInnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUBlockInnAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInSpTransFactor
public import CFSG.HardMathSupport.Dickson.BMRows.CensusShape
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hb
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13d
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13e
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma13g
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ConstrainedGen
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8140
public import Certificates.Certificate8141

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.OuterAutomorphisms

structure LinBlockModel (p : ℕ) {S : Type} [Group S] (J : Subgroup S) (y : S)
    (hN : y ∈ Subgroup.normalizer (J : Set S)) where
  a : ℕ
  E : Type
  fieldE : Field E
  finiteE : Finite E
  charE : (2 : E) = 0
  two_le : 2 ≤ a
  k : ℕ
  cardE : Nat.card E = 2 ^ k
  notSmall : a = 2 → 3 ≤ k
  h3 : a = 3 → 2 ≤ k
  h4 : a = 4 → 2 ≤ k
  B : GL (Fin a) E
  hBn : B ∈ Subgroup.normalizer
    (StatedSL a E : Set (GL (Fin a) E))
  Bpow : B ^ p = 1
  e : PSimple p J ≃* LargeEvenProj (StatedSL a E)
  equiv : ∀ m : ↥(StatedSL a E),
    MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN)
        (LargeEvenProjMk (StatedSL a E) m) =
      LargeEvenProjMk (StatedSL a E)
        ⟨B * (m : GL (Fin a) E) * B⁻¹,
          ((Subgroup.mem_normalizer_iff.mp hBn) (m : GL (Fin a) E)).mp m.2⟩

theorem linBlockModel_analysis {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Type} [Group S] {J : Subgroup S} {y : S}
    {hN : y ∈ Subgroup.normalizer (J : Set S)} (h : LinBlockModel p J y hN) :
    catalogIs (PSimple p J) (onLie isLinearCharTwoIdx) ∧
      CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN ∈ innAutDerived (PSimple p J) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Field h.E := h.fieldE
  letI : Finite h.E := h.finiteE
  have hcat : catalogIs (LargeEvenProj (StatedSL h.a h.E)) (onLie isLinearCharTwoIdx) :=
    catalogIs_largeEvenProj_statedSL h.cardE h.two_le h.notSmall h.h3 h.h4
  have hmem : TableB.projConj (StatedSL h.a h.E) ⟨h.B, h.hBn⟩ ∈
      innAutDerived (LargeEvenProj (StatedSL h.a h.E)) :=
    innAutDerived_projConj_statedSL hp hp2 h.B h.hBn h.Bpow
  have hconj : MulAut.congr h.e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J y hN) =
      TableB.projConj (StatedSL h.a h.E) ⟨h.B, h.hBn⟩ := by
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin h.a) h.E).subgroupOf (StatedSL h.a h.E)) x
    conv_rhs => rw [QuotientGroup.mk'_apply, TableB.projConj_mk]
    rw [h.equiv m, QuotientGroup.mk'_apply]
    congr 1
  refine ⟨CFSG.HardMathSupport.Dickson.BMRows.catalogIs_of_mulEquiv _ _ h.e.symm hcat, ?_⟩
  exact (mem_innAutDerived_congr h.e).mp (by rw [hconj]; exact hmem)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
