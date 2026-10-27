module

public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

set_option linter.unusedSectionVars false

section Descent

variable {τ : Tag} {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]

theorem langDescent_exact (hτ : τ = .G2 ∨ τ = .F4) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (D : LangDatum τ L)
    (hΦ : D.Φ = Units.map (entrywiseHom Fr)) {p : ℕ}
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) :
    LangDescent D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  classical
  have hex := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices τ hτ K L Fr
    hFr).1
  have hfix : D.fix = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hΦ]
    rfl
  set ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype with hι
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype]
  have hfixr : D.fix = ι.range := hfix.trans hrange.symm
  haveI : Finite (ModGL τ K) := finite_modGL
  haveI : Finite (adjointGroup τ K) := inferInstance
  refine ⟨?_, hfixr.ge, fun P hP _ => hfixr ▸ hP, ?_⟩
  · rw [hfixr]
    exact Finite.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  · rw [hfixr, hrange, ← Subgroup.map_commutator, commutator_self_eq_of_commutator_top hperf]

theorem exists_exact_frame (hτ : τ = .G2 ∨ τ = .F4) {p : ℕ} (w : WeylGroup τ)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L) (D : LangDatum τ L)
      (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
      D.q = Nat.card K ∧ D.n = canonicalRep (coxeterSystem τ) L w ∧
      ((Nat.card K : ℕ) : L) = 0 ∧
      LangDescent D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let D : LangDatum τ L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  exact ⟨L, inferInstance, inferInstance, inferInstance, D, Fr, hFr, hD, rfl, rfl, hK0,
    langDescent_exact hτ hFr D hD hperf⟩

end Descent

end CFSG.HardMathSupport.Timmesfeld.LangTorus
