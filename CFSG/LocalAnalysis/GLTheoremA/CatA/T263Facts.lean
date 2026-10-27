module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def T263FactGen : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (Ω : Type) [Group Ω] [Finite Ω], CFSG.Open.IsKGroup Ω → ∀ (S B : Subgroup Ω),
    S.Normal → CFSG.Open.IsQuasisimple ↥S → GLAPPrimeCore p ↥S = ⊥ →
    IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S) → S ⊔ B = ⊤ → GLAPPrimeCore p Ω = ⊥ →
    GLAIsBmax p B → 4 ≤ GLATwoLocalRank p Ω →
    (∃ T : Subgroup Ω, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ S ∧ B ≤ Subgroup.normalizer (T : Set Ω)) →
    Nat.card ↥(B ⊓ Subgroup.centralizer (S : Set Ω)) < p ^ 3 →
    (∃ E : Subgroup Ω, E ≤ B ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        GLAPLayer p (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥) ∨
      (p = 3 ∧ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))

theorem layer_centralizes_ne_bot {p : ℕ} (hp : p.Prime) {Ω : Type} [Group Ω] [Finite Ω] {S E : Subgroup Ω}
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hE : E ≤ Subgroup.centralizer (S : Set Ω)) :
    GLAPLayer p (S ⊓ Subgroup.centralizer (E : Set Ω)) ≠ ⊥ := by
  have hSC : S ≤ Subgroup.centralizer (E : Set Ω) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.1 (hE he) s hs).symm
  rw [inf_eq_left.2 hSC]
  have hQ : CFSG.Open.IsQuasisimple (↥S ⧸ GLAPPrimeCore p ↥S) :=
    hSq.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hSp).trans (QuotientGroup.quotientBot (G := ↥S)))
  have hcomp := (glaPLayer_of_isQuasisimple hQ).1
  have hQ2 := isQuasisimple_pQuot_of_glaPComponent hp hcomp
  intro hbot
  rw [hbot] at hQ2
  have hsub : Subsingleton (PQuot p (⊥ : Subgroup Ω)) := by
    constructor
    intro a b
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    congr 1
    exact Subtype.ext ((Subgroup.mem_bot.1 a'.2).trans (Subgroup.mem_bot.1 b'.2).symm)
  have hsub2 : Subsingleton (PQuot p (⊥ : Subgroup Ω) ⧸ Subgroup.center (PQuot p (⊥ : Subgroup Ω))) :=
    (QuotientGroup.mk_surjective).subsingleton
  haveI := hQ2.2
  exact (not_nontrivial_iff_subsingleton.2 hsub2) inferInstance

end CFSG.LocalAnalysis.GLTheoremA.T263

end
