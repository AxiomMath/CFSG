module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityActions
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality
open CFSG.BenderSuzuki.PFchapter1section1

universe u v w x

variable {G : Type u} {F : Type v} {Ω : Type w} {Ξ : Type x}
variable [Group G] [Group F]

theorem quotient_stabilizer_identification_smul {A B : Subgroup G}
    (h : A = B) (g : G) (z : G ⧸ A) :
    Subgroup.quotientEquivOfEq h (g • z) =
      g • Subgroup.quotientEquivOfEq h z := by
  induction z using Quotient.inductionOn with
  | h z => rfl

theorem transitive_action_equiv_of_stabilizer_eq
    [MulAction G Ω] [MulAction G Ξ]
    (hΩ : MulAction.IsPretransitive G Ω) (hΞ : MulAction.IsPretransitive G Ξ)
    (a : Ω) (b : Ξ) (hstab : MulAction.stabilizer G a = MulAction.stabilizer G b) :
    ∃ f : Ω ≃ Ξ, f a = b ∧ ∀ (g : G) (z : Ω), f (g • z) = g • f z := by
  let eΩ := actionCosetEquiv hΩ a
  let eΞ := actionCosetEquiv hΞ b
  let q := Subgroup.quotientEquivOfEq hstab
  let f : Ω ≃ Ξ := eΩ.symm.trans (q.trans eΞ)
  have hf (g : G) : f (g • a) = g • b := by
    have heΩ : eΩ (QuotientGroup.mk g) = g • a := actionCosetEquiv_mk hΩ a g
    rw [← heΩ]
    simp only [f, Equiv.trans_apply, Equiv.symm_apply_apply, q,
      Subgroup.quotientEquivOfEq_mk]
    exact actionCosetEquiv_mk hΞ b g
  refine ⟨f, ?_, ?_⟩
  · simpa only [one_smul] using hf 1
  · intro g z
    obtain ⟨k, rfl⟩ := hΩ.exists_smul_eq a z
    rw [← mul_smul, hf, hf, mul_smul]

theorem transitive_action_equiv_of_stabilizer_map
    [MulAction G Ω] [MulAction F Ξ]
    (hΩ : MulAction.IsPretransitive G Ω) (hΞ : MulAction.IsPretransitive F Ξ)
    (e : G ≃* F) (a : Ω) (b : Ξ)
    (hstab : (MulAction.stabilizer G a).map e.toMonoidHom = MulAction.stabilizer F b) :
    ∃ f : Ω ≃ Ξ, f a = b ∧ ∀ (g : G) (z : Ω), f (g • z) = e g • f z := by
  let : MulAction G Ξ := MulAction.compHom Ξ e.toMonoidHom
  have htrans : MulAction.IsPretransitive G Ξ := by
    constructor
    intro z z'
    obtain ⟨k, hk⟩ := hΞ.exists_smul_eq z z'
    exact ⟨e.symm k, by change e (e.symm k) • z = z'; simpa using hk⟩
  have hsame : MulAction.stabilizer G a = MulAction.stabilizer G b := by
    ext g
    change g ∈ MulAction.stabilizer G a ↔ e g • b = b
    rw [← MulAction.mem_stabilizer_iff, ← hstab]
    simp
  exact transitive_action_equiv_of_stabilizer_eq hΩ htrans a b hsame

theorem strong_embedding_adjust_isomorphism [Finite G] [Finite F]
    (hrank : TwoRankAtLeastTwo F) (H : Subgroup G) (B : Subgroup F)
    (hH : fusionStronglyEmbedded H) (hB : fusionStronglyEmbedded B) (e : G ≃* F) :
    ∃ E : G ≃* F, H.map E.toMonoidHom = B := by
  obtain ⟨g, hg⟩ := rank_two_strongEmbedding_conjugate hrank
    (H.map e.toMonoidHom) B (hH.map_mulEquiv e) hB
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_⟩
  rw [Subgroup.map_map] at hg
  change H.map ((MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom) = B
  exact hg

theorem strong_embedding_transitive_action_identification
    [Finite G] [Finite F] [MulAction G Ω] [MulAction F Ξ]
    (hrank : TwoRankAtLeastTwo F)
    (hΩ : MulAction.IsPretransitive G Ω) (hΞ : MulAction.IsPretransitive F Ξ)
    (a : Ω) (b : Ξ)
    (ha : fusionStronglyEmbedded (MulAction.stabilizer G a))
    (hb : fusionStronglyEmbedded (MulAction.stabilizer F b)) (e : G ≃* F) :
    ∃ (E : G ≃* F) (f : Ω ≃ Ξ),
      (MulAction.stabilizer G a).map E.toMonoidHom = MulAction.stabilizer F b ∧
      f a = b ∧ ∀ (g : G) (z : Ω), f (g • z) = E g • f z := by
  obtain ⟨E, hE⟩ := strong_embedding_adjust_isomorphism hrank _ _ ha hb e
  obtain ⟨f, hf, hequiv⟩ := transitive_action_equiv_of_stabilizer_map hΩ hΞ E a b hE
  exact ⟨E, f, hE, hf, hequiv⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
