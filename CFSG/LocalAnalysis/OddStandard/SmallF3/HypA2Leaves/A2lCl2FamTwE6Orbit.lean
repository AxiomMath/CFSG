module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTwE6Desc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamTwE6Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamE6Inv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamPSL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl2FamOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofTwE6Descent

public noncomputable section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG
  CFSG.ComponentClassification.CatLeafProof
  CFSG.ComponentClassification
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley CFSG.ComponentClassification.CatLeaf
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem cl24_e6_twisted_zero
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 0)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = D.e ∨ f' = 2 * D.e ∨ f' = 4 * D.e → Rel f' := by cl24_rel) :
    Cl24Q p Rel (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6SimpleRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_zero
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_zero hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact (cl24_e6_twisted_orbitGroup D (Or.inl rfl) hχ hθ J' hq hJS ⟨0, rfl⟩
      fun K₂ _ _ hK₂ _ hα _ hL => cl24_E6_involution hp D.odd hadm
        (lieModel_pairSpan_e6Simple hp D.odd hK₂) hα hL).mono
        fun f' h => hRel f' (by omega)

end

section


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem cl24_e6_twisted_twenty
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 20)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = D.e ∨ f' = 2 * D.e ∨ f' = 4 * D.e → Rel f' := by cl24_rel) :
    Cl24Q p Rel (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .POmegaPlus 5 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num⟩
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e6D5TwRoot := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e6_twenty
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (fun i => e6_simple_inter_twenty hχ i)
    with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact (cl24_e6_twisted_orbitGroup D (Or.inr (Or.inl rfl)) hχ hθ J' hq hJS
      ⟨3, rfl⟩ fun K₂ _ _ hK₂ _ hα _ hL => cl24_omegaPlus_involution hp D.odd
        hadm (lieModel_pairSpan_e6D5Tw hp D.odd hK₂) hα hL).mono
        fun f' h => hRel f' (by omega)

end

section


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem cl24_e6_two_theta
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    (hJS : (D.withOrbit J').simpleRootsJ = {hiE6})
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = D.e → Rel f' := by cl24_rel) :
    Cl24Q p Rel (D.withOrbit J').orbitGroup := by
  have hfix : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ (toReal β) = toReal β := by
    intro β hβ
    rw [hJS, Set.mem_singleton_iff] at hβ
    subst hβ
    change D.θ _ = _
    rw [hθ, thetaMap_e6_hiE6]
  have horb := orbitGroup_eq_map_pairSpan (D.withOrbit J') hfix
  rw [hJS] at horb
  have hK : Nat.card (frobeniusFixedField k p D.e) = p ^ D.e :=
    card_frobeniusFixedField D.one_le_e
  have : Finite (frobeniusFixedField k p D.e) :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let e : (D.withOrbit J').orbitGroup ≃* pairSpan .E6 (frobeniusFixedField k p D.e) {hiE6} :=
    (MulEquiv.subgroupCongr horb).trans
      ((Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective _)).symm)
  exact cl24_of_mulEquiv e
    (cl24_pairSpan_hiE6 (Fact.out : p.Prime) D.odd hK
      (LocalCores.isQuasisimple_of_mulEquiv e hq))

end

section


variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem cl24_e6_twisted_two
    (D : OrthogonalSemilinearFixedRootDatum .E6 p k) (hχ : D.χ = signMaskChar .E6 2)
    (hθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (ToralSign.wordElt .E6 []) TwistTag.E6.perm γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {Rel : ℕ → Prop} (hRel : ∀ f', f' = D.e ∨ f' = 2 * D.e ∨ f' = 4 * D.e → Rel f' := by cl24_rel) :
    Cl24Q p Rel (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .PSL 6 p (D.e * 2) :=
    ⟨hp, by have := D.one_le_e; omega, by norm_num, by simp, by simp⟩
  rcases e6_two_simpleRootsJ D hχ hθ J' with h0 | hA | hT
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  · exact (cl24_e6_twisted_orbitGroup D (Or.inr (Or.inr rfl)) hχ hθ J' hq hA
      ⟨0, rfl⟩ fun K₂ _ _ hK₂ _ hα _ hL => cl24_psl_involution hp D.odd hadm
        (lieModel_pairSpan_e6A5 hp D.odd hK₂) hα hL).mono
        fun f' h => hRel f' (by omega)
  · exact cl24_e6_two_theta D hθ J' hq hT

end

end CFSG.OddStandard.SmallF3.HypA2Leaves
