module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Model
public import CFSG.ClassicalInvolution.Asc77.AscT7Z2
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped commutatorElement MatrixGroups

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]


structure ModelLayer (t : StatedLieTag) (k : ℕ) (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Φ : Set (Subgroup G)) where
  ψ : (modelUniv t k p f Fact.out).K →* G
  ker_le : ψ.ker ≤ Subgroup.center (modelUniv t k p f Fact.out).K
  range_eq : ψ.range = omegaGen Φ
  fund : ∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t (modelUniv t k p f Fact.out).D, L = R.map ψ

theorem nonempty_modelLayer_of_omegaLie {Φ : Set (Subgroup G)} (D : OmegaLie p f Φ)
    (hcard : D.card = 1) (i : Fin D.card) {t : StatedLieTag} {k : ℕ} (hit : D.tag i = t)
    (hir : D.rank i = k) (hie : D.exp i = f) : Nonempty (ModelLayer t k p f Φ) := by
  have hsub : Subsingleton (Fin D.card) := by
    rw [hcard]
    infer_instance
  have key : ∀ (t' : StatedLieTag) (k' e : ℕ) (ψ : (modelUniv t' k' p e Fact.out).K →* G),
      t' = t → k' = k → e = f →
      ψ.ker ≤ Subgroup.center (modelUniv t' k' p e Fact.out).K → ψ.range = omegaGen Φ →
      (∀ L ∈ Φ, ∃ R ∈ fundamentalSubgroups t' (modelUniv t' k' p e Fact.out).D,
        L = R.map ψ) → Nonempty (ModelLayer t k p f Φ) := by
    rintro t' k' e ψ rfl rfl rfl hker hr hf
    exact ⟨⟨ψ, hker, hr, hf⟩⟩
  refine key _ _ _ (D.hom i) hit hir hie (D.ker_le_center i) ?_ ?_
  · have h1 : ⨆ j, (D.hom j).range = (D.hom i).range :=
      le_antisymm (iSup_le fun j => by rw [Subsingleton.elim j i])
        (le_iSup (fun j => (D.hom j).range) i)
    rw [← h1]
    exact D.generate
  · intro L hL
    obtain ⟨j, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl : j = i := Subsingleton.elim j i
    exact ⟨R, hR, hLR⟩

namespace ModelLayer

variable {t : StatedLieTag} {k : ℕ} {Φ : Set (Subgroup G)} (P : ModelLayer t k p f Φ)

theorem injOn_fund (hp2 : p ≠ 2) (hadm : StatedLieAdmissible t k p f)
    (hfund : Generic.IsFundTag t) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) {L : Subgroup G}
    {R : Subgroup (modelUniv t k p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t k p f Fact.out).D) (hLR : L = R.map P.ψ)
    (eL : Nonempty (↥L ≃* SL(2, GaloisField p f))) : ∀ x ∈ R, P.ψ x = 1 → x = 1 := by
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2
    hD4 hR
  obtain ⟨e₂⟩ := eL
  have : Finite (modelUniv t k p f Fact.out).K := by
    exact ModelFacts.finite_modelUniv hp2 Fact.out (ih8_isFundTag_mf hfund) hadm
  intro x hx hψ
  refine eq_one_of_map_eq_one_of_card_eq P.ψ ?_ hx hψ
  rw [← hLR]
  exact (Nat.card_congr e₂.toEquiv).trans (Nat.card_congr e₁.toEquiv).symm

end ModelLayer

end T7Z

end CFSG.ClassicalInvolution.Asc77
