module

public import CFSG.GH74.GLS.TwoThin.Basic
public import CFSG.GH74.GLS.Stage2.Local.Concl

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

@[expose] def Lemma31NarrowConcl {G : Type} [Group G] (z : G) (H J R : Subgroup G) : Prop :=
  (IsCyclic ↥R ∨ IsQuat ↥R ∨ IsDihedral ↥R) ∧
  (IsDihedral ↥R → (Nonempty (Hat J ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 (Hat J) Odd)) ∧
  (J ≤ pLayerOf 2 H → J ≠ pLayerOf 2 H →
    ∃ K₁ K₂ : Subgroup (HBar H), K₁ ⊔ K₂ = barIn H (pLayerOf 2 H) ∧
      (∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) ∧
      (Group.IsSolvable ↥K₁ ∨ IsQuasisimple ↥K₁) ∧ (Group.IsSolvable ↥K₂ ∨ IsQuasisimple ↥K₂)) ∧
  ((NativeSporadic.IsSporadic (Hat J) .M11 ∨
      ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ (Odd (p ^ f) ∨ p ^ f = 4) ∧
        (LieModel (Hat J) .PSL 3 p f ∨ LieModel (Hat J) .PSU 3 p f)) →
    NativeSporadic.IsSporadic (Hat J) .M11 ∧ IsDoubleCoverOfAlt (CentralizerBar z) 11)

@[expose] def Lemma31Narrow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J R : Subgroup G, H ≠ ⊤ → IsPCompIn 2 H J →
      CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)) → R ≠ ⊥ →
      Lemma31NarrowConcl z H J R

theorem not_isSolvable_of_isPCompIn {G : Type} [Group G] [Finite G] {H J : Subgroup G}
    (hJ : IsPCompIn 2 H J) : ¬ Group.IsSolvable ↥J := by
  intro hsol
  obtain ⟨hperf, hsimp, -⟩ := TwoThin.isQuasisimple_hat hJ
  have hsolQ : Group.IsSolvable (↥J ⧸ pPrimeCore 2 ↥J) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥J))
      (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) := hsimp
  have hnt : Nontrivial (↥J ⧸ pPrimeCore 2 ↥J) :=
    (QuotientGroup.mk_surjective (s := center (↥J ⧸ pPrimeCore 2 ↥J))).nontrivial
  have := hperf
  exact Group.IsPerfect.not_isSolvable (↥J ⧸ pPrimeCore 2 ↥J) hsolQ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
