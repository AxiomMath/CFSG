module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

@[expose] def hatOf {A : Type} [Group A] (P J : Subgroup A) :
    Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) :=
  (J.subgroupOf P).map (QuotientGroup.mk' (CFSG.pCore 2 ↥P))

@[expose] def KFactTwelveNotLeAltSix : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsAltTwoP 3 K → ∀ E : Sylow 3 K,
    (∀ U : Subgroup K, (E : Subgroup K) ≤ U → U ≠ ⊤ →
      U ≤ Subgroup.normalizer ((E : Subgroup K) : Set K)) ∧
    Group.IsSolvable ↥(Subgroup.normalizer ((E : Subgroup K) : Set K)) ∧
    ∃ t ∈ Subgroup.normalizer ((E : Subgroup K) : Set K), (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      ∀ Z : Subgroup K, Z ≤ E → Nat.card Z = 3 → Z.map (MulAut.conj t).toMonoidHom ≠ Z

@[expose] def KFactTwelveNotLeGraph : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (Y P J J₁ : Subgroup A) (t : A),
    Open.IsQuasisimple ↥Y → pCoreOf 2 Y = ⊥ →
    IsClassicalTwoOrG2 (↥Y ⧸ Subgroup.center ↥Y) → IsParabolicTwo Y P → Open.pRank 3 Y ≤ 3 →
    J ≤ P → IsSubnormal (hatOf P J) ⊤ → Nonempty (↥(hatOf P J) ≃* Equiv.Perm (Fin 3)) →
    t ∈ Subgroup.normalizer (Y : Set A) → t ∈ Subgroup.normalizer (P : Set A) →
    (∃ k : ℕ, t ^ 2 ^ k = 1) → hatOf P (J.map (MulAut.conj t).toMonoidHom) ≠ hatOf P J →
    J₁ ≤ P → IsSubnormal (hatOf P J₁) ⊤ →
    (IsSymThreeOrSUThreeTwo ↥(hatOf P J₁) ∨ Open.IsQuasisimple ↥(hatOf P J₁)) →
    hatOf P J₁ ≠ hatOf P J → hatOf P J₁ ≠ hatOf P (J.map (MulAut.conj t).toMonoidHom) →
    ∃ r : ℕ, 4 ≤ r ∧ IsLieOver ↥Y (.A r) 2 1

@[expose] def KFactTwelveNotLeSymThreeUnique : Prop :=
  ∀ (R : Type) [Group R] [Finite R],
    ((∃ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 6) ∧ Nonempty (R ≃* Equiv.Perm (Fin n))) ∨
      (∃ n : ℕ, Nonempty (R ⧸ CFSG.pCore 2 R ≃* Equiv.Perm (Fin n))) ∨
      (∃ r s : ℕ, 5 ≤ s ∧
        Nonempty (R ⧸ CFSG.pCore 2 R ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin s))) ∨
      (∃ (k : ℕ) (d : TauCeti.ValidLieTypeIndex), 3 ≤ k ∧
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) ∧
        Nonempty (R ⧸ CFSG.pCore 2 R ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (∃ f : R →* Equiv.Perm (Fin 4), Function.Surjective f ∧ f.ker ≤ Subgroup.center R ∧
        Nat.card f.ker = 3)) →
    ∀ X W : Subgroup (R ⧸ CFSG.pCore 2 R), IsSubnormal X ⊤ → IsSubnormal W ⊤ →
      Nonempty (↥X ≃* Equiv.Perm (Fin 3)) → Nonempty (↥W ≃* Equiv.Perm (Fin 3)) → X = W

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
