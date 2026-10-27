module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank619Thompson

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family

section

variable {A : Type} [Group A]

structure Hyp2813 (X K R P₁ : Subgroup A) : Prop where
  charTwo : X ⊓ centralizer (pCoreOf 2 X : Set A) ≤ pCoreOf 2 X
  K_le : K ≤ X
  K_normal : X ≤ normalizer (K : Set A)
  K_perfect : ⁅K, K⁆ = K
  X_eq : X = K ⊔ pCoreOf 2 X
  quot : ∃ f : ↥K →* GL32, Function.Surjective f ∧ ∀ k : ↥K, f k = 1 ↔ (k : A) ∈ pCoreOf 2 X
  R_le : R ≤ X
  R_two : IsPGroup 2 R
  R_sylow : ¬ 2 ∣ (R.subgroupOf X).index
  R_le_P : R ≤ P₁
  P_le : P₁ ≤ X
  P_index : (P₁.subgroupOf X).index = 7
  nofact : ∀ Q₀ : Subgroup A, Q₀ ≤ pCoreOf 2 P₁ → Q₀ ≠ ⊥ →
    (Q₀.subgroupOf (pCoreOf 2 P₁)).Characteristic →
    ¬ X ≤ (X ⊓ centralizer ((omegaCenter (pCoreOf 2 P₁) : Subgroup A) : Set A)) ⊔
      (X ⊓ normalizer (Q₀ : Set A))

@[expose] def TT (X : Subgroup A) : Subgroup A := omegaCenter (pCoreOf 2 X)

@[expose] def T0 (X : Subgroup A) : Subgroup A := TT X ⊓ centralizer (X : Set A)

@[expose] def Hbar (X : Subgroup A) (ψ : ↥X →* GL32) (H : Subgroup A) : Subgroup GL32 :=
  (H.subgroupOf X).map ψ

structure IsTBridge (X : Subgroup A) (ψ : ↥X →* GL32) {N : Type} [AddCommGroup N]
    [DistribMulAction GL32 N] (ι : ↥(TT X) → N) : Prop where
  mul : ∀ a b : ↥(TT X), ι (a * b) = ι a + ι b
  bij : Function.Bijective ι
  equiv : ∀ (x : ↥X) (t : ↥(TT X)) (ht : (x : A) * (t : A) * (x : A)⁻¹ ∈ TT X),
    ι ⟨(x : A) * (t : A) * (x : A)⁻¹, ht⟩ = ψ x • ι t

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
