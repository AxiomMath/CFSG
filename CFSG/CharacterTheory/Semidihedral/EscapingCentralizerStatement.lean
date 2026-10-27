module

public import CFSG.CharacterTheory.Semidihedral.EscapingLocalEigensubgroups

public noncomputable section

namespace CFSG.Semidihedral.EscapingCentralizer

open CFSG.Open CFSG.Semidihedral
open CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.Semidihedral.EscapingLocalEigensubgroups

universe u

variable {G : Type u} [Group G]

@[expose] def EscapingTrivialFactorConclusion (i : G) (Wa : Subgroup G) (ell p f : ℕ) : Prop :=
  let Wi := localFixedGroup Wa i
  let Pi := (Wi.subgroupOf (C i)).map (nu i)
  let Yq := (localLayerPreimage i).map (nu i)
  let z := nu i (tInC i)
  let K := Subgroup.centralizer (Wi : Set G)
  ell = p ∧ CFSG.IsElementaryAbelian p Wa ∧ Nat.card Wa = (p ^ f) ^ 2 ∧
    CFSG.IsElementaryAbelian p Wi ∧ Nat.card Wi = p ^ f ∧
    Pi ≤ Yq ∧ Nat.card Pi = p ^ f ∧
    (∃ S : Sylow p Yq, (S : Subgroup Yq).map Yq.subtype = Pi) ∧
    Subgroup.centralizer (Pi : Set (H i)) = Pi ⊔ Subgroup.zpowers z ∧
    Disjoint Pi (Subgroup.zpowers z) ∧ orderOf z = 2 ∧ z ∈ Subgroup.center (H i) ∧
    (∃ e : Pi × Subgroup.zpowers z ≃* Subgroup.centralizer (Pi : Set (H i)),
      ∀ x : Pi × Subgroup.zpowers z, (e x : H i) = (x.1 : H i) * (x.2 : H i)) ∧
    (Nat.card K).factorization 2 = 1 ∧ (∀ S : Sylow 2 K, Nat.card (S : Subgroup K) = 2) ∧
    ∃ M : Subgroup K, M.Normal ∧ Odd (Nat.card M) ∧ M.index = 2 ∧ M = CFSG.pPrimeCore 2 K

@[expose] def EscapingCentralizerConclusion (t i : G) (Wa : Subgroup G) (ell p f : ℕ) :
    Prop :=
  let Wi := localFixedGroup Wa i
  let Na := (N i).map (C i).subtype
  let J := localCentralizingLayer i
  let Y := localLayerPreimage i
  let K := Subgroup.centralizer (Wi : Set G)
  ∃ U : Subgroup G,
    (∀ x : G, x ∈ U ↔ x ∈ Na ∧ t * x * t⁻¹ = x⁻¹) ∧
    U ≤ Na ∧ IsMulCommutative U ∧ (U.subgroupOf Na).Characteristic ∧
    Nat.Coprime (Nat.card U) (U.relIndex Na) ∧
    Group.IsPerfect J ∧ J.Normal ∧ ⁅J, N i⁆ = ⊥ ∧ Y = J ⊔ N i ∧
    J.map (nu i) = Y.map (nu i) ∧
    Wi ≤ J.map (C i).subtype ⊔ U ∧ U ≤ K ∧
    ⁅K, Subgroup.zpowers i⁆ ≤ (CFSG.pPrimeCore 2 K).map K.subtype ∧
    (Wi ⊓ U = ⊥ → EscapingTrivialFactorConclusion i Wa ell p f)

@[expose] def EscapingCentralizerStatement : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] [IsSimpleGroup G],
    (∃ a b : G, a * b ≠ b * a) →
    PerfectLayerNormalization.OriginalSmallerSimpleRecognition G →
    ∀ (n : ℕ), 4 ≤ n → ∀ (S0 : Sylow 2 G), (SemidihedralGroup n ≃* S0) →
    ∀ (t s : G), orderOf t = 2 → orderOf s = 2 → s ∈ C t → t ≠ s →
    ∀ [IsSimpleGroup (CFSG.generalizedFitting (Gamma t))],
    (∃ a b : CFSG.generalizedFitting (Gamma t), a * b ≠ b * a) →
    Subgroup.centralizer (CFSG.generalizedFitting (Gamma t) : Set (Gamma t)) = ⊥ →
    (∀ P : Sylow 2 (CFSG.generalizedFitting (Gamma t)), ¬ IsCyclic P) →
    ∀ (p f : ℕ), p.Prime → Odd p → 1 ≤ f → 5 < p ^ f →
    (CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 2 p f ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
        Nonempty (CFSG.generalizedFitting (Gamma t) ≃*
          CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F))) →
    allLocalPrimeStationaryCovers t s →
    ∀ (H : Subgroup G), Subgroup.closure ({t, s} : Set G) ≤ H →
    (localCentralizingLayer t).map (C t).subtype ≤ H →
    CFSG.pPrimeCore 2 H ≠ ⊥ →
    ∀ (ell : ℕ), ell.Prime → ell ∣ Nat.card (CFSG.pPrimeCore 2 H) →
    ∀ (W : Sylow ell (CFSG.pPrimeCore 2 H)),
    Subgroup.closure ({t, s} : Set G) ≤
      Subgroup.normalizer (coveringOddSylowAmbient H W : Set G) →
    ¬ coveringOddSylowAmbient H W ≤ C t →
    ∀ i : G, i = s ∨ i = t * s →
      EscapingCentralizerConclusion t i (coveringOddSylowAmbient H W) ell p f

end CFSG.Semidihedral.EscapingCentralizer
