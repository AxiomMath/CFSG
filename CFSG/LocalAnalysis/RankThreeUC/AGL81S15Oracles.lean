module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Ctx

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open
open scoped Pointwise

@[expose] def IsLThreeTwoPow (S : Type) [Group S] : Prop :=
  (∃ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.p = 2 ∧ d.1 = .A 2 Q) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.card = 7 ∧ d.1 = .A 1 Q) ∧
      Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group))

@[expose] def IsMaxInvariantTwo {G : Type} [Group G] (A R : Subgroup G) : Prop :=
  IsPGroup 2 R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
    ∀ S : Subgroup G, IsPGroup 2 S → A ≤ Subgroup.normalizer (S : Set G) → R ≤ S → S = R

@[expose] def QuotEquiv {G : Type} [Group G] (T R : Subgroup G) (Q : Type) [Group Q] : Prop :=
  ∃ _ : (R.subgroupOf T).Normal, Nonempty ((↥T ⧸ R.subgroupOf T) ≃* Q)

structure L34Config {G : Type} [Group G] [Finite G] (M A T R H' : Subgroup G) : Prop where
  le_M : A ≤ M
  elemAbelian : IsElemAbelian 3 A
  card_eq : Nat.card A = 9
  gamma : rankThreeGamma 1 3 A ≤ M
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 T M
  not_sylow : ¬ CFSG.ABGLocalTools.IsSylowOf 2 T H'
  perm : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G)
  core : R = pCoreOf 2 (A ⊔ T)
  normalizer_le : Subgroup.normalizer (R : Set G) ≤ H'
  maximal : IsMaxInvariantTwo A R
  maxLocal : rankThreeIsMaxTwoLocal H'
  le_H : A ≤ H'
  not_le_M : ¬ H' ≤ M
  solvable : Group.IsSolvable ↥(H' ⊓ M ⊓ Subgroup.normalizer (R : Set G))
  quotient : QuotEquiv T R (QuaternionGroup 2) ∨ QuotEquiv T R (CFSG.Open.SemidihedralGroup 4)
  quaternion : ∃ Q : Subgroup (MulAut ↥A),
    Q ≤ (T.subgroupOf (Subgroup.normalizer (A : Set G))).map A.normalizerMonoidHom ∧
      Nonempty (↥Q ≃* QuaternionGroup 2)
  transitive : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    ∃ t ∈ T ⊓ Subgroup.normalizer (A : Set G), t * a * t⁻¹ = b

@[expose] def O1211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q : ℕ, q.Prime → 5 ≤ q → q ∉ sigmaM G M →
        ∀ E : Subgroup G, E ≤ M → IsElemAbelian q E → Nat.card E = q ^ 2 →
          rankThreeGamma 1 q E ≤ M →
          ∀ H : Subgroup G, IsTwoLocal H → E ≤ H → H ≤ M

@[expose] def O1217 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q p : ℕ, q ∈ sigmaM G M → 5 ≤ q → p.Prime → p ≠ 2 →
        ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
          q ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (E : Set G)) →
          (∀ A : Subgroup G, A ≤ E → Nat.card A = p →
            2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.normalizer (A : Set G))) →
          rankThreeGamma 1 p E ≤ M

@[expose] def O1218 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q p : ℕ, q ∈ sigmaM G M → p.Prime → p ≠ 2 →
        ∀ E : Subgroup G, E ≤ M → IsElemAbelian p E → Nat.card E = p ^ 2 →
          rankThreeGamma 1 p E ≤ M →
          ∀ H : Subgroup G, E ≤ H → q ∣ Nat.card ↥(H ⊓ M) → pCoreOf 2 H ≠ ⊥ → H ≤ M

@[expose] def O1521 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      3 ∉ sigmaM G M →
      ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
        ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H ≠ M →
          ∃ A T R H' : Subgroup G, L34Config M A T R H'

@[expose] def O1521b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      3 ∉ sigmaM G M →
      ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
        ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H ≠ M →
          ∀ q ∈ sigmaM G M, ¬ q ∣ Nat.card ↥(H ⊓ M)

@[expose] def O991 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      3 ∉ sigmaM G M →
      ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E ≤ M →
        E ∈ uniqueSet M

@[expose] def O89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ H : Subgroup G, IsTwoLocal H →
        ∀ L : Subgroup G, L ≤ H ⊓ M → CFSG.IsPComponent 3 (L.subgroupOf (H ⊓ M)) →
          CFSG.Open.pRank 3 L = 1 → IsLThreeTwoPow (↥L ⧸ CFSG.pCore 2 ↥L) →
          ∀ A : Subgroup G, A ≤ L → Nat.card A = 3 → A ∈ uniqueSet M →
            (∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom ≤
                Subgroup.normalizer (A : Set G) ⊓ (H ⊓ M) →
              A.map (MulAut.conj h).toMonoidHom = A) →
            ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ M ∧
              Subgroup.normalizer (S : Set G) ⊓ H ≤ M

@[expose] def K89S : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ N L : Subgroup X, CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 N →
      CFSG.Open.pRank 3 N ≤ 1 → L ≤ N → CFSG.IsPComponent 3 (L.subgroupOf N) →
      IsLThreeTwoPow (↥L ⧸ CFSG.pPrimeCore 3 ↥L) →
      ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ S ≤ N ∧
        Subgroup.normalizer (S : Set X) ≤ N

@[expose] def O812six : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ q ∈ sigmaM G M, 5 ≤ q →
        ∀ F : Subgroup G, F ≤ M → IsPGroup 3 F → F ≠ ⊥ → Group.IsSolvable (MulAut ↥F) →
          2 ≤ CFSG.Open.pRank q (M ⊓ Subgroup.centralizer (F : Set G)) →
          ¬ CFSG.HallHigman.IsPSolvable q ↥(M ⊓ Subgroup.centralizer (F : Set G)) →
          Subgroup.normalizer (F : Set G) ≤ M

@[expose] def P812 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.RankThree.PartOne.IsStronglyPEmbedded p M →
        2 < CFSG.Open.pRank p M →
        ∀ L₁ L₂ : Subgroup G, L₁ ≤ M → L₂ ≤ M → L₁ ≠ L₂ →
          CFSG.IsPComponent p (L₁.subgroupOf M) → CFSG.IsPComponent p (L₂.subgroupOf M) →
          (L₁.subgroupOf M).Normal → CFSG.Open.pRank 3 M ≤ 3 →
          CFSG.Open.pRank p L₁ = 1 → CFSG.Open.pRank 3 L₁ = 1 →
          CFSG.Open.pRank p L₂ = 1 → CFSG.Open.pRank 3 L₂ = 1 →
          (∀ B : Subgroup G, B ≤ M → Nat.card B = 3 →
            2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G)) →
            ¬ CFSG.HallHigman.IsPSolvable p ↥(M ⊓ Subgroup.centralizer (B : Set G)) →
            Subgroup.normalizer (B : Set G) ≤ M) →
          ∀ A : Subgroup G, Nat.card A = 3 → (A ≤ L₁ ∨ A ≤ L₂) → A ∈ uniqueSet M

@[expose] def barMeet {G : Type} [Group G] (K M : Subgroup G) :
    Subgroup (↥K ⧸ CFSG.pPrimeCore 3 ↥K) :=
  ((K ⊓ M).subgroupOf K).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K))

@[expose] def ThreeFourShape {G : Type} [Group G] (K M : Subgroup G) : Prop :=
  ((∃ d : TauCeti.ValidLieTypeIndex, (∃ Q : TauCeti.PrimePower, Q.card = 4 ∧ d.1 = .A 2 Q) ∧
        Nonempty (((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pPrimeCore 3 ↥K)) ≃*
          (TauCeti.CFSGIndex.lie d).Group)) ∧
      ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(barMeet K M) → r = 2 ∨ r = 3) ∨
    (Nonempty ((↥K ⧸ CFSG.pPrimeCore 3 ↥K) ≃* alternatingGroup (Fin 11)) ∧
      Nonempty (↥(barMeet K M) ≃* Equiv.Perm (Fin 9)))

@[expose] def O98 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      3 ∉ sigmaM G M →
      ∀ Q : Subgroup G, Q ≤ M → IsPGroup 3 Q → ¬ IsCyclic ↥Q → rankThreeGamma 1 3 Q ≤ M →
        ∀ x : G, x ∈ M → orderOf x = 3 → (∀ y ∈ Q, x * y = y * x) →
          ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
          pCoreOf 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ →
          pCoreOf 2 (Subgroup.centralizer ({x} : Set G) ⊓ M) ≠ ⊥ →
            ∃ K : Subgroup G, K ≤ Subgroup.centralizer ({x} : Set G) ∧
              CFSG.IsPComponent 3 (K.subgroupOf (Subgroup.centralizer ({x} : Set G))) ∧
              ¬ K ≤ M ∧ ThreeFourShape K M ∧
              (∀ y ∈ Subgroup.centralizer ({x} : Set G) ⊓ M, orderOf y = 7 →
                y ∈ Subgroup.normalizer (K : Set G))

@[expose] def O1517b : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing G → rankThreeUC G →
    ∀ M : Subgroup G, rankThreeIsMaxTwoLocal M →
      (∃ p ∈ sigmaM G M, ∃ P : Sylow p G, IsWitness p P M) →
      (∀ q ∈ sigmaM G M, CFSG.RankThree.PartOne.IsStronglyPEmbedded q M) →
      ∀ p ∈ sigmaM G M,
        ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M → rankThreeGamma 2 3 R ≤ M →
          ∀ A : Subgroup G, A ≤ M → Nat.card A = 3 →
            p ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (A : Set G)) →
            ∀ P : Subgroup G,
              CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ Subgroup.normalizer (A : Set G)) →
              (((IsElemAbelian 3 P ∧ Nat.card P = 27) ∨ IsCyclic ↥(Subgroup.center ↥P)) ∧
                3 ≤ CFSG.Open.pRank 3 P) →
              Subgroup.normalizer (A : Set G) ≤ M

end CFSG.LocalAnalysis.RankThreeUC.S15
