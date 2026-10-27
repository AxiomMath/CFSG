module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma29

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def IsHatSix (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))

@[expose] def IsHatMTwentyTwo (X : Type*) [Group X] : Prop :=
  commutator X = ⊤ ∧ Nat.card (Subgroup.center X) = 3 ∧
    Nonempty ((X ⧸ Subgroup.center X) ≃*
      (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M22).Group)

@[expose] def IsLTwoOddPow (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), n % 2 = 1 ∧ 1 < n ∧ Nat.card K = 2 ^ n ∧
    Nonempty (X ≃* ↥(StatedSL 2 K))

@[expose] def IsSUThreeTwoPow (X : Type*) [Group X] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), n % 2 = 1 ∧ 1 < n ∧ n % 3 ≠ 0 ∧
    Nat.card K = (2 ^ n) ^ 2 ∧ Nonempty (X ≃* ↥(StatedSU 3 (2 ^ n) K))

@[expose] def Input11_2Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ (X B L : Subgroup G), IsElemAbelian p B → B ≤ X →
      GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B → GLAPComponent p X L →
      ¬ B ≤ Subgroup.normalizer (L : Set G) →
      p = 3 ∧ (Subgroup.normalizer (L : Set G)).relIndex B = 3 ∧
        CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (barOf 3 L))) ≤ 2 ∧
        (IsElemAbelian 3 (Subgroup.center ↥(barX 3 X (bClosure B L))) ∧
          Nat.card (Subgroup.center ↥(barX 3 X (bClosure B L))) ≤ 9) ∧
        (IsLTwoOddPow (barOf 3 L) ∨ IsHatSix (barOf 3 L) ∨ IsHatSeven (barOf 3 L) ∨
          IsHatMTwentyTwo (barOf 3 L) ∨ IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L) ∨
          IsSUThreeTwoPow (barOf 3 L))

theorem input11_2_of_full (h : Input11_2Full) : Input11_2 := fun G _ _ m p hS X B L hB hBX hr hL hn =>
  let h' := h G m p hS X B L hB hBX hr hL hn
  ⟨h'.1, h'.2.1, h'.2.2.1⟩

@[expose] def Input19_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsKProper G → ∀ p : ℕ, p.Prime → ∀ B : Subgroup G, IsElemAbelian p B → ∀ k : ℕ, 1 ≤ k →
      ∀ D : Subgroup G, IsEkIn p k B D → ∀ b ∈ B, b ≠ 1 →
      (∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
        IsCompWeaklyLocallyBalanced p k B L) →
      (⁅oPrimePOf p (Subgroup.centralizer ({b} : Set G)), delta2At p B D b⁆ ≤
          GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) ∧
        ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
          delta2At p B D b ≤ Subgroup.normalizer (L : Set G)) ∧
      ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
        ¬ ⁅L, delta2At p B D b⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
          ¬ IsCompLocallyBalanced p k B L ∧ kerB p D L = ⊥ ∧
            ¬ B ≤ Subgroup.normalizer (L : Set G) ∧ D ≤ Subgroup.normalizer (L : Set G) ∧
            (((delta2At p B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≠ ⊥ ∧
              ((delta2At p B D b).subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L) ≤
                localDeltaIn p
                  (((delta2At p B D b ⊔ L).subgroupOf (Subgroup.normalizer (L : Set G))).map
                    (barAut p L))
                  ((D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut p L)))

@[expose] def Input19_5_2 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    (IsLTwoOddPow K ∨ IsHatSix K ∨ IsHatSeven K ∨ IsHatMTwentyTwo K) →
    ∀ A : Subgroup (MulAut K), IsPGroup 3 A → IsLocallyBalanced 3 2 A

end CFSG.HardMathSupport.Solomon.LocalBalance
