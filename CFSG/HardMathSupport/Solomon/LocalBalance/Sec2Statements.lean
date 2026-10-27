module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec2Defs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def Lemma24 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, IsBOneMax p B → ¬ IsWeaklyBalancedWrt p 2 B →
      ∀ D : Subgroup G, IsEkIn p 2 B D → ∀ b ∈ B, b ≠ 1 →
        ¬ delta2At p B D b ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G)) →
          p = 3 ∧
            (∃ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L ∧
              ¬ ⁅L, delta2At p B D b⁆ ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({b} : Set G))) ∧
            ∀ L : Subgroup G, Lemma24Setup p B D b L → Lemma24Conclusion B D b L

@[expose] def Lemma25 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ (B D : Subgroup G) (b : G) (L : Subgroup G), Lemma24Setup 3 B D b L →
      ∀ Lᵢ : Subgroup G, IsBConjugate B L Lᵢ → ∀ x : G,
        x ∈ Subgroup.centralizer ({b} : Set G) → orderOf x = 3 →
        ⁅Lᵢ, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) →
        let Jis : Subgroup G := ⨆ g ∈ GLAPLayer 3 (Subgroup.centralizer ({x} : Set G)),
          GLBConj g (GLAPLayer 3 (Lᵢ ⊓ Subgroup.centralizer ({x} : Set G)))
        (x ∈ B → Lemma24Conclusion B D x Jis) ∧
          ((barImageAt 3 b (Subgroup.closure {x, b}) ≤ barCenterAt 3 b (bClosure B L) ∨
              (D ≤ Subgroup.centralizer ({x} : Set G) ∧
                barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L))) →
            b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G)))

@[expose] def Lemma26 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ¬ IsWeaklyBalancedWrt 3 2 B →
      ∃ (D : Subgroup G) (b : G) (L : Subgroup G), Lemma24Setup 3 B D b L ∧
        Lemma24Conclusion B D b L ∧
        b ∈ bClosure B L ∧ barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)

@[expose] def Lemma27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L → ¬ B ≤ Subgroup.normalizer (L : Set G) →
      b ∈ bClosure B L →
      ((∃ D : Subgroup G, Lemma24Setup 3 B D b L ∧ Lemma24Conclusion B D b L ∧
          barImageAt 3 b (Subgroup.zpowers b) = barCenterAt 3 b (bClosure B L)) ∨
        (GLATwoLocalRank 3 G = 4 ∧ (IsSLThree (barOf 3 L) ∨ IsSUThree (barOf 3 L)) ∧
          (Nat.card L).factorization 3 = 3 ∧ IsWeaklyBalancedWrt 3 2 B)) →
      ∀ Lᵢ Lⱼ : Subgroup G, IsBConjugate B L Lᵢ → IsBConjugate B L Lⱼ →
        ∀ x ∈ Lᵢ ⊔ Lⱼ, orderOf x = 3 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({x} : Set G))

@[expose] def Lemma28 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsElemAbelian 3 B → GLATwoLocalRank 3 G ≤ CFSG.Open.pRank 3 B →
      ∀ b ∈ B, b ≠ 1 → ∀ (A : Subgroup G) (k : ℕ), 3 ≤ k → IsEkIn 3 k B A →
        (∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ A ≤ Subgroup.normalizer (T : Set G)) → b ∈ A →
        (∀ a ∈ A, a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))) →
        (∀ L : Subgroup G, GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
          B ≤ Subgroup.normalizer (L : Set G)) →
        IsBZeroMax 3 B ∧ IsWeaklyBalancedWrt 3 2 B

@[expose] def Lemma29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 →
    ∀ B : Subgroup G, IsElemAbelian 3 B → CFSG.Open.pRank 3 B = GLATwoLocalRank 3 G →
      ∀ X : Subgroup G, B ≤ X → X ≠ ⊤ →
        ∃ B' : Subgroup G, B' ≤ X ∧ IsElemAbelian 3 B' ∧ CFSG.Open.pRank 3 B ≤ CFSG.Open.pRank 3 B' ∧
          (∀ L : Subgroup G, GLAPComponent 3 X L → B' ≤ Subgroup.normalizer (L : Set G)) ∧
          ∀ J : Subgroup G, GLAPComponent 3 X J → ¬ B ≤ Subgroup.normalizer (J : Set G) →
            ¬ B' ⊓ J ≤ oPrimePOf 3 J

@[expose] def Lemma210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLATwoLocalRank 3 G = 4 →
    ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
      GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L →
      (IsSLThreeExc (barOf 3 L) ∨ IsSUThreeExc (barOf 3 L)) → bClosure B L ≠ L →
      ∀ L₂ L₃ : Subgroup G, IsBConjugate B L L₂ → IsBConjugate B L L₃ → L ≠ L₂ → L ≠ L₃ → L₂ ≠ L₃ →
        ∃ B' : Subgroup G, IsBZeroMax 3 B' ∧ b ∈ B' ∧ B' ≤ bClosure B L ∧
          (∀ Lᵢ : Subgroup G, IsBConjugate B L Lᵢ → ¬ B' ⊓ Lᵢ ≤ oPrimePOf 3 Lᵢ) ∧
          CFSG.Open.pRank 3 (B' ⊓ (L₂ ⊔ L₃)) = 3 ∧
          ∀ a ∈ B' ⊓ (L₂ ⊔ L₃), a ≠ 1 → b ∈ oPrimePOf 3 (Subgroup.centralizer ({a} : Set G))

end CFSG.HardMathSupport.Solomon.LocalBalance
