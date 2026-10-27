module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti

@[expose] def ActsIrr {X : Type*} [Group X] (N R : Subgroup X) : Prop :=
  ∀ W : Subgroup X, W ≤ R → N ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = R

@[expose] def Gls3ConclusionPlus (X : Type) [Group X] [Finite X] (K P : Subgroup X) : Prop :=
  gammaCore 3 1 K (P ⊓ K) < K ∧
  (∀ H : Subgroup X, gammaCore 3 1 K (P ⊓ K) < H → H ≤ K → H = K) ∧
  (
  (∃ q : PrimePower, q.p = 3 ∧ IsoLie ↥K (.A 1 q) ∧ ¬ 3 ∣ K.index ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    (∃ J : Subgroup X, IsCyclic ↥J ∧ gammaCore 3 1 K (P ⊓ K) = (P ⊓ K) ⊔ J) ∧
    IsElemAbelian 3 (P ⊓ K) ∧ Nat.card ↥(P ⊓ K) = q.card) ∨
  (∃ q : PrimePower, q.p = 3 ∧ IsoLie ↥K (.twistedA 2 q) ∧ ¬ 3 ∣ K.index ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    (∃ J : Subgroup X, IsCyclic ↥J ∧ gammaCore 3 1 K (P ⊓ K) = (P ⊓ K) ⊔ J) ∧
    ¬ (∀ a ∈ P ⊓ K, ∀ b ∈ P ⊓ K, a * b = b * a) ∧ Nat.card ↥(P ⊓ K) = q.card ^ 3 ∧
    ∃ E : Subgroup X, E ≤ P ⊓ K ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = q.card ^ 2) ∨
  (∃ m : ℕ, IsoLie ↥K (.reeG2 m) ∧ ¬ 3 ∣ K.index ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    (∃ J : Subgroup X, IsCyclic ↥J ∧ gammaCore 3 1 K (P ⊓ K) = (P ⊓ K) ⊔ J) ∧
    ∃ E : Subgroup X, E ≤ P ⊓ K ∧ IsElemAbelian 3 E ∧ Nat.card ↥E = 3 ^ (2 * m + 1)) ∨
  (IsoLie ↥K (.A 1 ⟨2, 3, Nat.prime_two, by norm_num⟩) ∧ K.index = 3 ∧ IsCyclic ↥(P ⊓ K) ∧
    Nat.card ↥(P ⊓ K) = 9 ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    Nonempty (↥(gammaCore 3 1 K (P ⊓ K)) ≃* DihedralGroup 9) ∧
    Nat.card ↥P = 27 ∧ ¬ (∀ a ∈ P, ∀ b ∈ P, a * b = b * a)) ∨
  ((∃ φ : ↥K ≃* alternatingGroup (Fin 6), ∃ A : Finset (Fin 6), A.card = 3 ∧
    ∀ k : ↥K, (k : X) ∈ gammaCore 3 1 K (P ⊓ K) ↔
      (A.image (φ k : Equiv.Perm (Fin 6)) = A ∨ A.image (φ k : Equiv.Perm (Fin 6)) = Aᶜ)) ∧
    ¬ 3 ∣ K.index ∧ IsElemAbelian 3 (P ⊓ K) ∧ Nat.card ↥(P ⊓ K) = 9 ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    ∃ J : Subgroup X, IsCyclic ↥J ∧ gammaCore 3 1 K (P ⊓ K) = (P ⊓ K) ⊔ J ∧
      ActsIrr J (P ⊓ K)) ∨
  (IsoLie ↥K (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩) ∧ (∃ k : ℕ, K.index = 2 ^ k) ∧
    Nat.card ↥K = 20160 ∧ IsElemAbelian 3 (P ⊓ K) ∧ Nat.card ↥(P ⊓ K) = 9 ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    ∃ S : Subgroup X, S ≤ gammaCore 3 1 K (P ⊓ K) ∧ (P ⊓ K) ⊓ S = ⊥ ∧
      (P ⊓ K) ⊔ S = gammaCore 3 1 K (P ⊓ K) ∧ Nonempty (↥S ≃* QuaternionGroup 2) ∧
      ActsIrr S (P ⊓ K)) ∨
  (Nonempty (↥K ≃* (CFSGIndex.sporadic SporadicName.M11).Group) ∧ K = ⊤ ∧
    IsElemAbelian 3 (P ⊓ K) ∧ Nat.card ↥(P ⊓ K) = 9 ∧
    gammaCore 3 1 K (P ⊓ K) = K ⊓ Subgroup.normalizer ((P ⊓ K : Subgroup X) : Set X) ∧
    ∃ S : Subgroup X, S ≤ gammaCore 3 1 K (P ⊓ K) ∧
      (P ⊓ K) ⊔ S = gammaCore 3 1 K (P ⊓ K) ∧
      Nat.card ↥S = 16 ∧ (∃ a ∈ S, ∃ b ∈ S, orderOf a = 8 ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ 3 ∧ S = Subgroup.closure {a, b}) ∧
      S ⊓ Subgroup.centralizer ((P ⊓ K : Subgroup X) : Set X) = ⊥ ∧ ActsIrr S (P ⊓ K)))

@[expose] def Gls3StronglyThreeEmbeddedPlus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X →
    ∀ K : Subgroup X, K.Normal → IsSimpleGroup ↥K → (∃ a b : ↥K, a * b ≠ b * a) →
      Subgroup.centralizer (K : Set X) = ⊥ →
      ∀ P : Sylow 3 X, 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) →
        gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ →
          Gls3ConclusionPlus X K (P : Subgroup X)

theorem Gls3ConclusionPlus.toConclusion {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (h : Gls3ConclusionPlus X K P) : Gls3Conclusion X K (P ⊓ K) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases h3 with ⟨q, hq, hI, -, hN, hJ, -⟩ | ⟨q, hq, hI, -, hN, hJ, -⟩ | ⟨m, hI, -, hN, hJ, -⟩ |
      ⟨hI, -, hc, h9, hN, hD, -⟩ | ⟨⟨φ, A, hA, hmem⟩, -, -, -, -, -⟩ |
      ⟨hI, -, -, hE, h9, hN, S, hS, hQS, hsup, hQ8, -⟩ |
      ⟨hM, -, hE, h9, hN, S, hS, hsup, h16, hab, hC, -⟩
  · exact Or.inl ⟨Or.inl ⟨q, hq, Or.inl hI⟩, hN, hJ⟩
  · exact Or.inl ⟨Or.inl ⟨q, hq, Or.inr hI⟩, hN, hJ⟩
  · exact Or.inl ⟨Or.inr ⟨m, hI⟩, hN, hJ⟩
  · exact Or.inr (Or.inl ⟨hI, hc, h9, hN, hD⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ, A, hA, hmem⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hI, hE, h9, hN, S, hS, hQS, hsup, hQ8⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hM, hN, S, hS, hsup, h16, hab, hC⟩)))

theorem gls3_of_plus (h : Gls3StronglyThreeEmbeddedPlus) : Gls3StronglyThreeEmbedded :=
  fun X _ _ hX K hKn hKs hKnc hKc P hP hΓ => (h X hX K hKn hKs hKnc hKc P hP hΓ).toConclusion

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
