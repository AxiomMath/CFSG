module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.QuasithinUnique

@[expose] def KFactUPrimeExcL34 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p = 3 ∧ IsLinThreeFour K →
    ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      (∀ Y : Subgroup K, GLBCore p 1 (T : Subgroup K) ≤ Y →
        Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤) ∧
      ∀ N : Subgroup K, N ≤ GLBCore p 1 (T : Subgroup K) →
        (N.subgroupOf (GLBCore p 1 (T : Subgroup K))).Normal → p.Coprime (Nat.card N) → N = ⊥

@[expose] def KFactUPrimeExcFi22 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (p : ℕ), p = 5 ∧ IsFi22 K →
    ∀ T : Sylow p K, GLBCore p 1 (T : Subgroup K) ≠ ⊤ →
      (∀ Y : Subgroup K, GLBCore p 1 (T : Subgroup K) ≤ Y →
        Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤) ∧
      ∀ N : Subgroup K, N ≤ GLBCore p 1 (T : Subgroup K) →
        (N.subgroupOf (GLBCore p 1 (T : Subgroup K))).Normal → p.Coprime (Nat.card N) → N = ⊥

theorem kFactUPrimeExc_of_halves (h34 : KFactUPrimeExcL34) (hFi : KFactUPrimeExcFi22) :
    KFactUPrimeExc := by
  intro K _ _ p hp
  rcases hp with hp | hp
  · exact h34 K p hp
  · exact hFi K p hp

@[expose] def KFactCaseTwoLocalL28 : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K],
    (p = 3 ∧ ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧
      q.exponent = 3 ∧ d.1 = .A 1 q) ∧ Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    KFactUPrime p K ∧
    (∀ t : K, orderOf t = p → IsPGroup p (MulAction.stabilizer (MulAut K) t)) ∧
    ∀ T : Sylow p K,
      (∃ s ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        ∀ x ∈ (T : Subgroup K), s * x * s⁻¹ = x → x = 1) ∧
      (∀ f : MulAut K, (∀ x ∈ (T : Subgroup K), f x = x) →
        ∃ t ∈ (T : Subgroup K), f = MulAut.conj t) ∧
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

@[expose] def KFactCaseTwoLocalSz32 : Prop :=
  ∀ (p : ℕ) (K : Type) [Group K] [Finite K],
    (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 ∧
      Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group)) →
    KFactUPrime p K ∧
    (∀ t : K, orderOf t = p → IsPGroup p (MulAction.stabilizer (MulAut K) t)) ∧
    ∀ T : Sylow p K,
      (∃ s ∈ Subgroup.normalizer ((T : Subgroup K) : Set K),
        ∀ x ∈ (T : Subgroup K), s * x * s⁻¹ = x → x = 1) ∧
      (∀ f : MulAut K, (∀ x ∈ (T : Subgroup K), f x = x) →
        ∃ t ∈ (T : Subgroup K), f = MulAut.conj t) ∧
      Group.IsSolvable (GLBCore p 1 (T : Subgroup K))

theorem kFactCaseTwoLocal_of_halves (h28 : KFactCaseTwoLocalL28) (h32 : KFactCaseTwoLocalSz32) :
    KFactCaseTwoLocal := by
  intro p K _ _ hK
  obtain ⟨d, hd, he⟩ := hK
  rcases hd with ⟨hp, hq⟩ | ⟨hp, hs⟩
  · exact h28 p K ⟨hp, d, hq, he⟩
  · exact h32 p K ⟨hp, d, hs, he⟩

end CFSG.AGLEmbedding
