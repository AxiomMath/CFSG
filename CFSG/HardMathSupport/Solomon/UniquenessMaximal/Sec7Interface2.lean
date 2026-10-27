module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Vocab
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMaxBInvariantTwo (B T : Subgroup G) : Prop :=
  IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
    ∀ T' : Subgroup G, IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set G) → T ≤ T' → T' = T

@[expose] noncomputable def jOf (T : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ T ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ CFSG.Open.pRank 2 T), E

@[expose] noncomputable def jOneOf (T : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ T ∧ IsElemAbelian 2 E ∧ 2 ^ (CFSG.Open.pRank 2 T - 1) ≤ Nat.card E), E

@[expose] def omegaOneZ (T : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ centerOf T ∧ x ^ 2 = 1}

@[expose] noncomputable def tripleOf (T : Subgroup G) : Fin 3 → Subgroup G :=
  ![jOf T, omegaOneZ (jOneOf T), omegaOneZ T]

@[expose] def Lemma710Stmt (B : Subgroup G) : Prop :=
  ∀ T : Subgroup G, IsMaxBInvariantTwo B T → ∀ K : Subgroup G, IsHSet B K →
    ∃ s : Finset (Fin 3), 2 ≤ s.card ∧
      ∀ i ∈ s, Covers3 (Subgroup.normalizer (tripleOf T i : Set G)) K

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
