module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshInput
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup CFSG.Blueprint CFSG.SectionRank

structure SolomonA12HypK (K : Type) [Group K] : Prop where
  fusionSimple : FusionSimple K
  sylowType : ∃ (S : Sylow 2 K) (S' : Sylow 2 (alternatingGroup (Fin 12))),
    Nonempty (↥(S : Subgroup K) ≃* ↥(S' : Subgroup (alternatingGroup (Fin 12))))
  exists_E : ∃ E : Subgroup K, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 2 ^ 6 ∧ ¬ E.Normal ∧
    Nonempty (↥(normalizer (E : Set K)) ⧸ E.subgroupOf (normalizer (E : Set K)) ≃*
      GL (Fin 3) (ZMod 2))

theorem card_gl_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field (𝔽 := ZMod 2) 3, ZMod.card, Fin.prod_univ_three]
  norm_num

@[expose] def SolomonA12InputK : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsKGroupCat K → SolomonA12HypK K → LieModel K .PSp 3 2 1

@[expose] def ElemFactsIn {G : Type} [Group G] (Q : Subgroup G) : Prop :=
  Nat.card Q = 2 ^ 9 ∧ (∃ g ∈ Q, orderOf g = 8) ∧
    ∃ E ≤ Q, (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 2 ^ 6 ∧
      ∀ A ≤ Q, (∀ x ∈ A, x * x = 1) → 2 ^ 6 ≤ Nat.card A → A ≤ E

@[expose] def AltNine (n : ℕ) : Prop :=
  ∀ E : Subgroup (alternatingGroup (Fin n)), (∀ x ∈ E, x * x = 1) → Nat.card E = 2 ^ 6 →
    9 ∣ Nat.card (normalizer (E : Set (alternatingGroup (Fin n))))

@[expose] def SylowData (G : Type) [Group G] : Prop :=
  ∃ P E H : Subgroup G, Nat.card P = 2 ^ 9 ∧ E ≤ P ∧ (∀ x ∈ E, x * x = 1) ∧ Nat.card E = 2 ^ 6 ∧
    (∃ g ∈ P, orderOf g = 8) ∧
    (∀ A : Subgroup G, A ≤ P → (∀ x ∈ A, x * x = 1) → 2 ^ 6 ≤ Nat.card A → A ≤ E) ∧
    H ≤ normalizer (E : Set G) ∧ Nat.card H = 9

structure P12Facts : Prop where
  sylow : ∀ S : Sylow 2 (alternatingGroup (Fin 12)),
    ElemFactsIn (S : Subgroup (alternatingGroup (Fin 12)))
  alt12 : AltNine 12
  alt13 : AltNine 13

end CFSG.EvenSporadicStandard.M12Std.SolomonK
