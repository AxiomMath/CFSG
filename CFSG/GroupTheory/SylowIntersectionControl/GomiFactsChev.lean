module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.GlaubermanNiles
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.GroupTheory

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

structure GomiConjugatesCommute {G : Type} [Group G] (L : Subgroup G) : Prop where
  commute : ∀ g : G, L.map (MulAut.conj g).toMonoidHom ≠ L →
    ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ = ⊥
  isPGroup_quotient : IsPGroup 2 (G ⧸ Subgroup.normalClosure (L : Set G))

structure GomiHyp21 {G : Type} [Group G] (L : Subgroup G) : Prop
    extends GomiConjugatesCommute L where
  quasisimple : CFSG.IsQuasisimple ↥L

@[expose] def IsGomiChevTwo (L : Type) [Group L] : Prop :=
  CFSG.IsQuasisimple L ∧ CFSG.pCore 2 L = ⊥ ∧ IsChevTwo (L ⧸ Subgroup.center L)

@[expose] def IsGomiL2 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 5)) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .A 1 q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsGomiU3 (Y : Type) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .twistedA 2 q) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsGomiSz (Y : Type) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, (∃ k : ℕ, d.1 = .suzuki k) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsGomiL3 (Y : Type) [Group Y] : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex,
    ((∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .A 2 q) ∨
      (∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q)) ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsGomiSp4 (Y : Type) [Group Y] : Prop :=
  Nonempty (Y ≃* alternatingGroup (Fin 6)) ∨
    ∃ d : TauCeti.ValidLieTypeIndex, (∃ q : TauCeti.PrimePower, q.p = 2 ∧ d.1 = .B 2 q) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group)

@[expose] def IsGomiParabolicSwap {G : Type} [Group G] (S L : Subgroup G) : Prop :=
  ∃ s ∈ S ⊓ Subgroup.normalizer (L : Set G), ∃ P : Subgroup G,
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) < P ∧ P < L ∧
      s ∉ Subgroup.normalizer (P : Set G)

@[expose] def IsGomiThreeCycle {G : Type} [Group G] (n : ℕ) (K : Subgroup G) (x : G) : Prop :=
  ∃ (hx : x ∈ K) (φ : ↥K ≃* alternatingGroup (Fin n)),
    ((φ ⟨x, hx⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle

@[expose] def GomiFact22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), GomiHyp21 L → IsGomiChevTwo ↥L →
    ¬ (IsGomiL2 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiU3 (↥L ⧸ Subgroup.center ↥L) ∨
        IsGomiSz (↥L ⧸ Subgroup.center ↥L)) →
    ((IsGomiL3 (↥L ⧸ Subgroup.center ↥L) ∨ IsGomiSp4 (↥L ⧸ Subgroup.center ↥L)) →
        ∃ S : Sylow 2 G, ¬ IsGomiParabolicSwap (S : Subgroup G) L) →
    ∀ H : Subgroup G, H ≠ ⊥ → IsPGroup 2 H →
      IsPIsolatedOver 2 (Subgroup.normalizer (H : Set G)) H →
      ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧
        (∃ K : Subgroup G, H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G) ∧
          (K.subgroupOf (Subgroup.normalizer (H : Set G))).IsSubnormal ∧
          2 ∣ H.relIndex K ∧ K ≤ M) ∧
        twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G)) ≤
          Subgroup.normalClosure (L : Set G) ⊓
            Subgroup.centralizer (Subgroup.normalClosure (L : Set G) : Set G)

@[expose] def GomiFact23 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), GomiHyp21 L → 7 ≤ n →
    Nonempty (↥L ≃* alternatingGroup (Fin n)) →
    ∀ H : Subgroup G, H ≠ ⊥ → IsPGroup 2 H →
      IsPIsolatedOver 2 (Subgroup.normalizer (H : Set G)) H →
      ((∀ m : ℕ, n ≠ 2 ^ m + 1) → ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧
        ∃ K : Subgroup G, H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G) ∧
          (K.subgroupOf (Subgroup.normalizer (H : Set G))).IsSubnormal ∧
          2 ∣ H.relIndex K ∧ K ≤ M) ∧
      (Even n → ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧
        (∃ K : Subgroup G, H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G) ∧
          (K.subgroupOf (Subgroup.normalizer (H : Set G))).IsSubnormal ∧
          2 ∣ H.relIndex K ∧ K ≤ M) ∧
        CharTwo M) ∧
      (n % 4 = 3 → ∃ M : Subgroup G, M ≠ ⊤ ∧ Odd M.index ∧
        (∃ K : Subgroup G, H ≤ K ∧ K ≤ Subgroup.normalizer (H : Set G) ∧
          (K.subgroupOf (Subgroup.normalizer (H : Set G))).IsSubnormal ∧
          2 ∣ H.relIndex K ∧ K ≤ M) ∧
        ∃ x : Subgroup G → G,
          (∀ g : G, IsGomiThreeCycle n (L.map (MulAut.conj g).toMonoidHom)
            (x (L.map (MulAut.conj g).toMonoidHom))) ∧
          twoResidual (M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G)) ≤
            Subgroup.closure (Set.range fun g : G => x (L.map (MulAut.conj g).toMonoidHom)))

@[expose] def GomiLemma49Chev : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsChevTwo G →
    ∀ (S : Sylow 2 G) (α : MulAut G), Odd (orderOf α) →
      (∀ s ∈ (S : Subgroup G), α s = s) → α = 1

end CFSG.GroupTheory

end
