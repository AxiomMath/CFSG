module

public import CFSG.CGT.Foote82.T66.Perm310
public import CFSG.CGT.Foote82.Setup
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.Blueprint.NativeSporadic

@[expose] def FrontierRankTwoF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog G →
    ∀ L : Subgroup G, standardComponentIsStandard L →
      2 ≤ CFSG.Open.pRank 2 (Subgroup.centralizer (L : Set G)) →
      (∃ n : ℕ, 9 ≤ n ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∨
        (IsSporadic G .J2 ∨ IsSporadic G .Suz ∨ IsSporadic G .He ∨ IsSporadic G .Ru ∨
          IsSporadic G .Co1)

@[expose] def SporadicNoFComponent : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsSporadic X .J2 ∨ IsSporadic X .Suz ∨ IsSporadic X .He ∨ IsSporadic X .Ru ∨
      IsSporadic X .Co1) →
    ∀ t : X, orderOf t = 2 → ∀ Y : Subgroup X,
      IsComponentOf Y (Subgroup.centralizer ({t} : Set X)) →
      (∀ n : ℕ, 6 ≤ n → ∀ α : ↥Y →* alternatingGroup (Fin n), ¬ Function.Surjective α) ∧
      (∀ α : ↥Y →* ↥(omegaMinusTwo 2), ¬ Function.Surjective α) ∧
      (∀ α : ↥Y →* ↥(omegaMinusTwo 3), ¬ Function.Surjective α)

@[expose] def IsNaturalHeartFor {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (G L : Subgroup (GLV V)) {N n : ℕ} (φ : ↥G ≃* alternatingGroup (Fin N)) (τ : Fin n ↪ Fin N) :
    Prop :=
  ∃ β : ↥(commSpace L ⊤) →+ altHeart n, Function.Surjective β ∧
    β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup ∧
    ∀ (g : ↥G), (g : GLV V) ∈ L → ∀ σ : Equiv.Perm (Fin n),
      (∀ i, ((φ g : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) (τ i) = τ (σ i)) →
      ∀ w w' : ↥(commSpace L ⊤), (w' : V) = (g : GLV V) (w : V) →
        ∀ x : CFSG.QuasithinUnique.evenWeight n, β w = (x : altHeart n) →
          β w' = (evenWeightPerm σ x : altHeart n)

@[expose] def FooteLemma24 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G L : Subgroup (GLV V)) (n : ℕ)
    (φ : ↥G ≃* alternatingGroup (Fin (n + 4))) (τ : Fin n ↪ Fin (n + 4)),
    6 ≤ n → L ≤ G →
    (L.subgroupOf G).map ((alternatingGroup (Fin (n + 4))).subtype.comp φ.toMonoidHom) =
      altOn (Set.range τ) →
    IsIrr G ⊤ → IsNaturalHeartFor G L φ τ → IsAltHeartFor G (n + 4)

@[expose] def A11DoubleThreeCycle : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (H : Subgroup (GLV W))
    (φ : ↥H ≃* alternatingGroup (Fin 11)), IsIrr H ⊤ →
    ∀ h : ↥H, ((φ h : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).cycleType = {3, 3} →
      4 ≤ Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers (h : GLV W)) ⊤)

@[expose] def A6NoSixDimIrr : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (H : Subgroup (GLV W)),
    Nonempty (↥H ≃* alternatingGroup (Fin 6)) → IsIrr H ⊤ → Module.finrank (ZMod 2) W ≠ 6

end CFSG.CGT.Foote82
