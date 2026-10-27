module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Kinds
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29G2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29M12

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12 CFSG.Assembly.LowTwoRank

@[expose] def L29G2Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G),
    Stage2Ctx G z Kind.g2 S → ∀ (r₁ : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      G2Shape z S r₁ 3 L₁ L₂ → Lemma29FirstAt z Kind.g2

@[expose] def L29M12NoConj : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G),
    Stage2Ctx G z Kind.m12 S → ∀ U : Subgroup G, IVK.IsFourSubgroup U →
      (∀ u ∈ U, ¬ IsConj z u) → HasNormal2Compl (centralizer (U : Set G))

@[expose] def L29OneClassSwap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) (ε : Bool),
    Stage2Ctx G z (Kind.l4 ε) S → ∀ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)),
      Stage1L4 G z S ε q L₁ L₂ → (∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v) →
      ∀ u ∈ S, u ∈ Cen z → u * u = 1 → u ∉ zpowers z → Swaps z u L₁ L₂ →
        ∀ U : Subgroup G, IVK.IsFourSubgroup U → z ∈ U → u ∈ U → Lemma29Alt z (Kind.l4 ε) U

theorem lemma29First_of (hND : NonCentralDihedral) (h3 : L29G2Three) (hm : L29M12NoConj)
    (hs : L29OneClassSwap) : Lemma29First := by
  intro G _ _ z k S ctx
  cases k with
  | g2 =>
    cases ctx.data with
    | g2 hg =>
      obtain ⟨r₁, r₂, L₁, L₂, hsh⟩ := hg.shape
      by_cases hr : 3 < r₂
      · exact lemma29FirstAt_of_g2_gt3 ctx rfl hsh hr
      · have hr2 : r₂ = 3 := by
          obtain ⟨-, ho₂, -, -, -, hs₂, -⟩ := hsh
          obtain ⟨F, hF, hFin, hq, -⟩ := hs₂
          have : 1 < Nat.card F := Finite.one_lt_card
          have hq' : r₂ = Nat.card F := hq.symm
          obtain ⟨j, hj⟩ := ho₂
          omega
        subst hr2
        exact h3 G z S ctx r₁ L₁ L₂ hsh
  | m12 => exact lemma29FirstAt_of_m12 ctx (hm G z S ctx)
  | psp4 => exact lemma29FirstAt_of_psp4 hND ctx rfl
  | l4 ε =>
    exact lemma29FirstAt_of_l4 hND ctx fun {q L₁ L₂} hq hone u huS hu hu2 hu1 hsw U hU hzU huU =>
      hs G z S ε ctx q L₁ L₂ hq hone u huS hu hu2 hu1 hsw U hU hzU huU
  | mcl => exact lemma29FirstAt_of_mclly ctx (Or.inl rfl)
  | ly => exact lemma29FirstAt_of_mclly ctx (Or.inr rfl)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
