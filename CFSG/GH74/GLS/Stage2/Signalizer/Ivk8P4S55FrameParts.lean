module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Stmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

structure Cfg55 (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G)
    (p : ℕ) (H P : Subgroup G) (g : G) (X Y : Subgroup G) : Prop where
  ctx : Stage2Ctx G z k S
  c51 : Ctx51 k z S T Tstar p H P
  hnot : ¬ Concl51 k S p H P
  l52 : L52 k S T Tstar p H P
  s53 : Step53 p H P g X Y
  one : TypeOneCase G k

@[expose] def Link55 {G : Type} [Group G] [Finite G] (H P T : Subgroup G) (g : G) {Γ : Type}
    [Group Γ] (K : Subgroup Γ) (a : Γ) (P' R : Subgroup Γ) : Prop :=
  ∃ (Γ₀ : Type) (_ : Group Γ₀) (π : ↥H →* Γ₀) (ι : Γ →* Γ₀) (hg : g ∈ H)
    (J : Subgroup (HBar H)),
    Function.Injective ι ∧ Function.Surjective π ∧ ι.range.Normal ∧ ι.range.index ≤ 2 ∧
    ι a = π ⟨g, hg⟩ ∧ P'.map ι = (P.subgroupOf H).map π ∧
    R.map ι = (T.subgroupOf H).map π ⊓ ι.range ∧
    IsComponent J ∧ ¬ barIn H (zpowers g) ≤ centralizer (J : Set (HBar H)) ∧
    ∃ Dl : Subgroup G, Dl ≤ H ∧ Group.IsPerfect ↥Dl ∧
      (Dl.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) = J ∧
      (Dl.subgroupOf H).map π = K.map ι ∧
      ∀ h : ↥H, QuotientGroup.mk' (pPrimeCore 2 ↥H) h ∈ normalizer (J : Set (HBar H)) →
        (h : G) ∈ normalizer (Dl : Set G)

@[expose] def Bridge55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55 G z k S T Tstar p H P g X Y →
      ∃ (Γ : Type) (_ : Group Γ) (_ : Finite Γ) (V : Type) (_ : AddCommGroup V)
        (_ : Module (ZMod p) V) (_ : Module.Finite (ZMod p) V)
        (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ) (P' R : Subgroup Γ),
        Frame55 k p ρ K a P' R ∧ Link55 H P T g K a P' R

@[expose] def Endgame55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S T Tstar : Subgroup G) (p : ℕ)
    (H P : Subgroup G) (g : G) (X Y : Subgroup G), Cfg55 G z k S T Tstar p H P g X Y →
      ∀ (Γ : Type) [Group Γ] [Finite Γ] (V : Type) [AddCommGroup V] [Module (ZMod p) V]
        [Module.Finite (ZMod p) V] (ρ : Γ →* (V →ₗ[ZMod p] V)ˣ) (K : Subgroup Γ) (a : Γ)
        (P' R : Subgroup Γ), Frame55 k p ρ K a P' R → Link55 H P T g K a P' R →
          Concl55 p K → L55 k p H

theorem frame55thm_of_parts (hB : Bridge55) (hE : Endgame55) : Frame55Thm := by
  intro G _ _ z k S ctx T Tstar p H P hc hnot l52 g X Y hs53 hone
  have hcfg : Cfg55 G z k S T Tstar p H P g X Y := ⟨ctx, hc, hnot, l52, hs53, hone⟩
  obtain ⟨Γ, _, _, V, _, _, _, ρ, K, a, P', R, hf, hl⟩ :=
    hB G z k S T Tstar p H P g X Y hcfg
  exact ⟨Γ, inferInstance, inferInstance, V, inferInstance, inferInstance, inferInstance, ρ, K, a,
    P', R, hf, hE G z k S T Tstar p H P g X Y hcfg Γ V ρ K a P' R hf hl⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
