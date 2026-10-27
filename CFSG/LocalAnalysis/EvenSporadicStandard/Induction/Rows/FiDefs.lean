module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Open
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.PredS

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def fiTypes : List TauCeti.SporadicName := [.Fi22, .Fi23, .Fi24Prime]

@[expose] def NoBiggerFi (H : Type) [Group H] (s : TauCeti.SporadicName) : Prop :=
  ∀ (L₁ : Subgroup H) (s₁ : TauCeti.SporadicName), SolStd L₁ → s₁ ∈ fiTypes → OddCover s₁ L₁ →
    Nat.card (Carrier s₁) ≤ Nat.card (Carrier s)

@[expose] def fiInBase (s : TauCeti.SporadicName) (n : ℕ) (H : Type) [Group H]
    (L K : Subgroup H) (u : H) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ CFSG.IsQuasisimple ↥K ∧
    n ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K) ∧ NoBiggerFi H s

@[expose] def fiLoc (n : ℕ) (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ CFSG.IsQuasisimple ↥K ∧
    n ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K)

theorem fiInBase_iff {s : TauCeti.SporadicName} {n : ℕ} {H : Type} [Group H] {L K : Subgroup H}
    {u : H} : fiInBase s n H L K u ↔ fiLoc n H L K u ∧ NoBiggerFi H s := by
  simp only [fiInBase, fiLoc, and_assoc]

@[expose] def fiIn22 (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  fiInBase .Fi22 18393661440 H L K u ∧
    ∀ [Finite H] (N : Subgroup H) (t : H), SolomonHypQ H N L K t u → t ∈ N

@[expose] def fiIn23 (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  fiInBase .Fi23 (2 * 64561751654400) H L K u

@[expose] def fiIn24 (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  fiInBase .Fi24Prime (2 * 64561751654400) H L K u

@[expose] def fiOut24 (H : Type) [Group H] (L K : Subgroup H) (u : H) : Prop :=
  u ∈ normalizer (L : Set H) ∧ u ∉ L ⊔ centralizer (L : Set H) ∧ orderOf u = 2 ∧ K ≤ L ∧
    (∀ k ∈ K, k * u = u * k) ∧ CFSG.IsQuasisimple ↥K ∧
    4089470473293004800 ≤ Nat.card (↥K ⧸ CFSG.oddCore ↥K) ∧ NoBiggerFi H .Fi24Prime

@[expose] def fiPair : TauCeti.SporadicName → PairClass
  | .Fi22 => fiIn22
  | .Fi23 => fiIn23
  | .Fi24Prime => fun H _ L K u => fiIn24 H L K u ∨ fiOut24 H L K u
  | _ => fun _ _ _ _ _ => False

structure Cfg610_2Data (H : Type) [Group H] (L : Subgroup H) (t u : H) (K Lu Lut : Subgroup H) :
    Prop where
  le_L : K ≤ L
  le_C : K ≤ centralizer ({u} : Set H)
  isSporadic : IsSporadic ↥K .Fi23
  unique : ∀ K' : Subgroup H, K' ≤ L → K' ≤ centralizer ({u} : Set H) → IsSporadic ↥K' .Fi23 →
    K' = K
  Lu_comp : IsCompIn Lu (centralizer ({u} : Set H))
  Lu_cover : OddCover .Fi24Prime Lu
  Lu_std : SolStd Lu
  le_Lu : K ≤ Lu
  Lut_comp : IsCompIn Lut (centralizer ({u * t} : Set H))
  Lut_cover : OddCover .Fi24Prime Lut
  Lut_std : SolStd Lut
  le_Lut : K ≤ Lut

structure Cfg610_2 (H : Type) [Group H] (N L : Subgroup H) (t u : H) : Prop where
  fstar : FStarSimple N
  index_le_two : N.index ≤ 2
  standardL : SolStd L
  cyclicSylow : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S
  t_order : orderOf t = 2
  t_mem : t ∈ centralizer (L : Set H)
  u_order : orderOf u = 2
  u_comm_t : u * t = t * u
  u_mem : u ∈ normalizer (L : Set H)
  u_not_mem : u ∉ L ⊔ centralizer (L : Set H)
  exists_data : ∃ K Lu Lut : Subgroup H, Cfg610_2Data H L t u K Lu Lut

@[expose] def FiOut (H : Type) [Group H] (N L : Subgroup H) (s : TauCeti.SporadicName) : Prop :=
  (∃ (K : Subgroup H) (t u : H), SolomonGlobalQ H L K t u ∧ fiPair s H L K u) ∨
    (s = .Fi24Prime ∧ ∃ t u : H, Cfg610_2 H N L t u)

@[expose] def Sol78ClosingFi : Prop :=
  Sol78Lit → ∀ (H : Type) [Group H] [Finite H], BelowSec (Sol78PredS fiTypes) H →
    ∀ (N L : Subgroup H) (s : TauCeti.SporadicName), s ∈ fiTypes → FStarSimple N →
      N.index ≤ 2 → CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → OddCover s L →
        FiOut H N L s → Sol78Concl N L

@[expose] def FiGiven : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L : Subgroup H) (s : TauCeti.SporadicName),
    s ∈ fiTypes → FStarSimple N → IsSporadic ↥N .Fi24Prime → N.index ≤ 2 →
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog H → SolStd L → OddCover s L →
        IsSporadic ↥L .Fi23 ∧ center ↥L = ⊥

end CFSG.EvenSporadicStandard.Induction
