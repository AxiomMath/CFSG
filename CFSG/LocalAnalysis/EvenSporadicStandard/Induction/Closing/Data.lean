module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Lemma39
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRow

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78

@[expose] def AutOddCoreTrivial (Y : Type) [Group Y] : Prop :=
  ∀ ν : MulAut Y, ν ≠ 1 → ν * ν = 1 → ∀ P : Subgroup Y, P ≤ fixSubgroup ν →
    (P.subgroupOf (fixSubgroup ν)).Normal → Odd (Nat.card P) → P = ⊥

abbrev ExcClass : Type 1 := ∀ (Y : Type) [Group Y], MulAut Y → Prop

structure FusionRowData (s : TauCeti.SporadicName) (Exc : ExcClass) : Prop where
  autCenter : ∀ (Y : Type) [Group Y], IsSporadic Y s → AutCenterCondExc Y (Exc Y)
  uMoves : ∀ (Y : Type) [Group Y], IsSporadic Y s → UMovesCond Y
  oddCore : ∀ (Y : Type) [Group Y], IsSporadic Y s → AutOddCoreTrivial Y

structure PerfectRowData (s : TauCeti.SporadicName) : Prop where
  allInner : ∀ (Y : Type) [Group Y], IsSporadic Y s → ∀ α : MulAut Y, ∃ g : Y, α = MulAut.conj g
  perfect : ∀ (Y : Type) [Group Y], IsSporadic Y s → PerfectInvolutions Y
  center : ∀ (Y : Type) [Group Y], IsSporadic Y s → CenterInvolutions Y
  oddCore : ∀ (Y : Type) [Group Y], IsSporadic Y s → AutOddCoreTrivial Y

@[expose] def PairClass.InL (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] (L K : Subgroup H) (u : H), Q H L K u → u ∈ L

@[expose] def PairClass.TwoSylow (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H), Q H L K u →
    ∀ S : Sylow 2 (centralizer (L : Set H)), Nat.card S = 2

@[expose] def SolomonCoreP (s : TauCeti.SporadicName) (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), OddCover s L →
    SolomonHypQ H N L K t u → Q H L K u → False

@[expose] def SolomonCorePAt (s : TauCeti.SporadicName) (Q : PairClass) (H : Type) [Group H]
    [Finite H] : Prop :=
  ∀ (N L K : Subgroup H) (t u : H), OddCover s L → SolomonHypQ H N L K t u → Q H L K u → False

@[expose] def SolomonCorePHered (s : TauCeti.SporadicName) (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], Balance.UHered H → SolomonCorePAt s Q H

@[expose] def ExcExcluded (s : TauCeti.SporadicName) (Exc : ExcClass) (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), OddCover s L →
    SolomonHypQ H N L K t u → Q H L K u →
      ∀ (u₁ : H) (hN : u₁ ∈ normalizer (L : Set H)), u₁ * u₁ = 1 → u₁ * t = t * u₁ →
        IsConj u u₁ → ¬ Exc (↥L ⧸ center ↥L) (normalizerAction L ⟨u₁, hN⟩)

@[expose] def TMemFStar (s : TauCeti.SporadicName) (Q : PairClass) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (N L K : Subgroup H) (t u : H), OddCover s L →
    SolomonHypQ H N L K t u → Q H L K u → t ∈ N

theorem sol78ClosingAt_of_partsP {S : List TauCeti.SporadicName}
    {Q P : TauCeti.SporadicName → PairClass} {H : Type} [Group H] [Finite H]
    (hloc : ∀ s ∈ S, Sol78SettingLocalQ s (Q s) (P s)) (h39 : ∀ s ∈ S, Sol78Local39Q s (P s))
    (hcore : ∀ s ∈ S, SolomonCorePAt s (Q s) H) : Sol78ClosingAt S Q H := by
  intro N L K t u s hs hN hidx hK hcov hglob hQ
  obtain ⟨hl, hP⟩ := hloc s hs H L K u hcov hQ
  have hset : SolomonSettingQ H N L K t u :=
    SolomonSettingQ.of_parts hN hidx hK hcov hglob hl
  obtain ⟨hne, hfus, hgen⟩ := h39 s hs H N L K t u hcov hset hP
  exact hcore s hs N L K t u hcov (hset.toHypQ hne hfus hgen) hQ

theorem sol78Closing_of_partsP {S : List TauCeti.SporadicName}
    {Q P : TauCeti.SporadicName → PairClass}
    (hloc : ∀ s ∈ S, Sol78SettingLocalQ s (Q s) (P s)) (h39 : ∀ s ∈ S, Sol78Local39Q s (P s))
    (hcore : ∀ s ∈ S, SolomonCoreP s (Q s)) : Sol78Closing S Q :=
  fun H _ _ => sol78ClosingAt_of_partsP hloc h39 (fun s hs => hcore s hs H)

theorem sol78ClosingHered_of_partsP {S : List TauCeti.SporadicName}
    {Q P : TauCeti.SporadicName → PairClass}
    (hloc : ∀ s ∈ S, Sol78SettingLocalQ s (Q s) (P s)) (h39 : ∀ s ∈ S, Sol78Local39Q s (P s))
    (hcore : ∀ s ∈ S, SolomonCorePHered s (Q s)) : Sol78ClosingHered S Q :=
  fun H _ _ hH => sol78ClosingAt_of_partsP hloc h39 (fun s hs => hcore s hs H hH)

end CFSG.EvenSporadicStandard.Induction
