module

public import CFSG.LocalAnalysis.EvenSporadicStandard.CentralTwoRowsLarge
public import CFSG.Sporadic.Recognition.Fi22MultiplierRho
public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierFinal

public section

namespace CFSG.EvenSporadicStandard

theorem rowBound_Fi22 :
    RowBound .Fi22 :=
  rowBound_of_card_center_le_two rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact card_center_le_two_of_unique_double_cover
      CFSG.Sporadic.Recognition.Fi22Multiplier.noPerfectDoubleCover_R332
      (fun D _ φ hφ hperf hk =>
        CFSG.Sporadic.Recognition.Fi22Multiplier.nonempty_mulEquiv_R332_of_doubleCover φ hφ
          hperf hk) hq hZ e

open Subgroup CFSG.Monster.Schur

theorem card_ker_le_two_of_row {S : Type} [Group S] [IsSimpleGroup S] (hS : center S = ⊥)
    {E : Type} [Group E] [Finite E] [hE : Group.IsPerfect E] (η : E →* S)
    (hη : Function.Surjective η) (hker : η.ker ≤ center E) (hp : IsPGroup 2 η.ker)
    (hrow : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
      IsPGroup 2 (center L) → Nonempty (L ⧸ center L ≃* S) → Nat.card (center L) ≤ 2) :
    Nat.card η.ker ≤ 2 := by
  have hc : center E = η.ker := by
    refine le_antisymm (fun c hc => ?_) hker
    rw [MonoidHom.mem_ker]
    have : η c ∈ center S := by
      rw [mem_center_iff]
      intro s
      obtain ⟨e, rfl⟩ := hη s
      rw [← map_mul, ← map_mul, mem_center_iff.1 hc e]
    rw [hS] at this
    exact this
  let e' : E ⧸ center E ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientKerEquivOfSurjective η hη)
  have hq : CFSG.Open.IsQuasisimple E :=
    ⟨Group.isPerfect_def.1 hE, @MulEquiv.isSimpleGroup _ _ _ _ inferInstance e'⟩
  have h := hrow E hq (by rw [hc]; exact hp) ⟨e'⟩
  rw [hc] at h
  exact h

set_option maxRecDepth 100000 in
open CFSG.Sporadic.Fi23 in
theorem noPerfectDoubleCover_Fi23_of
    (hS : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
      (η : E →* CFSG.Blueprint.NativeSporadic.Fi22), Function.Surjective η → η.ker ≤ center E →
        IsPGroup 2 η.ker → Nat.card η.ker ≤ 2) :
    NoPerfectDoubleCover CFSG.Blueprint.NativeSporadic.Fi23 := by
  have e : ↥(Subgroup.centralizer ({d} : Set J)) ⧸ center ↥(Subgroup.centralizer ({d} : Set J)) ≃*
      CFSG.Blueprint.NativeSporadic.Fi22 :=
    quotCenterEquiv.trans CFSG.Sporadic.Fi22.fi22EquivJ.symm
  have hnd : NoPerfectDoubleCover ↥(Subgroup.centralizer ({d} : Set J)) :=
    noPerfectDoubleCover_of_center_two (S := CFSG.Blueprint.NativeSporadic.Fi22) card_center_C e
      (fun E _ _ _ η hη hc hp => hS E η hη hc hp)
  have hodd : Odd (Subgroup.centralizer ({d} : Set J)).index := by
    have h1 := (Subgroup.centralizer ({d} : Set J)).card_mul_index
    rw [card_centralizer_d, card_J] at h1
    have : (Subgroup.centralizer ({d} : Set J)).index = 31671 := by omega
    rw [this]; decide
  have hJ : NoPerfectDoubleCover J :=
    noPerfectDoubleCover_of_odd_index _ hodd (Group.isPerfect_def.2 commutator_C) hnd
  exact NoPerfectDoubleCover.of_mulEquiv (G := J) (H := CFSG.Blueprint.NativeSporadic.Fi23)
    fi23EquivJ.symm hJ

theorem center_Fi22_eq_bot :
    center CFSG.Blueprint.NativeSporadic.Fi22 = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h : CFSG.Sporadic.Fi22.fi22EquivJ x ∈ center CFSG.Sporadic.Fi22.J := by
    rw [mem_center_iff] at hx ⊢
    intro j
    obtain ⟨y, rfl⟩ := CFSG.Sporadic.Fi22.fi22EquivJ.surjective j
    rw [← map_mul, ← map_mul, hx y]
  rw [CFSG.Sporadic.Fi22.center_eq_bot, mem_bot] at h
  exact mem_bot.2 (CFSG.Sporadic.Fi22.fi22EquivJ.injective (by rw [h, map_one]))

theorem rowBound_Fi23_of_Fi22
    (hFi22 : RowBound .Fi22) : RowBound .Fi23 :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    have := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
    refine center_eq_bot_of_noPerfectDoubleCover
      (noPerfectDoubleCover_Fi23_of (fun E _ _ _ η hη hker hp => ?_)) hq hZ e
    refine card_ker_le_two_of_row center_Fi22_eq_bot η hη hker hp ?_
    intro L' _ _ hq' hZ' hs'
    have h2 : twoPartBound .Fi22 = 2 := rfl
    have := (hFi22 L' hq' hZ' hs').1
    rw [h2] at this
    exact Nat.le_of_dvd (by norm_num) this

theorem rowBound_Fi23 :
    RowBound .Fi23 :=
  rowBound_Fi23_of_Fi22 rowBound_Fi22

theorem rowBound_Fi24Prime :
    RowBound .Fi24Prime :=
  rowBound_of_center_eq_bot rfl (by decide) fun L _ _ hq hZ hs => by
    obtain ⟨e⟩ := hs
    exact center_eq_bot_of_noPerfectDoubleCover
      CFSG.Sporadic.Recognition.Fi24PrimeMultiplier.noPerfectDoubleCover_Fi24prime hq hZ e

end CFSG.EvenSporadicStandard
