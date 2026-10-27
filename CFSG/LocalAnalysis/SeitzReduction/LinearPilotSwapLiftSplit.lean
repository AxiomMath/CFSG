module

public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Matrix
open CFSG.SeitzReduction.UnitaryPilot (OddCentralSplit)

theorem sl_exists_section_of_coprime
    {m : ℕ} {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    [CharP F p] {E : Type} [Group E] [Finite E] {π : E →* SpecialLinearGroup (Fin (m + 1)) F}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ center E) (hC : ¬ p ∣ Nat.card π.ker) :
    ∃ σ : SpecialLinearGroup (Fin (m + 1)) F →* E, ∀ g, π (σ g) = g :=
  (CFSG.LieType.Steinberg.existsUnique_section_of_sl2_lift
    (D := CFSG.LieType.Universal.SpecialLinear.rootDatum m F)
    (CFSG.LieType.Universal.SpecialLinear.isCTGroupDatum m F)
    (CFSG.LieType.Universal.SpecialLinear.steinbergExtras m F)
    CFSG.LieType.Steinberg.SL.isParametrization (fun i => CFSG.LieType.Steinberg.SL.rankOne i)
    hπ hcen hC fun ρ => by
      obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC ρ
      exact ⟨ρ', fun g => congrArg (· g) hρ'⟩).exists

theorem oddCentralSplit_specialLinearGroup
    {m : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] : OddCentralSplit (SpecialLinearGroup (Fin (m + 1)) F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro E _ _ π hπ hcen hodd
  exact sl_exists_section_of_coprime hπ hcen (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd))

theorem oddCentralSplit_blockSpecialLinear
    {n : ℕ} {F : Type} [Field F]
    [Finite F] [CharP F 2] {N : Finset (Fin n)} (hN : N.Nonempty) :
    OddCentralSplit (blockSpecialLinear (K := F) N) := by
  obtain ⟨m, hm⟩ : ∃ m, N.card = m + 1 := ⟨N.card - 1, by have := hN.card_pos; omega⟩
  exact (oddCentralSplit_specialLinearGroup (m := m) (F := F)).of_mulEquiv
    (blockSLEquiv N (N.equivFinOfCardEq hm))

end CFSG.SeitzReduction.LinearPilot
