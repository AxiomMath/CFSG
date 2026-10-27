module

public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultAlt
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def sporadicMultiplierOrder : TauCeti.SporadicName → ℕ
  | .M11 => 1 | .M12 => 2 | .M22 => 12 | .M23 => 1 | .M24 => 1
  | .J1 => 1 | .J2 => 2 | .J3 => 3 | .J4 => 1
  | .HS => 2 | .McL => 3 | .He => 1 | .Ru => 2 | .Suz => 6 | .ONan => 3
  | .Co1 => 2 | .Co2 => 1 | .Co3 => 1
  | .Fi22 => 6 | .Fi23 => 1 | .Fi24Prime => 3
  | .HN => 1 | .Ly => 1 | .Th => 1 | .B => 2 | .M => 1

@[expose] def SporadicMultiplierTable : Prop :=
  ∀ (s : TauCeti.SporadicName) (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
    ∀ π : Q →* (TauCeti.CFSGIndex.sporadic s).Group, Function.Surjective π →
      π.ker = Subgroup.center Q → Nat.card (Subgroup.center Q) ∣ sporadicMultiplierOrder s

theorem listedMultiplierBoundAt_sporadic (hSp : SporadicMultiplierTable) (p : ℕ)
    (s : TauCeti.SporadicName) : ListedMultiplierBoundAt p (.sporadic s) := by
  intro hi Q _ _ hQ π hπ hker hZ hne
  haveI hnt : Nontrivial (Subgroup.center Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hd := hSp s Q hQ π hπ hker
  have hp : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 := by
    cases s <;> simp [k2, k2Spor, k3] at hi <;> omega
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> cases s <;>
    first
    | (exfalso; simp [k2, k2Spor, k3] at hi; done)
    | (exfalso
       exact absurd (pGroup_card_of_dvd (by norm_num) hZ hnt hd).1 (by decide))
    | exact ⟨rfl, (pGroup_card_of_dvd Nat.prime_three hZ hnt hd).2 (by decide),
        by simp [CoverListed, k2HatIndex, k3HatIndex]⟩

theorem dvd_three_of_odd_of_dvd_three_mul_two_pow {z a : ℕ} (hodd : Odd z)
    (hd : z ∣ 3 * 2 ^ a) : z ∣ 3 :=
  (Nat.Coprime.pow_right a (Odd.coprime_two_right hodd)).dvd_of_dvd_mul_right hd

theorem hatOddMultiplierBoundAt_sporadic (hSp : SporadicMultiplierTable)
    (s : TauCeti.SporadicName) : HatOddMultiplierBoundAt (.sporadic s) := by
  intro hi Q _ _ hQ π hπ hker hodd
  have hd := hSp s Q hQ π hπ hker
  cases s <;> simp [k2HatIndex, k3HatIndex] at hi <;> simp only [sporadicMultiplierOrder] at hd
  all_goals first
    | exact dvd_three_of_odd_of_dvd_three_mul_two_pow (a := 0) hodd (by simpa using hd)
    | exact dvd_three_of_odd_of_dvd_three_mul_two_pow (a := 1) hodd (by simpa using hd)
    | exact dvd_three_of_odd_of_dvd_three_mul_two_pow (a := 2) hodd (by simpa using hd)

section


theorem listedMultiplierBound_of_tables (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSp : SporadicMultiplierTable) (p : ℕ) : ListedMultiplierBound p :=
  listedMultiplierBound_of_forall fun i => by
    cases i with
    | cyclic q hq => exact listedMultiplierBoundAt_cyclic p q hq
    | alternating n hn => exact listedMultiplierBoundAt_alternating p n hn
    | lie j => exact listedMultiplierBoundAt_lie hGA p j
    | sporadic s => exact listedMultiplierBoundAt_sporadic hSp p s

theorem hatOddMultiplierBound_of_tables (hSp : SporadicMultiplierTable) :
    HatOddMultiplierBound :=
  hatOddMultiplierBound_of_forall fun i => by
    cases i with
    | cyclic q hq => exact hatOddMultiplierBoundAt_cyclic q hq
    | alternating n hn => exact hatOddMultiplierBoundAt_alternating n hn
    | lie j =>
      exact fun hi => hi.elim (fun h => h.elim) (fun h => h.elim)
    | sporadic s => exact hatOddMultiplierBoundAt_sporadic hSp s

end

end CFSG.LocalAnalysis.GLTheoremA
