module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

theorem one_add_two_pow_sq (m : ℕ) (hm : 1 ≤ m) :
    ((1 : ZMod (2 ^ (m + 1))) + 2 ^ m) * (1 + 2 ^ m) = 1 := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have h0 : (2 : ZMod (2 ^ (m' + 1 + 1))) ^ (m' + 1 + 1) = 0 := by
    have := ZMod.natCast_self (2 ^ (m' + 1 + 1))
    exact_mod_cast this
  linear_combination (1 + 2 ^ m') * h0

theorem two_pow_add_two_pow (m : ℕ) : (2 : ZMod (2 ^ (m + 1))) ^ m + 2 ^ m = 0 := by
  have h0 : (2 : ZMod (2 ^ (m + 1))) ^ (m + 1) = 0 := by
    have := ZMod.natCast_self (2 ^ (m + 1))
    exact_mod_cast this
  linear_combination h0

section Psi


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {S₁ : Sylow 2 Y} {R₁ R₂ : Subgroup Y} {t₁ u₁ u₂ : Y}

theorem card_R₁ (hr : 4 ≤ r) (hP : PerpHypR r n Y R S t)
    (hyp : T7F25.Asc77.Hyp25 (CoreAssembly.conjClass (tightCore R)) (tightCore R) K' W S₁ R₁ R₂ t
      t₁ u₁ u₂) : Nat.card R₁ = 2 ^ r := by
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  have hsyl := hP.core.datum.sylow_core
  rw [hR₁.natCard_eq hsyl, Subgroup.card_map_of_injective R.subtype_injective]
  obtain ⟨e⟩ := hP.core.quat
  haveI : NeZero (2 ^ (r - 2)) := ⟨by positivity⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card,
    show 4 * 2 ^ (r - 2) = 2 ^ r by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      congr 1
      omega]

end Psi

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
