module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTAbs
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTSpData

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open scoped MatrixGroups
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Generic


theorem kill3At_PSp (n : ℕ) (hn : 2 ≤ n) : Kill3At .PSp n := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  have hadm : StatedLieAdmissible .PSp n 3 1 :=
    ⟨Nat.prime_three, le_rfl, hn, fun h => by simpa using congrArg Prod.snd h⟩
  have hsl2 : ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSp) (n := n)
      (e := 1) (by norm_num) trivial hadm (by decide) (by decide) hR
  have hnc : ∀ R ∈ fundamentalSubgroups .PSp (modelUniv .PSp n 3 1 Nat.prime_three).D,
      ∀ r ∈ R, (∀ y : (modelUniv .PSp n 3 1 Nat.prime_three).K,
        r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center _) → r = 1 := fun R hR r hr h =>
    ModelFacts.fundNoncentral_generic 3 .PSp n 1 trivial hadm (by rintro ⟨h, -⟩; cases h) R hR r
      hr h
  have hsingle := ModelFacts.fundamentalSingleClass .PSp n 3 1 Nat.prime_three trivial hadm
    (by decide) (by decide)
  by_cases hn2 : n = 2
  · subst hn2
    left
    obtain ⟨R₀, hR₀, z₀, w₀, hz₀R, hz₀2, hz₀1, hzw, hcomm⟩ := LTSp.two_data
    exact LTTwin.twin_of_family ψ hker _ hsl2 hnc (R₀ := R₀)
      (fun R hR => hsingle R₀ hR₀ R hR) hz₀R hz₀2 hz₀1 hzw hcomm R hR t ht ht2
  · right
    obtain ⟨R₀, hR₀, z₀, hz₀R, hz₀2, hz₀1, E₀, hC, hN, hq, hE⟩ := LTSp.comp_data n (by omega)
    exact LTAbs.component_of_family ψ hψ hker _ hsl2 hnc (R₀ := R₀)
      (fun R hR => hsingle R₀ hR₀ R hR) hz₀R hz₀2 hz₀1 hC hN hq hE R hR t ht ht2

theorem lie3At_PSp (n : ℕ) : Lie3At .PSp n := by
  by_cases h2 : 2 ≤ n
  · exact lie3At_of_kill (by decide) (by decide) (kill3At_PSp n h2)
  · intro _ hadm
    exfalso
    have := hadm.2.2.1
    omega

end CFSG.CGT.PushingUpLit.SolKNA
