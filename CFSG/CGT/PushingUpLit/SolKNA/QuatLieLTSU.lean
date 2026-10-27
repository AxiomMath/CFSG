module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTAbs
public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTSUData

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Generic


theorem kill3At_PSU_four : Kill3At .PSU 4 := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  left
  have hadm : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, fun h => by simpa using congrArg Prod.snd h⟩
  obtain ⟨R₀, hR₀, z₀, w₀, hz₀R, hz₀2, hz₀1, hzw, hcomm⟩ := LTSU.four_data
  exact LTTwin.twin_of_family ψ hker
    (fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
      (t := .PSU) (n := 4) (e := 1) (by norm_num) trivial hadm (by decide) (by decide) hR)
    (fun R hR r hr h => ModelFacts.fundNoncentral_generic 3 .PSU 4 1 trivial hadm
      (by rintro ⟨h, -⟩; cases h) R hR r hr h)
    (R₀ := R₀) (fun R hR => ModelFacts.fundamentalSingleClass .PSU 4 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide) R₀ hR₀ R hR)
    hz₀R hz₀2 hz₀1 hzw hcomm R hR t ht ht2

theorem kill3At_PSU_ge5 (n : ℕ) (hn : 5 ≤ n) : Kill3At .PSU n := by
  intro X _ _ ψ hψ hker R hR t ht ht2 _
  right
  have hadm : StatedLieAdmissible .PSU n 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, fun h => by simpa using congrArg Prod.snd h⟩
  obtain ⟨R₀, hR₀, z₀, hz₀R, hz₀2, hz₀1, E₀, hC, hN, hq, hE⟩ := LTSU.comp_data n hn
  exact LTAbs.component_of_family ψ hψ hker
    (fundamentalSubgroups .PSU (modelUniv .PSU n 3 1 Nat.prime_three).D)
    (fun R hR => ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3)
      (t := .PSU) (n := n) (e := 1) (by norm_num) trivial hadm (by decide) (by decide) hR)
    (fun R hR r hr h => ModelFacts.fundNoncentral_generic 3 .PSU n 1 trivial hadm
      (by rintro ⟨h, -⟩; cases h) R hR r hr h)
    (R₀ := R₀) (fun R hR => ModelFacts.fundamentalSingleClass .PSU n 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide) R₀ hR₀ R hR)
    hz₀R hz₀2 hz₀1 hC hN hq hE R hR t ht ht2

theorem lie3At_PSU (n : ℕ) : Lie3At .PSU n := by
  by_cases h3 : n = 3
  · subst h3
    exact lie3At_of_survivor (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · by_cases h4 : n = 4
    · subst h4
      exact lie3At_of_kill (by decide) (by decide) kill3At_PSU_four
    · by_cases h5 : 5 ≤ n
      · exact lie3At_of_kill (by decide) (by decide) (kill3At_PSU_ge5 n h5)
      · intro _ hadm
        exfalso
        have := hadm.2.2.1
        omega

end CFSG.CGT.PushingUpLit.SolKNA
