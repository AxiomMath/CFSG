module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Fpf.Cyclic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Fpf

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem eq_bot_or_eq_top_of_fixedFree (α β ν : V →ₗ[ZMod 2] V) (hα : α ^ 5 = 1) (hβ : β ^ 5 = 1)
    (hαβ : β * α = α * β) (hνα : ν * α = α * ν) (hνβ : ν * β = β ^ 4 * ν)
    (hν : Function.Injective ν) (h8 : finrank (ZMod 2) V = 8)
    (hα' : LinearMap.ker (α - 1) = ⊥) (hβ' : LinearMap.ker (β - 1) = ⊥)
    (U : Submodule (ZMod 2) V) (hUα : ∀ u ∈ U, α u ∈ U) (hUβ : ∀ u ∈ U, β u ∈ U)
    (hUν : ∀ u ∈ U, ν u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  have hfixU : ∀ u ∈ U, α u = u → u = 0 := by
    intro u _ hu
    have hmem : u ∈ LinearMap.ker (α - 1) :=
      LinearMap.mem_ker.mpr (by simp [hu])
    rw [hα'] at hmem
    simpa using hmem
  have h4dvd : 4 ∣ finrank (ZMod 2) U :=
    four_dvd_finrank_of_fixedFree α hα U hUα hfixU
  have hle : finrank (ZMod 2) U ≤ 8 := by
    have := Submodule.finrank_le U
    rwa [h8] at this
  obtain ⟨k, hk⟩ := h4dvd
  have hk2 : k ≤ 2 := by omega
  have hkcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hkcases with rfl | rfl | rfl
  ·
    left
    norm_num at hk
    exact hk
  ·
    exfalso
    norm_num at hk
    have hβid := eq_self_of_conj_inv α β ν hα hβ hαβ hνα hνβ hν U hUα hUβ hUν hfixU hk
    have hle_ker : U ≤ LinearMap.ker (β - 1) := by
      intro u hu
      rw [LinearMap.mem_ker]
      simp [hβid u hu]
    have hbot : U ≤ ⊥ := by rwa [hβ'] at hle_ker
    have hzero : finrank (ZMod 2) U = 0 := Submodule.finrank_eq_zero.mpr (le_bot_iff.mp hbot)
    omega
  ·
    right
    norm_num at hk
    apply Submodule.eq_top_of_finrank_eq
    omega

end CFSG.EvenSporadicStandard.HNRecog.Fpf
