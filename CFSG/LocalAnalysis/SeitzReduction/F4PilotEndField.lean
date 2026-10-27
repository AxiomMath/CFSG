module

public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem even_F4_zpowers_finiteExceptionalAut_complement {n : ℕ} (hn : 1 ≤ n) (K : Type)
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ n) :
    (∀ β ∈ zpowers (ReeTag.F4.finiteExceptionalAut K),
      β ∈ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range → β = 1) ∧
    (∀ α : MulAut (adjointGroup ReeTag.F4.tag K), ∃ g : adjointGroup ReeTag.F4.tag K,
      ∃ β ∈ zpowers (ReeTag.F4.finiteExceptionalAut K), α = MulAut.conj g * β) ∧
    Nat.card (zpowers (ReeTag.F4.finiteExceptionalAut K)) = 2 * n := by
  obtain ⟨hord, hNF, ⟨Θ, hΘ, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hn K hK
  have : NeZero (2 * n) := ⟨by omega⟩
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ hβi
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hβ
    have hΘφ : Θ (ReeTag.F4.finiteExceptionalAut K) = Multiplicative.ofAdd (1 : ZMod (2 * n)) := by
      have h := hΘ (ReeTag.F4.finiteExceptionalAut K) 1 1 (by rw [map_one, one_mul, pow_one])
      rw [h, Nat.cast_one]
    have h1 : Θ (ReeTag.F4.finiteExceptionalAut K ^ k) = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hβi
    rw [map_zpow, hΘφ, ← ofAdd_zsmul, zsmul_one, ofAdd_eq_one,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at h1
    rw [← orderOf_dvd_iff_zpow_eq_one, hord]
    exact_mod_cast h1
  · intro α
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
    exact ⟨g, _, npow_mem_zpowers _ _, hgk⟩
  · rw [Nat.card_zpowers, hord]

end CFSG.SeitzReduction.F4Pilot
