module

public import CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoKernelBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6EndNode

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

public section

open CFSG.RankThree.PerfectCover CFSG.LieType.Chevalley.C2E6Std CFSG.StandardType
open CFSG.EvenSmallLie.TwoE6

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

open CFSG.RankThree.PerfectCover CFSG.LieType.Chevalley.C2E6Std CFSG.StandardType
open CFSG.EvenSmallLie.TwoE6

variable {G : Type} [Group G]
  [Finite ↥stdGroup] [Group.IsPerfect ↥stdGroup]

theorem levi34Diag_hopfCoverAut_fixed_two
    (P : Sylow 2 (hopfMultiplier ↥stdGroup)) (Q3 : Sylow 3 (hopfMultiplier ↥stdGroup)) :
    ∀ z ∈ hopfMultiplier ↥stdGroup, (∃ k : ℕ, z ^ (2 ^ k) = 1) →
      hopfCoverAut levi34Diag z = z → z = 1 :=
  fun _ hzM hz2 hfix => levi34Diag_hopfMultiplier_fixed_two_eq_one P Q3 hzM hz2 hfix

theorem quotient_actor_pow_three_of_original
    {H E : Subgroup G} {R : Type*} [Group R]
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (ψ : ↥H →* R) (hψ : Function.Surjective ψ)
    (e : ↥E) (he3 : e ^ 3 = 1) (δ : MulAut R)
    (hσ : ∀ x : ↥H, ψ (ggGamma H hEN e x) = δ (ψ x)) : δ ^ 3 = 1 := by
  apply TableBExc.pow_eq_one_of_induces hψ (fun x => (hσ x).symm)
  rw [← map_pow, he3, map_one]

theorem Z_map_inf_centralizer_eq_bot_of_two_subkernel
    {G : Type} [Group G] [Finite G] {H E Hr Hs : Subgroup G} [Group.IsPerfect ↥H]
    {Z : Subgroup ↥H}
    (ψ : ↥H →* ↥stdGroup) (hψ : Function.Surjective ψ)
    (hψker : ψ.ker ≤ Subgroup.center ↥H)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (e : ↥E) (he : (e : G) ∈ Hr ⊓ Hs) (he3 : e ^ 3 = 1)
    (δ : MulAut ↥stdGroup)
    (hσ : ∀ x : ↥H, ψ (ggGamma H hEN e x) = δ (ψ x))
    (hZ : Z ≤ ψ.ker) (hZ2 : IsPGroup 2 Z)
    (hfree : ∀ z ∈ hopfMultiplier ↥stdGroup,
      (∃ k : ℕ, z ^ (2 ^ k) = 1) → hopfCoverAut δ z = z → z = 1) :
    Z.map H.subtype ⊓ Subgroup.centralizer (Hr ⊓ Hs : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨z, hzZ, rfl⟩ := Subgroup.mem_map.mp hy.1
  have hzfix : ggGamma H hEN e z = z := by
    apply Subtype.ext
    rw [ggGamma_coe]
    have hc : (e : G) * (z : G) = (z : G) * (e : G) :=
      Subgroup.mem_centralizer_iff.mp hy.2 (e : G) he
    rw [hc]
    group
  have hzpow : ∃ k : ℕ, z ^ (2 ^ k) = 1 := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hZ2.exists_orderOf_eq_pow (⟨z, hzZ⟩ : Z)
    refine ⟨k, ?_⟩
    have hp : (⟨z, hzZ⟩ : Z) ^ (2 ^ k) = 1 := by
      rw [← hk]
      exact pow_orderOf_eq_one _
    exact congrArg Subtype.val hp
  have hδ3 := quotient_actor_pow_three_of_original hEN ψ hψ e he3 δ hσ
  have hz1 := fixed_two_element_of_hopf_lift_cube ψ hψ hψker
    (ggGamma H hEN e) δ hδ3 hσ hfree (hZ hzZ) hzpow hzfix
  simpa using congrArg Subtype.val hz1

end CFSG.LieType.Steinberg.CentralExt.TwistedE6TwoCover

end
