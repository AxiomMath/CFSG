module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Lang.D4Three

theorem exists_stable_sylow_of_order_three {G : Type*} [Group G] [Finite G] (u : MulAut G)
    (hu : u ^ 3 = 1) :
    ∃ S : Sylow 3 G, (S : Subgroup G).map u.toMonoidHom = S := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H : Subgroup (MulAut G) := Subgroup.zpowers u with hH
  have hHp : IsPGroup 3 H := by
    have hord : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (by simpa using hord : orderOf u ∣ 3 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [hH, Nat.card_zpowers, hk])
  have hmod := hHp.card_modEq_card_fixedPoints (Sylow 3 G)
  have hsyl : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hfix : Nat.card (MulAction.fixedPoints H (Sylow 3 G)) ≡ 1 [MOD 3] := hmod.symm.trans hsyl
  have hne : Nonempty (MulAction.fixedPoints H (Sylow 3 G)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints H (Sylow 3 G)) := by
      by_contra h0
      have : Nat.card (MulAction.fixedPoints H (Sylow 3 G)) = 0 := by omega
      rw [this] at hfix
      exact absurd (Nat.ModEq.symm hfix) (by decide)
    exact (Nat.card_pos_iff.1 hpos).1
  obtain ⟨⟨S, hS⟩⟩ := hne
  refine ⟨S, ?_⟩
  have h1 : (⟨u, Subgroup.mem_zpowers u⟩ : H) • S = S := hS ⟨u, Subgroup.mem_zpowers u⟩
  have h2 : (((⟨u, Subgroup.mem_zpowers u⟩ : H) • S : Sylow 3 G) : Subgroup G) = S :=
    congrArg (fun T : Sylow 3 G => (T : Subgroup G)) h1
  have h3 := (Sylow.pointwise_smul_def (g := (⟨u, Subgroup.mem_zpowers u⟩ : H)) (P := S)).symm.trans h2
  rw [Subgroup.pointwise_smul_def] at h3
  exact h3

end CFSG.HardMathSupport.Lang.D4Three
