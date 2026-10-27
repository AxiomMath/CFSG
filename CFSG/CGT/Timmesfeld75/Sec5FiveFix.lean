module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.Timmesfeld75

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_of_isPGroup {P V : Subgroup G} (hP : IsPGroup 2 P)
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hV : IsPGroup 2 V) (hV1 : V ≠ ⊥) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ p ∈ P, p * v * p⁻¹ = v := by
  let _ : MulAction P V :=
    MulAction.compHom V (V.normalizerMonoidHom.comp (Subgroup.inclusion hPV))
  have hsmul : ∀ (p : P) (v : V), ((p • v : V) : G) = (p : G) * v * (p : G)⁻¹ :=
    fun p v => rfl
  have hdvd : 2 ∣ Nat.card V := by
    rcases hV.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hV1
    · exact h
  have hfix : (1 : V) ∈ MulAction.fixedPoints P V := fun p =>
    Subtype.ext (by rw [hsmul]; simp)
  obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd hfix
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun p hp => ?_⟩
  have := congrArg Subtype.val (hb ⟨p, hp⟩)
  rwa [hsmul] at this

omit [Finite G] in
theorem isPGroup_two_zpowers_of_pow_four {u : G} (hu : u ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers u) := by
  intro ⟨v, hv⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
  refine ⟨2, Subtype.ext ?_⟩
  show (u ^ n) ^ (2 ^ 2) = 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  have : u ^ ((2 ^ 2 : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    simpa using hu
  rw [this, one_zpow]

end CFSG.CGT.Timmesfeld75
