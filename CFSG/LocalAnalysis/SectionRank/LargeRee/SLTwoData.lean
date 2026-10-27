module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneData
public import CFSG.LocalAnalysis.SectionRank.LargeRee.RankOneLift

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg Matrix

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem rankOneCells_zero
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    RankOneCells a 0 (blockT a hK 0) := by
  obtain ⟨ψ, -, -, -, hU, hsurj, hdiag, hweyl⟩ := exists_sl2_rankOne hK
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hn : relNrepHom K a (blockGen 0) = ψ sl2Weyl := Subtype.ext hweyl.symm
  have hX : ∀ c, ψ (sl2Upper c) ∈ blockX (K := K) a 0 := fun c => hU c
  have hT : ∀ u : Kˣ, ψ (sl2Diag u) ∈ blockT a hK 0 := fun u =>
    ⟨u, Subtype.ext (hdiag u).symm⟩
  intro x hx
  obtain ⟨c, hc⟩ := hsurj x x.2 hx
  obtain rfl : ψ (sl2Upper c) = x := Subtype.ext hc
  by_cases hc0 : c = 0
  · subst hc0
    refine .inl ⟨1, one_mem _, 1, one_mem _, ?_⟩
    rw [hn, ← map_mul, ← map_mul, sl2Weyl_mul_sl2Upper_zero_mul_sl2Weyl, map_one, mul_one]
  · refine .inr ⟨ψ (sl2Diag (Units.mk0 c hc0)⁻¹), hT _, ψ (sl2Upper c), hX c,
      ψ (sl2Upper c⁻¹), hX _, ?_⟩
    rw [hn, ← map_mul, ← map_mul, sl2Weyl_mul_sl2Upper_mul_sl2Weyl c hc0, map_mul, map_mul,
      map_mul]

theorem rankOneSection_zero
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) {E : Type*}
    [Group E] [Finite E] {π : E →* reeFixed ReeTag.F4 K a} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) :
    RankOneSection a π 0 (blockT a hK 0) := by
  obtain ⟨ψ, hψinj, -, -, hU, hsurj, hdiag, hweyl⟩ := exists_sl2_rankOne hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hC : ¬ 2 ∣ Nat.card π.ker := fun h2 =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
  obtain ⟨ρ', hρ', -⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := 2) hπ hcen hC ψ
  refine ⟨ψ.range, ρ'.comp (MonoidHom.ofInjective hψinj).symm.toMonoidHom, fun g => ?_,
    fun x hx => ?_, ?_, ⟨sl2Weyl, Subtype.ext hweyl⟩⟩
  · rw [MonoidHom.comp_apply, ← MonoidHom.comp_apply π, hρ', MulEquiv.coe_toMonoidHom,
      ← MonoidHom.ofInjective_apply hψinj, MulEquiv.apply_symm_apply]
  · obtain ⟨c, hc⟩ := hsurj x x.2 hx
    exact ⟨sl2Upper c, Subtype.ext hc⟩
  · rintro _ ⟨u, rfl⟩
    exact ⟨sl2Diag u, Subtype.ext (hdiag u)⟩

end CFSG.SectionRank.LargeRee
