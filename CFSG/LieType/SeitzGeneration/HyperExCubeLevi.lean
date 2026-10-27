module

public import CFSG.LieType.SeitzGeneration.HyperExCubeTw
public import CFSG.HardMathSupport.Malle.SeitzCube.E7ThreeCube
public import CFSG.HardMathSupport.Malle.SeitzCube.E8CubeAll

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbedding TauCeti
open CFSG.HardMathSupport.Malle.SeitzCube (ExcCubeHighAt excCubeHigh_E7_of_at
  excCubeHighAt_E7_three)

theorem orderOf_ne_one_two {p q : ℕ} (hp : p.Prime) (hq : 1 ≤ q) (hpq : ¬ p ∣ q ^ 2 - 1) :
    orderOf ((q : ℕ) : ZMod p) ≠ 1 ∧ orderOf ((q : ℕ) : ZMod p) ≠ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have key : orderOf ((q : ℕ) : ZMod p) ∣ 2 → False := by
    intro h
    have h2 : ((q : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h
    apply hpq
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, h2,
      Nat.cast_one, sub_self]
  exact ⟨fun h => key (by rw [h]; exact one_dvd 2), fun h => key (dvd_of_eq h)⟩

theorem excCubeHigh_E6_of_at (h : ExcCubeHighAt LieTypeIndex.E6 3) :
    ExcCubeHigh .E6 LieTypeIndex.E6 := by
  intro q hv p hp hp2 hpq hl hpq2 hcnt hE₀
  have h12 := orderOf_ne_one_two hp
    (by rw [PrimePower.card_def]; exact Nat.one_le_pow _ _ q.prime_p.pos) hpq2
  have hle : orderOf ((q.card : ℕ) : ZMod p) ≤ 30 :=
    le_thirty_of_degCount_pos (τ := .E6) (by simp) (by omega)
  have key : ∀ o ≤ 30, 3 ≤ degCount .E6 o → o = 1 ∨ o = 2 ∨ o = 3 := by decide
  rcases key _ hle hcnt with h1 | h1 | h1
  · exact absurd h1 h12.1
  · exact absurd h1 h12.2
  · exact h q hv p hp hp2 hpq hl hpq2 h1 hE₀

theorem excCubeHighTw_of_at (h : ExcCubeHighAt LieTypeIndex.twistedE6 6) : ExcCubeHighTw := by
  intro q hv p hp hp2 hpq hl hpq2 hcnt hE₀
  have h12 := orderOf_ne_one_two hp
    (by rw [PrimePower.card_def]; exact Nat.one_le_pow _ _ q.prime_p.pos) hpq2
  have hle : orderOf ((q.card : ℕ) : ZMod p) ≤ 60 := le_sixty_of_degCountTw_pos (by omega)
  have key : ∀ o ≤ 60, 3 ≤ degCountTw o → o = 1 ∨ o = 2 ∨ o = 6 := by decide
  rcases key _ hle hcnt with h1 | h1 | h1
  · exact absurd h1 h12.1
  · exact absurd h1 h12.2
  · exact h q hv p hp hp2 hpq hl hpq2 h1 hE₀

structure ExcCubeResidualsV4 : Prop where
  e6Three : ExcCubeHighAt LieTypeIndex.E6 3
  e7Six : ExcCubeHighAt LieTypeIndex.E7 6
  twE6Six : ExcCubeHighAt LieTypeIndex.twistedE6 6


theorem ExcCubeResidualsV4.toV3 (h : ExcCubeResidualsV4) : ExcCubeResidualsV3 where
  e6High := excCubeHigh_E6_of_at h.e6Three
  e7High := excCubeHigh_E7_of_at excCubeHighAt_E7_three h.e7Six
  e8High := CFSG.HardMathSupport.Malle.SeitzCube.excCubeHigh_E8
  twE6High := excCubeHighTw_of_at h.twE6Six

end CFSG.LieType.SeitzGeneration
