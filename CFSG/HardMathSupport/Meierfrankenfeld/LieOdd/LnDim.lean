module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnLift
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.LnOrbit

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.LocalAnalysis.ComponentInitial

theorem two_pow_le_card_of_psln {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {K : Type} [Field K] [Finite K] {p e n : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ e) (hn : 3 ≤ n) {L : Subgroup (MulAut W)}
    (π : ↥L →* LinearFlag.projectiveSL n K)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker) :
    2 ^ (orderOf (2 : ZMod p) * ((p ^ (e * (n - 1)) - 1) / (p - 1))) ≤ Nat.card W := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hτ : (Algebra.trace (ZMod p) K) ≠ 0 := by
    intro h
    obtain ⟨a, ha⟩ := Algebra.trace_surjective (ZMod p) K 1
    rw [h] at ha
    exact zero_ne_one ha
  have h := two_pow_le_card_of_lift_orbit hW hp2 π hπ hker hZ
    (U₀ := (uHom (K := K) (m := m)).range) (T₀ := (tHom (K := K) (m := m)).range)
    uHom_range_comm uHom_range_pow (uHom_range_ne_bot (by omega)) tHom_range_le_normalizer
    (m := (Nat.card K ^ m - 1) / (p - 1)) (fun D₀ hD hrel => orbit_bound hm hτ hD hrel)
  rw [hK, ← pow_mul] at h
  rw [Nat.add_sub_cancel, mul_comm]
  exact h

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
