module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Rank0

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator

theorem pRank_eq_of_card_eq {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : IsElemAbelian p H) {n : ℕ} (hn : Nat.card H = p ^ n) :
    CFSG.Open.pRank p H = n := by
  unfold CFSG.Open.pRank
  apply IsGreatest.csSup_eq
  refine ⟨⟨H, le_rfl, hH, hn⟩, ?_⟩
  rintro k ⟨E, hEH, -, hEk⟩
  have h1 : Nat.card E ≤ Nat.card H := Subgroup.card_le_of_le hEH
  rw [hEk, hn] at h1
  exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem isElemAbelian_of_mulEquiv {S : Type} [Group S] [Finite S]
    (V : Subgroup (MulAut S)) (φ : V ≃* Multiplicative (Fin 6 → ZMod 3)) :
    IsElemAbelian 3 V := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply φ.injective
    rw [map_mul, map_mul, mul_comm]
  · have h : (⟨x, hx⟩ : V) ^ 3 = 1 := by
      apply φ.injective
      rw [map_pow, map_one]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_pow, toAdd_one]
      exact three_nsmul_eq_zero_coords _
    exact congrArg Subtype.val h

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end
