module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.LieType.SeitzGeneration

section Planes

variable {K : Type*} [Group K] {p : ℕ}

theorem exists_plane_le_of_card_eq_cube {G : Type*} [Group G] (hp : p.Prime) {D : Subgroup G}
    (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 3) :
    ∃ E : Subgroup G, E ≤ D ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite D := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 3 hp.ne_zero)
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := D) p (n := 2)
    (by rw [hcard]; exact pow_dvd_pow p (by norm_num))
  refine ⟨E'.map D.subtype, Subgroup.map_subtype_le _, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨x, -, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, -, rfl⟩⟩ := b
    apply Subtype.ext
    change (x : G) * y = y * x
    exact congrArg (fun z : D => (z : G)) (hD.1.is_comm.comm x y)
  · rintro _ ⟨x, -, rfl⟩
    exact hD.2 x x.2
  · rw [Subgroup.card_map_of_injective D.subtype_injective, hE']

theorem IsLocallyBalancedAbs.three_of_two (hp : p.Prime) (h : IsLocallyBalancedAbs p 2 K) :
    IsLocallyBalancedAbs p 3 K := by
  intro D hD hcard H hH hDH
  obtain ⟨E, hED, hE, hEc⟩ := exists_plane_le_of_card_eq_cube hp hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (h E hE hEc H hH (hED.trans hDH)).le)

theorem isInnerLocallyBalanced_of_innerPlanes (hp : p.Prime)
    (h : ∀ E : Subgroup (MulAut K), E ≤ innerAut K → IsElemAbelian p E → Nat.card E = p ^ 2 →
      ∀ H : Subgroup (MulAut K), innerAut K ≤ H → localDeltaIn p H E = ⊥) :
    IsInnerLocallyBalanced p K := by
  intro D hD hcard hDin H hH _
  obtain ⟨E, hED, hE, hEc⟩ := exists_plane_le_of_card_eq_cube hp hD hcard
  exact le_bot_iff.1 ((localDeltaIn_antitone H hED).trans
    (h E (hED.trans hDin) hE hEc H hH).le)

end Planes

section Families

theorem CrossCharFamAt.of_two {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
      idx.1.characteristic ≠ p → R idx p → IsLocallyBalancedAbs p 2 (Cat idx)) :
    CrossCharFamAt k R := fun idx hk p hp hp2 hc hR =>
  IsLocallyBalancedAbs.three_of_two hp (h idx hk p hp hp2 hc hR)

theorem CrossCharInnerAt.of_two {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h : ∀ idx : TauCeti.ValidLieTypeIndex, k.Matches idx.1 → ∀ p : ℕ, p.Prime → p ≠ 2 →
      idx.1.characteristic ≠ p → R idx p → IsLocallyBalancedAbs p 2 (Cat idx)) :
    CrossCharInnerAt k R :=
  (CrossCharFamAt.of_two h).innerAt

theorem CrossCharInnerAt.of_split {k : LieFamily} {R : TauCeti.ValidLieTypeIndex → ℕ → Prop}
    (h3 : CrossCharInnerAt k fun idx p => R idx p ∧ p = 3)
    (h5 : CrossCharInnerAt k fun idx p => R idx p ∧ p = 5)
    (h7 : CrossCharInnerAt k fun idx p => R idx p ∧ 7 ≤ p) : CrossCharInnerAt k R := by
  intro idx hk p hp hp2 hc hR
  rcases eq_three_or_five_le hp hp2 with rfl | h5'
  · exact h3 idx hk 3 hp hp2 hc ⟨hR, rfl⟩
  · rcases Nat.lt_or_ge p 7 with h7' | h7'
    · rcases (by omega : p = 5 ∨ p = 6) with rfl | rfl
      · exact h5 idx hk 5 hp hp2 hc ⟨hR, rfl⟩
      · exact absurd hp (by norm_num)
    · exact h7 idx hk p hp hp2 hc ⟨hR, h7'⟩

end Families

end CFSG.HardMathSupport.Timmesfeld.CrossChar
