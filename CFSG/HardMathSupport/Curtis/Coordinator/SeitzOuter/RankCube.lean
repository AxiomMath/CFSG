module

public import CFSG.LieType.SeitzGeneration.Defs

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open

theorem rankLE2_of_not_exists_cube {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ¬ ∃ E : Subgroup X, IsElemAbelian p E ∧ Nat.card E = p ^ 3) :
    CFSG.LieType.SeitzGeneration.RankLE2 p X := by
  intro F hF
  have : Fact p.Prime := ⟨hp⟩
  have : IsMulCommutative F := hF.1
  have hFp : IsPGroup p F := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hF.2 g g.2⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  by_contra hlt
  have h3 : 3 ≤ k := by
    by_contra h3
    apply hlt
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hdvd : p ^ 3 ∣ Nat.card F := by
    rw [hk]
    exact pow_dvd_pow p h3
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
  refine h ⟨K.map F.subtype, ⟨inferInstance, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    have := hF.2 (y : X) y.2
    simpa using this
  · rw [Subgroup.card_map_of_injective F.subtype_injective]
    exact hK

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

end
