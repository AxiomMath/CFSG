module

public import CFSG.Open.StatedZModTwo
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Open.StatedAPI

open CFSG.Assembly.LowTwoRank

theorem nonempty_mulEquiv_specialLinear_zmod_two_of_psl {X : Type} [Group X] {n : ℕ}
    (h : StatedClassicalModel X .PSL n 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : Fintype K := Fintype.ofFinite K
  let ε : K ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hK2, ZMod.card])
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK2 (Fin n), Subgroup.bot_subgroupOf]
  let q : StatedProj (StatedSL n K) ≃* StatedSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let σ : Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2) :=
    MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map ε.toRingHom)
      (Matrix.SpecialLinearGroup.map ε.symm.toRingHom)
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
      (MonoidHom.ext fun A => Subtype.ext (by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]))
  exact ⟨((e.trans q).trans (specialLinearGroupEquivStatedSL n K).symm).trans σ⟩

end CFSG.Open.StatedAPI
