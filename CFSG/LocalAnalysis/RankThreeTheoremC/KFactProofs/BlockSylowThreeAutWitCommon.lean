module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open

section Scalars

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem subsingleton_units_of_card_two [Finite K] (hK : Nat.card K = 2) : Subsingleton Kˣ := by
  have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.1 h).1

theorem statedScalars_eq_bot_of_card_two [Finite K] (hK : Nat.card K = 2) :
    StatedScalars ι K = ⊥ := by
  have := subsingleton_units_of_card_two hK
  refine eq_bot_iff.2 ?_
  rintro _ ⟨c, rfl⟩
  rw [Subsingleton.elim c 1, map_one]
  exact Subgroup.one_mem _

theorem orderOf_mk_statedProj [Finite K] (hK : Nat.card K = 2) {H : Subgroup (GL ι K)} (g : H) :
    orderOf (QuotientGroup.mk g : StatedProj H) = orderOf g := by
  have hb : (StatedScalars ι K).subgroupOf H = ⊥ := by
    rw [statedScalars_eq_bot_of_card_two hK]
    exact Subgroup.bot_subgroupOf _
  let f : H →* StatedProj H := QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)
  have hinj : Function.Injective f :=
    (MonoidHom.ker_eq_bot_iff f).1 (by rw [QuotientGroup.ker_mk', hb])
  exact orderOf_injective f hinj g

theorem exists_orderOf_eq_of_equiv_statedProj [Finite K] (hK : Nat.card K = 2) {X : Type}
    [Group X] {H : Subgroup (GL ι K)} (e : X ≃* StatedProj H) {m : ℕ} (g : H)
    (hg : orderOf g = m) : ∃ x : X, orderOf x = m := by
  refine ⟨e.symm (QuotientGroup.mk g), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_mk_statedProj hK, hg]

end Scalars

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
