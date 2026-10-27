module

public import CFSG.Goldschmidt.Steps.G211T

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.QuasithinUnique G2
open scoped Pointwise

theorem G211_of : S_G211 := by
  have h211T := G211T
  intro G _ _ A X y h hI hN
  by_cases hT : ∀ b ∈ A, ∀ c ∈ A, b ≠ 1 → c ≠ 1 → ∃ x ∈ X, x⁻¹ * b * x = c
  · exact h211T G A X y h hI hN hT
  exfalso
  have : Fact (IsElemAbelian 2 A) := ⟨h.elem⟩
  have hL := linHyp_of_onanHyp h
  set ρ := conjRep h.le with hρ
  set η := ρ ⟨y, h.mem⟩ with hη
  have hXt : ¬ ONan.IsTransitiveNonzero ρ.range := fun ht =>
    hT ((transitive_iff_of_onanHyp h).mpr ht)
  have hnorm := normalizes_of_onanHyp h hN
  have hCV : fixSp η ≠ ⊤ := by
    intro h0
    apply hL.comSp_ne_bot
    have := hL.isCompl.inf_eq_bot
    rwa [h0, inf_top_eq] at this
  have hR : ONan.IsTransitiveOnSummand (Subgroup.zpowers η) (comSp η) (fixSp η) :=
    ⟨fun r hr a ha => apply_mem_comSp (mul_comm_of_mem_zpowers hr) ha,
      fun r hr c hc => apply_eq_of_mem_zpowers hr hc,
      fun a ha b hb ha0 hb0 => hL.exists_zpowers ha hb ha0 hb0⟩
  have hTI : ONan.IsTI ρ.range (fixSp η) := by
    intro x hx hne
    by_contra hxC
    apply hne
    rw [inf_comm]
    exact hL.ti x hx hxC
  have hRnorm : ∀ x ∈ ρ.range, ONan.image x (fixSp η) = fixSp η →
      ∀ r ∈ Subgroup.zpowers η, x * r * x⁻¹ ∈ Subgroup.zpowers η := by
    intro x hx hxC r hr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hnorm x hx hxC) j
  have horb := ONan.onan_irreducible_intransitive_TI ρ.range (Subgroup.zpowers η) hL.zpowers_le
    (irreducible_of_onanHyp h) hXt (comSp η) (fixSp η) hL.isCompl hL.two_le_finrank_comSp
    hL.fixSp_ne_bot hCV hR inferInstance
    (fun r hr a ha ha0 hra => hL.eq_one_of_apply_eq hr ha ha0 hra) hTI hRnorm
  have horb' : MulAction.orbit ρ.range (fixSp η) = ONan.orbit ρ.range (fixSp η) := by
    ext D
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hidx2 : (MulAction.stabilizer ρ.range (fixSp η)).index = 2 := by
    rw [MulAction.index_stabilizer, horb', horb]
  apply index_ne_two_of_onanHyp h hI ((MulAction.stabilizer ρ.range (fixSp η)).map ρ.range.subtype)
    (Subgroup.map_subtype_le _)
  rw [show ((MulAction.stabilizer ρ.range (fixSp η)).map ρ.range.subtype).subgroupOf ρ.range =
      MulAction.stabilizer ρ.range (fixSp η) from
    Subgroup.comap_map_eq_self_of_injective ρ.range.subtype_injective _]
  exact hidx2

theorem G211 : S_G211 := G211_of

end CFSG.Goldschmidt
