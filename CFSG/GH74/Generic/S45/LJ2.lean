module

public import CFSG.GH74.Generic.S45.PumpLeaves

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.Blueprint

theorem exists_e16_of_mulEquiv {K G : Type} [Group K] [Group G] (e : K ≃* G) (E : Subgroup G)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hc : Nat.card E = 16) :
    ∃ E' : Subgroup K, (∀ a ∈ E', ∀ b ∈ E', a * b = b * a) ∧ (∀ a ∈ E', a * a = 1) ∧
      Nat.card ↥E' = 16 := by
  obtain ⟨⟨hcomm⟩, hsq⟩ := hE
  refine ⟨E.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h : a * b = b * a := congrArg Subtype.val (hcomm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show e.symm a * e.symm b = e.symm b * e.symm a
    rw [← map_mul, ← map_mul, h]
  · rintro _ ⟨a, ha, rfl⟩
    have h : a * a = 1 := by rw [← sq]; exact hsq a ha
    show e.symm a * e.symm a = 1
    rw [← map_mul, h, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc]

theorem b_IA_5_3g : B_IA_5_3g := by
  intro K _ _ ⟨e⟩
  obtain ⟨E, hE, hc⟩ := CFSG.GH74.Uniqueness.SU.K.R3.exists_E16_J2
  exact ⟨@MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e,
    exists_e16_of_mulEquiv e E hE hc⟩

end CFSG.GH74.Generic.S45
