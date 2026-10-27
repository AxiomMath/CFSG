module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.ConjClassCount

public section

namespace CFSG.EvenSporadicStandard.HSStd.HFI

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

theorem card_carrier_mul_card_centralizer {G : Type*} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier * Nat.card (centralizer ({x} : Set G)) = Nat.card G := by
  rw [← CFSG.EvenSporadicStandard.SuzOuter.card_conj_mul_card_centralizer x]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    exact ⟨c⁻¹, by rw [← hc]; group⟩
  · rintro ⟨c, hc⟩
    exact ⟨c⁻¹, by rw [hc]; group⟩

theorem conjClass_of_tabs_gen {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {x : H} {O : List Tab}
    (hs : ∀ t ∈ O, ∃ c ∈ H, TabRep t (c * (x : Equiv.Perm (Fin n)) * c⁻¹))
    (hc : ∀ c ∈ H, ∃ t ∈ O, TabRep t (c * (x : Equiv.Perm (Fin n)) * c⁻¹)) (hn : O.Nodup) :
    (∀ y : H, IsConj y x ↔ ∃ t ∈ O, TabRep t (y : Equiv.Perm (Fin n))) ∧
      Nat.card (ConjClasses.mk x).carrier = O.length := by
  have hy : ∀ y : H, IsConj y x ↔ ∃ t ∈ O, TabRep t (y : Equiv.Perm (Fin n)) := by
    intro y
    rw [isConj_comm, isConj_iff]
    constructor
    · rintro ⟨c, rfl⟩
      simpa using hc c c.2
    · rintro ⟨t, ht, hr⟩
      obtain ⟨c, hcH, hcr⟩ := hs t ht
      exact ⟨⟨c, hcH⟩, Subtype.ext (by simpa using (hcr.perm_eq hr))⟩
  refine ⟨hy, ?_⟩
  rw [← Nat.card_image_of_injective Subtype.coe_injective]
  apply card_set_of_tabs _ _ hn
  · intro t ht
    obtain ⟨c, hcH, hcr⟩ := hs t ht
    refine ⟨_, ⟨⟨_, H.mul_mem (H.mul_mem hcH x.2) (H.inv_mem hcH)⟩, ?_, rfl⟩, hcr⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm,
      isConj_iff]
    exact ⟨⟨c, hcH⟩, rfl⟩
  · rintro _ ⟨y, hyc, rfl⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hyc
    exact (hy y).1 hyc

end CFSG.EvenSporadicStandard.HSStd.HFI
