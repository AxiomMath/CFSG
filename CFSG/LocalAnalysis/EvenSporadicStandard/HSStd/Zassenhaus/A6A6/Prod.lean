module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.A6A6.Config

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup

theorem sup_mulEquiv_prod {G : Type*} [Group G] {C D : Subgroup G}
    (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) (hinf : C ⊓ D = ⊥) :
    Nonempty (↥(C ⊔ D) ≃* C × D) := by
  have hc : ∀ (a : C) (b : D), Commute (C.subtype a) (D.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  have hd : Disjoint C D := disjoint_iff.2 hinf
  have hinj := (MonoidHom.noncommCoprod_injective C.subtype D.subtype hc).2
    ⟨Subtype.val_injective, Subtype.val_injective, by simpa [Subgroup.range_subtype] using hd⟩
  have hrange := MonoidHom.noncommCoprod_range C.subtype D.subtype hc
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hrange
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

theorem card_sup_of_comm {G : Type*} [Group G] {C D : Subgroup G}
    (hcomm : ∀ x ∈ C, ∀ y ∈ D, x * y = y * x) (hinf : C ⊓ D = ⊥) :
    Nat.card ↥(C ⊔ D) = Nat.card C * Nat.card D := by
  obtain ⟨e⟩ := sup_mulEquiv_prod hcomm hinf
  rw [Nat.card_congr e.toEquiv, Nat.card_prod]

variable {V : Type} [Group V] {G : Type} [Group G] {ρ : G →* MulAut V}

theorem Config.nonempty_sup_equiv (c : Config ρ) :
    Nonempty (↥(c.C ⊔ c.D) ≃* alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := sup_mulEquiv_prod c.comm c.inf_CD
  exact ⟨e.trans (MulEquiv.prodCongr c.eC c.eD)⟩

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem Config.card_sup (c : Config ρ) : Nat.card ↥(c.C ⊔ c.D) = 129600 := by
  rw [card_sup_of_comm c.comm c.inf_CD, Nat.card_congr c.eC.toEquiv, Nat.card_congr c.eD.toEquiv,
    card_alternatingGroup_six]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
