module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S14Catalog
public import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.GroupTheory.PerfectSubgroupNormalMeet

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup

@[expose] def ONanNoSL29N : Prop :=
  ∀ (N : Type) [Group N] [Finite N], ONanList N →
    ∀ (K : Type) [Group K] [Finite K], commutator K = ⊤ → Nat.card (center K) = 2 →
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin 6)) →
      ∀ f : K →* N, Function.Injective f → False

@[expose] def ONanOutSmall : Prop :=
  ∀ (N : Type) [Group N] [Finite N], ONanList N → Nat.card (MulAut N) < 360 * Nat.card N

@[expose] def ONanCenterFree : Prop :=
  ∀ (N : Type) [Group N] [Finite N], ONanList N → center N = ⊥

theorem onanNoSL29Y_of_facts (h1 : ONanNoSL29N) (h2 : ONanOutSmall) (h3 : ONanCenterFree) :
    PartA.ONanNoSL29Y := by
  unfold PartA.ONanNoSL29Y
  intro Y _ _ N hN hC hList H hperf hcen hA6
  classical
  obtain ⟨e⟩ := hA6
  have hs : IsSimpleGroup (↥H ⧸ center ↥H) :=
    (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
  by_cases hHN : H ≤ N
  ·
    have hK : commutator ↥H = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype, hperf]
    exact h1 ↥N hList ↥H hK hcen ⟨e⟩ (Subgroup.inclusion hHN)
      (Subgroup.inclusion_injective hHN)
  ·
    have hdvd : (center ↥H).index ∣ N.index :=
      index_center_dvd_index_of_perfect (H := H) (N := N) hperf hs hHN
    have hidx : (center ↥H).index = 360 := by
      rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
        Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    have h360dvd : 360 ∣ N.index := by rwa [hidx] at hdvd
    have h360le : 360 ≤ N.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h360dvd
    have hcard : N.index * Nat.card ↥N = Nat.card Y := Subgroup.index_mul_card N
    have hbig : 360 * Nat.card ↥N ≤ Nat.card Y := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ h360le
    have hYle : Nat.card Y ≤ Nat.card (MulAut ↥N) :=
      card_le_card_mulAut_of_centralizer_le (N := N) hC (h3 ↥N hList)
    have hAut : Nat.card (MulAut ↥N) < 360 * Nat.card ↥N := h2 ↥N hList
    omega

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
