module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.FS79Co3
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Layer0

public section

namespace CFSG.EvenSporadicStandard.M12Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def FS79M12InnerAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StdHyp G L → IsSporadic L .M12 →
    ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
      centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G)

section Co3

theorem centralizer_le_sup_of_isSporadic_co3 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (h : StdHyp G L) (hL : IsSporadic L .M12) (hG : IsSporadic G .Co3) {t : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G) := by
  have hZ : center L = ⊥ := center_eq_bot_of_isSporadic_m12 hL
  have hdisj : Disjoint L (zpowers t) :=
    disjoint_of_le_centralizer_of_center_eq_bot (zpowers_le.2 ht) hZ
  have hcardsup : Nat.card ↥(L ⊔ zpowers t) = Nat.card L * 2 := by
    rw [← Nat.card_congr (mulEquivProdSup (zpowers_le.2 ht) hdisj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, ht2]
  have hL95 : Nat.card L = 95040 := by
    obtain ⟨eL⟩ := hL
    rw [Nat.card_congr eL.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  have hle : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (h.component_of_involution ht ht2).1
      (zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl))
  have hdvd : Nat.card ↥(L ⊔ zpowers t) ∣ Nat.card (centralizer ({t} : Set G)) :=
    Subgroup.card_dvd_of_le hle
  rcases card_centralizer_of_isSporadic_co3 hG ht2 with h1 | h1
  · rw [hcardsup, hL95, h1] at hdvd
    norm_num at hdvd
  · have heq : L ⊔ zpowers t = centralizer ({t} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h1, hcardsup, hL95])
    rw [← heq]
    exact sup_le_sup_left (zpowers_le.2 ht) L

end Co3

end CFSG.EvenSporadicStandard.M12Std
