module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Harris
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Quot
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S9Count

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Open
  CFSG.EvenSporadicStandard.HSStd

@[expose] def H2Prop (X : Type) [Group X] : Prop :=
  ∃ τ : X, orderOf τ = 2 ∧ Nonempty (↥(centralizer ({τ} : Set X)) ≃*
    Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6)))

@[expose] def H3Prop (X : Type) [Group X] : Prop :=
  ∃ y : X, orderOf y = 3 ∧ Nonempty (↥(centralizer ({y} : Set X)) ⧸
    fusionOddCore ↥(centralizer ({y} : Set X)) ≃* Equiv.Perm (Fin 5))

section Transport

variable {G : Type} [Group G] [Finite G]

theorem H2Prop.transport {T T' : G} (h : T = T') (hp : H2Prop (QuotT T)) : H2Prop (QuotT T') := by
  subst h; exact hp

theorem nonempty_quotT_transport {T T' : G} (h : T = T')
    (hp : Nonempty (QuotT T ≃* NativeSporadic.HS)) : Nonempty (QuotT T' ≃* NativeSporadic.HS) := by
  subst h; exact hp

end Transport

section Main

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {E W : Subgroup G} {z : G}

theorem harris_of_props (hHiS : Harris311HiS) {X : Type} [Group X] [Finite X]
    (hK : CFSG.SectionRank.IsKGroupCat X)
    (h1 : fusionOddCore X = ⊥) (h2 : H2Prop X) (h3 : H3Prop X) :
    Nonempty (X ≃* NativeSporadic.HS) := by
  obtain ⟨τ, hτ, ⟨e⟩⟩ := h2
  obtain ⟨y, hy, hyS⟩ := h3
  exact harris_hs hHiS hK h1 hτ e y hy hyS

theorem card_quotT_mul_two {T : G} (hT2 : T * T = 1) (hT1 : T ≠ 1) :
    Nat.card (QuotT T) * 2 = Nat.card ↥(Cen T) := by
  have hw2 : wOf T * wOf T = 1 := Subtype.ext hT2
  have hw1 : wOf T ≠ 1 := fun h => hT1 (congrArg Subtype.val h)
  have hwo : orderOf (wOf T) = 2 := orderOf_eq_two_of_sq hw2 hw1
  have := (zpowers (wOf T)).card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_zpowers, hwo] at this
  rw [this]

theorem fusionOddCore_quotT (hb : PAB G L t E W z) {T : G} (hT2 : orderOf T = 2) :
    fusionOddCore (QuotT T) = ⊥ := by
  have hTT : T * T = 1 := mul_self_eq_one_of_orderOf_eq_two_fullness hT2
  have hT1 : T ≠ 1 := fun h => by rw [h, orderOf_one] at hT2; omega
  have hw2 : wOf T * wOf T = 1 := Subtype.ext hTT
  have hw1 : wOf T ≠ 1 := fun h => hT1 (congrArg Subtype.val h)
  exact s3l_fusionOddCore_quot_zpowers hw2 hw1 (wOf_central T) (hb.setting.1.oddCore T hT2)

theorem autCentralizer_not_five_of_one {X : Type} [Group X] [Finite X]
    (hO : fusionOddCore X = ⊥) (hcard : 120 < Nat.card X) :
    ¬ Nonempty (↥(autCentralizer (1 : MulAut X)) ⧸ fusionOddCore ↥(autCentralizer (1 : MulAut X)) ≃*
      Equiv.Perm (Fin 5)) := by
  rintro ⟨e⟩
  set Y : Subgroup X := autCentralizer (1 : MulAut X) with hY
  let f : ↥Y →* X := Y.subtype
  have hfinj : Function.Injective f := Y.subtype_injective
  have hmem : ∀ g : X, g ∈ Y := fun g => by
    show (1 : MulAut X) g = g
    exact MulAut.one_apply X g
  have hfsurj : Function.Surjective f := fun g => ⟨⟨g, hmem g⟩, rfl⟩
  have hOY : fusionOddCore ↥Y = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hn : ((fusionOddCore ↥Y).map f).Normal := Subgroup.Normal.map inferInstance f hfsurj
    have hdvd : Nat.card ((fusionOddCore ↥Y).map f) ∣ Nat.card (fusionOddCore ↥Y) :=
      Subgroup.card_map_dvd _ _
    have hodd : Odd (Nat.card ((fusionOddCore ↥Y).map f)) :=
      Odd.of_dvd_nat (natCard_fusionOddCore_odd' _) hdvd
    have hle := le_fusionOddCore_of_odd' (N := (fusionOddCore ↥Y).map f) hodd
    rw [hO] at hle
    have : f x ∈ (fusionOddCore ↥Y).map f := ⟨x, hx, rfl⟩
    have h1 : f x = 1 := by simpa using hle this
    exact (Subgroup.mem_bot.2 (hfinj (h1.trans (map_one f).symm)))
  have h1 := (fusionOddCore ↥Y).card_eq_card_quotient_mul_card_subgroup
  have h2 : Nat.card ↥(fusionOddCore ↥Y) = 1 := by rw [hOY]; exact Subgroup.card_bot
  have h3 : Nat.card ↥Y = Nat.card X :=
    Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  have h4 : Nat.card (↥Y ⧸ fusionOddCore ↥Y) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  rw [h2, h4, h3] at h1
  omega

end Main

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
