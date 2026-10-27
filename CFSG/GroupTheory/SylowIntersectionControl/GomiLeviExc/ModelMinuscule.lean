module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiLeviExc.Model
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter
import CFSG.Timmesfeld.LieEmbed.SLE6
import CFSG.Adapters.TauCetiExceptional.EvenBridgeE6E7

public section

namespace CFSG.GroupTheory.GomiLeviExc

open Subgroup CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley

private theorem exists_primePower_two_card (k : Type) [Field k] [Finite k] [CharP k 2] :
    ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.card = Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  refine ⟨⟨2, n, Nat.prime_two, n.pos⟩, rfl, ?_⟩
  rw [TauCeti.PrimePower.card_def, ← hn, Nat.card_eq_fintype_card]

namespace MinusculeModel

variable (k : Type) [Field k]

theorem isCharTwoSteinberg_e6 [CharP k 2] :
    IsCharTwoSteinberg (e6Datum k).roots (e6Data_valid.xm k) := by
  have hroot : (e6Datum k).roots = {γ | IsRoot .E6 γ} :=
    e6Data_valid.minDatum_roots isFiniteType_cartan_E6 k
  refine ⟨fun γ _ c d => e6Data_valid.xm_add k γ c d, ?_⟩
  intro α hα β hβ hne c d
  have hα' : IsRoot .E6 α := by simpa [hroot] using hα
  have hβ' : IsRoot .E6 β := by simpa [hroot] using hβ
  by_cases h : IsRoot .E6 (α + β)
  · rw [if_pos (by simpa [hroot] using h)]
    obtain ⟨σ, hσ, hσc⟩ := (e6Data_valid.commutator_xm k hα' hβ' hne).1 h
    rw [hσc c d, CFSG.Timmesfeld.LieEmbed.isSign_eq_one hσ, one_mul]
  · rw [if_neg (by simpa [hroot] using h)]
    exact (e6Data_valid.commutator_xm k hα' hβ' hne).2 h c d

theorem isCharTwoSteinberg_e7 [CharP k 2] :
    IsCharTwoSteinberg (e7Datum k).roots (e7Data_valid.xm k) := by
  have hroot : (e7Datum k).roots = {γ | IsRoot .E7 γ} :=
    e7Data_valid.minDatum_roots isFiniteType_cartan_E7 k
  refine ⟨fun γ _ c d => e7Data_valid.xm_add k γ c d, ?_⟩
  intro α hα β hβ hne c d
  have hα' : IsRoot .E7 α := by simpa [hroot] using hα
  have hβ' : IsRoot .E7 β := by simpa [hroot] using hβ
  by_cases h : IsRoot .E7 (α + β)
  · rw [if_pos (by simpa [hroot] using h)]
    obtain ⟨σ, hσ, hσc⟩ := (e7Data_valid.commutator_xm k hα' hβ' hne).1 h
    rw [hσc c d, CFSG.Timmesfeld.LieEmbed.isSign_eq_one hσ, one_mul]
  · rw [if_neg (by simpa [hroot] using h)]
    exact (e7Data_valid.commutator_xm k hα' hβ' hne).2 h c d

variable [Finite k] [CharP k 2]

private theorem odd_card_center_e7 : Odd (Nat.card (center ↥(e7Data_valid.minGroup k))) := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k 2
  have hodd : Odd (Nat.card k - 1) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, n.ne_zero⟩) odd_one
  rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7 (k := k)).1,
    Nat.coprime_iff_gcd_eq_one.mp hodd.coprime_two_left]
  exact odd_one

section E6Catalogue

theorem isChevTwo_e6 :
    IsChevTwo (↥(e6Data_valid.minGroup k) ⧸ center ↥(e6Data_valid.minGroup k)) := by
  obtain ⟨q, hq, hcard⟩ := exists_primePower_two_card k
  have hv : (TauCeti.LieTypeIndex.E6 q).Valid := TauCeti.LieTypeIndex.valid_E6 q
  have e₁ : ↥(e6Data_valid.minGroup k) ⧸ Subgroup.center ↥(e6Data_valid.minGroup k) ≃*
      CFSG.Blueprint.AdjointQuotient .E6 k :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple
      (φ := CFSG.LieType.Steinberg.Isogeny.e6Isogeny k)
      (CFSG.LieType.CurtisTits.isQuasisimple_e6 (k := k))
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective k)
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
        (CFSG.LieType.CurtisTits.isQuasisimple_e6 (k := k))
        (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_ne_one k))
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq k hcard.symm
  exact Or.inl ⟨⟨.E6 q, hv⟩, hq, ⟨MulEquiv.trans e₁ e₂⟩⟩

theorem isCharTwoModel_e6 : IsCharTwoModel (e6Datum k) k (e6Data_valid.xm k) where
  conclusionB := e6_conclusionB k
  divisible := rfl
  isSymm := by
    change (Tag.cartan .E6).IsSymm
    rw [cartan_E6]
    exact CartanMatrix.E_isSymm 6
  steinberg := isCharTwoSteinberg_e6 k
  isQuasisimple := CFSG.LieType.CurtisTits.isQuasisimple_e6 (k := k)
  odd_card_center := by
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := k)).1]
    exact (by decide : Odd 3).of_dvd_nat (Nat.gcd_dvd_left 3 _)
  isChevTwo := isChevTwo_e6 k

theorem hasCharTwoModel_E6 : HasCharTwoModel k (CartanMatrix.E 6) :=
  ⟨_, _, e6Datum k, e6Data_valid.xm k, Equiv.refl _, fun i j => by
    change Tag.cartan .E6 i j = _
    rw [cartan_E6], isCharTwoModel_e6 k⟩

end E6Catalogue

section E7Catalogue

theorem isChevTwo_e7 :
    IsChevTwo (↥(e7Data_valid.minGroup k) ⧸ center ↥(e7Data_valid.minGroup k)) := by
  obtain ⟨q, hq, hcard⟩ := exists_primePower_two_card k
  have hv : (TauCeti.LieTypeIndex.E7 q).Valid := TauCeti.LieTypeIndex.valid_E7 q
  have e₁ : ↥(e7Data_valid.minGroup k) ⧸ Subgroup.center ↥(e7Data_valid.minGroup k) ≃*
      CFSG.Blueprint.AdjointQuotient .E7 k :=
    CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple
      (φ := CFSG.LieType.Steinberg.Isogeny.e7Isogeny k)
      (CFSG.LieType.CurtisTits.isQuasisimple_e7 (k := k))
      (CFSG.LieType.Steinberg.Isogeny.e7Isogeny_surjective k)
      (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
        (CFSG.LieType.CurtisTits.isQuasisimple_e7 (k := k))
        (CFSG.LieType.Steinberg.Isogeny.exists_e7Isogeny_ne_one k))
  obtain ⟨e₂⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_E7 q hv hq k hcard.symm
  exact Or.inl ⟨⟨.E7 q, hv⟩, hq, ⟨MulEquiv.trans e₁ e₂⟩⟩

theorem isCharTwoModel_e7 : IsCharTwoModel (e7Datum k) k (e7Data_valid.xm k) where
  conclusionB := e7_conclusionB k
  divisible := rfl
  isSymm := by
    change (Tag.cartan .E7).IsSymm
    rw [cartan_E7]
    exact CartanMatrix.E_isSymm 7
  steinberg := isCharTwoSteinberg_e7 k
  isQuasisimple := CFSG.LieType.CurtisTits.isQuasisimple_e7 (k := k)
  odd_card_center := odd_card_center_e7 k
  isChevTwo := isChevTwo_e7 k

theorem hasCharTwoModel_E7 : HasCharTwoModel k (CartanMatrix.E 7) :=
  ⟨_, _, e7Datum k, e7Data_valid.xm k, Equiv.refl _, fun i j => by
    change Tag.cartan .E7 i j = _
    rw [cartan_E7], isCharTwoModel_e7 k⟩

end E7Catalogue

end MinusculeModel

end CFSG.GroupTheory.GomiLeviExc
