module

public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.SporRestrictedLocal
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.HNOddCore.OuterFix
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpLeaf

public section

namespace CFSG.ComponentClassification.EvenPump

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.SolMax (card_of_mulEquiv_alt dvd_card_of_alt
  exact_component_of_oddCore fixedSubgroup_conj_eq eq_of_factorial_div_two_eq)

@[expose] def EvenAltOnlyTen (N : ℕ) (Y : Type) [Group Y] : Prop :=
  ∀ m : ℕ, Even m → 10 ≤ m → m.factorial / 2 ≤ N → Nonempty (Y ≃* alternatingGroup (Fin m)) →
    m = 10

theorem isoInvariant_evenAltOnlyTen (N : ℕ) : IsoInvariant (EvenAltOnlyTen N) := by
  intro Y Y' _ _ e h m hm hm10 hmN ⟨f⟩
  exact h m hm hm10 hmN ⟨e.symm.trans f⟩

theorem evenAltOnlyTen_of_card_quotient_center {N : ℕ} {Y : Type} [Group Y]
    (h : Nat.card (Y ⧸ center Y) = 1814400) : EvenAltOnlyTen N Y := by
  intro m _ hm10 _ ⟨f⟩
  have hZ : center Y = ⊥ := by
    have h1 := Subgroup.map_center_eq f
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; omega)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).mp h1
  rw [hZ, Nat.card_congr (QuotientGroup.quotientBot : Y ⧸ (⊥ : Subgroup Y) ≃* Y).toEquiv,
    card_of_mulEquiv_alt (by omega) f] at h
  exact eq_of_factorial_div_two_eq (by omega) (by norm_num) (h.trans (by decide))

theorem eq_ten_of_HN
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (e : S ≃* NativeSporadic.Carrier .HN) {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) (hex : Open.fusionZStar ↥P = pPrimeCore 2 ↥P) {m : ℕ}
    (hm : Even m) (hm10 : 10 ≤ m) (eP : ↥P ⧸ Open.fusionZStar ↥P ≃* alternatingGroup (Fin m)) :
    m = 10 := by
  have hσ1 := h.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hmN : m.factorial / 2 ≤ Nat.card S := Nat.le_of_dvd Nat.card_pos
    ((dvd_card_of_alt (by omega) eP).1.trans (Subgroup.card_subgroup_dvd_card P))
  have hcore : CFSG.oddCore (fixedSubgroup σ) = ⊥ :=
    oddCore_fixedSubgroup_eq_bot_of_mulAut hna
      (mulAut_oddCore_eq_bot_of_sporadicOddCoreFree Sporadic.HNOddCore.sporadicOddCoreFree_HN
        hna e) hσ2
  obtain ⟨hcomp, ⟨eL⟩⟩ := exact_component_of_oddCore h hcore hex
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  rcases exists_conj_or_not_mem_range σ with ⟨t, ht⟩ | hout
  ·
    exfalso
    obtain ⟨ht2, -, -, -⟩ := h.inner hna ht
    have hfix : fixedSubgroup σ = centralizer ({t} : Set S) := by
      rw [ht]
      exact fixedSubgroup_conj_eq t
    let φ := MulEquiv.subgroupCongr hfix
    have hin : NoEvenAltBelow (Nat.card S) ↥(L.map φ.toMonoidHom) :=
      noEvenAltBelow_of_card_quotient_center_eq (c := 44352000)
        (factorial_div_two_ne_even 12 (by decide) (by decide))
        (RestrictedStd.Spor.hnLocalComponentsInput_holds S e t ht2 _
          (isComponent_map_mulEquiv φ hcomp))
    exact (hin m hm hm10 hmN).false
      ((L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP))
  ·
    have hfix : Sporadic.Schreier.fixSub σ = fixedSubgroup σ := by
      ext x
      exact Iff.rfl
    let φ := MulEquiv.subgroupCongr hfix.symm
    obtain ⟨θ⟩ := Sporadic.HNOddCore.hn_outer_involution_fixSub e σ hσ2 hout
    have hcs : CompsSatisfy (Sporadic.Schreier.fixSub σ) (EvenAltOnlyTen (Nat.card S)) :=
      RestrictedStd.Spor.CompsSatisfy.of_mulEquiv (isoInvariant_evenAltOnlyTen _) θ
        (RestrictedStd.Spor.compsSatisfy_perm_ten.mono fun Y _ hY =>
          evenAltOnlyTen_of_card_quotient_center (Set.mem_singleton_iff.1 hY))
    exact hcs _ (isComponent_map_mulEquiv φ hcomp) m hm hm10 hmN
      ⟨(L.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans (eL.trans eP)⟩

end CFSG.ComponentClassification.EvenPump
