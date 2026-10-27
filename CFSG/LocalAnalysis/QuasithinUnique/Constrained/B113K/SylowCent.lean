module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113K.SylowAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge

private theorem bk5_alt_case
    {Ω : Type} [Group Ω] [Finite Ω] {L : Subgroup Ω} {m : ℕ}
    (hq : CFSG.IsQuasisimple ↥L) (e : ↥L ≃* alternatingGroup (Fin m)) :
    SylowAutTrivial (↥L ⧸ Subgroup.center ↥L) := by
  have hm5 : 5 ≤ m := by
    by_contra hlt
    have hsol : Group.IsSolvable ↥(alternatingGroup (Fin m)) := by
      refine alternatingGroup.isSolvable ?_
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      omega
    have hsolL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hntq : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.1.toNontrivial
    have hntL : Nontrivial ↥L :=
      (QuotientGroup.mk_surjective :
        Function.Surjective (QuotientGroup.mk : ↥L → ↥L ⧸ Subgroup.center ↥L)).nontrivial
    have hc := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L
    rw [hq.1.commutator_eq_top] at hc
    exact lt_irrefl _ hc
  have hsimple : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5)
  have hL : IsSimpleGroup ↥L := e.isSimpleGroup
  have hZ : Subgroup.center ↥L = ⊥ := by
    rcases hL.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exact h
    · exfalso
      have hsub : Subsingleton (↥L ⧸ Subgroup.center ↥L) := by
        rw [h]
        exact QuotientGroup.subsingleton_quotient_top
      have hntq : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.1.toNontrivial
      exact not_subsingleton (↥L ⧸ Subgroup.center ↥L) hsub
  have e' : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
  by_cases hm7 : 7 ≤ m
  · exact SylowAutTrivial.of_mulEquiv e' (sylowAutTrivial_alt_ge_seven hm7)
  · rcases (show m = 5 ∨ m = 6 by omega) with rfl | rfl
    · exact sylowAutTrivial_alt (Or.inl rfl) e'
    · exact sylowAutTrivial_alt (Or.inr (Or.inl rfl)) e'

private theorem bk5_sylowAutTrivial_quot
    {Ω : Type} [Group Ω]
    [Finite Ω] {L : Subgroup Ω} (hq : CFSG.IsQuasisimple ↥L) (hLA : IsLieAltType ↥L)
    (hAut : AsLieTwoSylowAut) : SylowAutTrivial (↥L ⧸ Subgroup.center ↥L) := by
  rcases hLA with h2 | ⟨m, ⟨e⟩⟩ | hHat
  · exact hAut (↥L ⧸ Subgroup.center ↥L) h2.1.2.1 h2.2
  · exact bk5_alt_case hq e
  · obtain ⟨-, -, ⟨e6⟩⟩ := hHat
    exact sylowAutTrivial_alt (Or.inr (Or.inl rfl)) e6

theorem asLieAltSylowCentralizer_of
    (hAut : AsLieTwoSylowAut) : AsLieAltSylowCentralizer := by
  unfold AsLieAltSylowCentralizer
  intro Ω _ _ L T hq hLA hT x hxN hxT hxo
  exact CFSG.QuasithinUnique.Bridge.centralizes_of_sylowAutTrivial hq hT
    (bk5_sylowAutTrivial_quot hq hLA hAut) hxN hxT hxo

end CFSG.Quasithin
