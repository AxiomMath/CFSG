module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYBender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYAlt
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXComponents

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem card_quasiQuotient_le (u : J) : Nat.card (QuasiQuotient u) ≤ Nat.card J :=
  (Nat.le_of_dvd Nat.card_pos (Subgroup.card_quotient_dvd_card _)).trans
    (Subgroup.card_le_card_group _)

theorem canonicalBelow_quasiQuotient (IH : CanonicalBelow (Nat.card J)) (u : J) :
    CanonicalBelow (Nat.card (QuasiQuotient u)) :=
  fun K _ _ hK => IH K (lt_of_lt_of_le hK (card_quasiQuotient_le u))

theorem BadLift.center_card_and_cover
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J))
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) {L : Subgroup (QuasiQuotient u)}
    (hL : OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L) :
    Nat.card (Subgroup.center L) = 2 ∧ quasiBar u ∉ L ∧
      (Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Theory.Comparator.PSL2Model 2) ∨
        Nonempty (L ⧸ Subgroup.center L ≃* ↥(CFSG.Theory.Comparator.SzModel 1))) :=
  hL.center_card_and_cover (hu.baseConfig h hz hrank) (quasiBar_mul_self u)
    (zpowers_quasiBar_normal u) (canonicalBelow_quasiQuotient IH u)

theorem BadLift.exists_alternating_component
    (hu : BadLift B z u) (h : Setting J Q B)
    (hz : FourGen Q z) (IH : CanonicalBelow (Nat.card J))
    (hrank : 3 ≤ CFSG.Open.pRank 2 (quasiNormalizer u)) :
    ∃ L : Subgroup (QuasiQuotient u),
      OneComponent (quasiImage B u) (quasiCentral u) (quasiBar u) L ∧
      Nat.card (Subgroup.center L) = 2 ∧ quasiBar u ∉ L ∧
      Nonempty (L ⧸ Subgroup.center L ≃* alternatingGroup (Fin 5)) ∧
      ∀ x : QuasiQuotient u, orderOf x = 2 →
        x ∈ L ⊔ Subgroup.centralizer (L : Set (QuasiQuotient u)) := by
  have hc := hu.baseConfig h hz hrank
  obtain ⟨L, hL⟩ := hu.exists_oneComponent h hz hrank
  obtain ⟨hZ, hvL, hcov⟩ := hu.center_card_and_cover h hz IH hrank hL
  rcases hcov with hL2 | hS
  · obtain ⟨e₅⟩ :=
      CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
    let eA := hL2.some.trans e₅
    exact ⟨L, hL, hZ, hvL, ⟨eA⟩, fun x hx => hL.mem_sup_centralizer_of_alternating hc
      (quasiBar_mul_self u) (zpowers_quasiBar_normal u) hZ eA hx⟩
  · exact (hu.false_of_szModel h hz hrank hL hZ hS.some).elim

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
