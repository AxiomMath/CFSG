module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CountFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FixedFive
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.ShapeCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

theorem gzClass_centQ_card (hI : TwoHSInterface) (hC : CSideFacts) {G : Type} [Group G]
    [Finite G] {a z : G} (h : IsF5Type a z) (hF1 : Vert Fusion1Facts a z)
    (hF2 : Vert Fusion2Facts a z) (hF3 : Vert Fusion3Facts a z) (hOrb : Vert GzOrbitFacts a z)
    (x : ↥(Gx z)) (hx : (barOf z x) ^ 2 = 1) (hcard : Nat.card ↥(CbarCent z x) = 240) :
    Nat.card (centQtilde z (x : G)) = 2 ^ 5 ∧
      ((x : G) ^ 2 = 1 → Nat.card {q : G // q ∈ Qz z ∧ q * (x : G) = (x : G) * q} = 2 ^ 5) := by
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hIrr : CIrreducible ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    cIrreducible_pCore h hOrb.self
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have hcard240 :
      Nat.card ↥(Subgroup.centralizer ({barOf z x} : Set (Gbar z))) = 240 := hcard
  have hx1 : barOf z x ≠ 1 :=
    ne_one_of_card_centralizer_ne e (by rw [hcard240]; norm_num)
  have hxmem : barOf z x ∈ commutator (Gbar z) := by
    rcases involution_cases_of_mulEquiv e hx hx1 with h | h | h
    · exact absurd h.2 (by rw [hcard240]; norm_num)
    · exact h.1
    · exact absurd h.2 (by rw [hcard240]; norm_num)
  have hW : Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧
      ⁅q, x⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))} = 2 ^ 5 :=
    hC.centQ_inv_base ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hQ hIrr x hx hx1 hxmem
  refine ⟨(card_centQtilde_eq h x).trans hW, ?_⟩
  intro hx2G
  have hx2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2G
  obtain ⟨ρ, hρ5, hρx⟩ :=
    exists_orderOf_five_commute (CFSG.pCore 2 ↥(Gx z)) hQ.plus hx2 hcard240 hW
  have hρbar5 : orderOf (barOf z ρ) = 5 := orderOf_barOf_five hρ5
  have hρbarcomm : barOf z ρ * barOf z x = barOf z x * barOf z ρ := by
    have h := congrArg (barOf z) hρx
    simpa [barOf, QuotientGroup.mk_mul] using h
  have hρbar : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 300 :=
    card_centralizer_five_of_mulEquiv e hxmem hx hcard240 hρbar5 hρbarcomm
  have hρQ : CFSG.pCore 2 ↥(Gx z) ⊓ Subgroup.centralizer ({ρ} : Set ↥(Gx z)) =
      centerOf (CFSG.pCore 2 ↥(Gx z)) := by
    rcases (hC.five_local_shapes ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hQ hIrr).1 ρ hρ5 with
      h | h | h
    · exact h.2
    · exfalso
      have h25 : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 25 :=
        card_of_isShapeZpTimesZp_five h
      have hcontra : (25 : ℕ) = 300 := h25.symm.trans hρbar
      norm_num at hcontra
    · exfalso
      have h50 : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 50 :=
        card_of_isShapeZpWrTwo_five h
      have hcontra : (50 : ℕ) = 300 := h50.symm.trans hρbar
      norm_num at hcontra
  have hζ : centerOf (CFSG.pCore 2 ↥(Gx z)) = Subgroup.zpowers (GxSelf z) :=
    centerOf_eq_zpowers h.orderOf_z hQ
  have hζc : ∀ g : ↥(Gx z), g * GxSelf z = GxSelf z * g := by
    intro g
    apply Subtype.ext
    simpa [GxSelf] using (mem_Gx.mp g.2).symm
  have hcomm : Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧ q * x = x * q} = 2 ^ 5 :=
    card_commute_eq_of_fixed_five (CFSG.pCore 2 ↥(Gx z)) hQ.plus hζ hζc hρ5 hρx hρQ hW
  exact (card_commute_Qz_eq x).trans hcomm

end CFSG.EvenSporadicStandard.HNRecog.Section3
