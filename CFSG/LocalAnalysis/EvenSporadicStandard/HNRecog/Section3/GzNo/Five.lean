module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CountFive
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.ShapeCard

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

theorem gzNo_five (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hOrb : GzOrbitFacts a z) (hCls : GzClassFacts a z) (x : ↥(Gx z))
    (hx2 : (x : G) ^ 2 = 1) (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) :
    Nat.card ↥(Qz z ⊓ Gx (x : G)) = 2 ^ 5 ∧
      ∃ ρ : ↥(Gx z), orderOf ρ = 5 ∧ ρ * x = x * ρ ∧
        (∀ q ∈ Qz z, q * (ρ : G) = (ρ : G) * q → q = 1 ∨ q = z) ∧
        IsShapeZpTimesA5 5 ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) := by
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hIrr : CIrreducible ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) :=
    cIrreducible_pCore h hOrb
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar (a := a) h
  have hx2' : x ^ 2 = (1 : ↥(Gx z)) := by
    apply Subtype.ext
    simpa using hx2
  have hbar2 : (barOf z x) ^ 2 = 1 := by
    simpa [QuotientGroup.mk_pow] using congrArg (barOf z) hx2'
  have hcard240 : Nat.card ↥(Subgroup.centralizer ({barOf z x} : Set (Gbar z))) = 240 :=
    card_of_isShapeTwoTwoTimesA5 hsh
  have hbar1 : barOf z x ≠ 1 :=
    ne_one_of_card_centralizer_ne e (by rw [hcard240]; norm_num)
  have hbar_mem : barOf z x ∈ commutator (Gbar z) := by
    rcases involution_cases_of_mulEquiv e hbar2 hbar1 with h1 | h2 | h3
    · exact absurd h1.2 (by rw [hcard240]; norm_num)
    · exact h2.1
    · exact absurd h3.2 (by rw [hcard240]; norm_num)
  have hW : Nat.card {q : ↥(Gx z) // q ∈ CFSG.pCore 2 ↥(Gx z) ∧
      ⁅q, x⁆ ∈ centerOf (CFSG.pCore 2 ↥(Gx z))} = 2 ^ 5 :=
    (card_centQtilde_eq h x).symm.trans (hCls.centQ_card x hbar2 hsh).1
  have hcard_sub : Nat.card ↥(Qz z ⊓ Gx (x : G)) =
      Nat.card {q : G // q ∈ Qz z ∧ q * (x : G) = (x : G) * q} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun q => ?_)
    rw [Subgroup.mem_inf, mem_Gx]
    exact and_congr_right fun _ => eq_comm
  refine ⟨hcard_sub.trans ((hCls.centQ_card x hbar2 hsh).2 hx2), ?_⟩
  obtain ⟨ρ, hρ5, hρx⟩ :=
    exists_orderOf_five_commute (CFSG.pCore 2 ↥(Gx z)) hQ.plus hx2' hcard240 hW
  have hρbar5 : orderOf (barOf z ρ) = 5 := orderOf_barOf_five hρ5
  have hρbarcomm : barOf z ρ * barOf z x = barOf z x * barOf z ρ := by
    have h := congrArg (barOf z) hρx
    simpa [barOf, QuotientGroup.mk_mul] using h
  have hρbar300 : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 300 :=
    card_centralizer_five_of_mulEquiv e hbar_mem hbar2 hcard240 hρbar5 hρbarcomm
  rcases (hC.five_local_shapes ↥(Gx z) (CFSG.pCore 2 ↥(Gx z)) hQ hIrr).1 ρ hρ5 with
    ⟨hρshape, hρQ⟩ | h2 | h3
  · refine ⟨ρ, hρ5, hρx, ?_, ?_⟩
    · intro q hq hcq
      obtain ⟨y, hyQ, hyeq⟩ := Subgroup.mem_map.mp hq
      have hycent : y ∈ Subgroup.centralizer ({ρ} : Set ↥(Gx z)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, show (y : G) = q from hyeq]
        exact hcq
      have hycenter : y ∈ centerOf (CFSG.pCore 2 ↥(Gx z)) := by
        rw [← hρQ]
        exact Subgroup.mem_inf.mpr ⟨hyQ, hycent⟩
      have hyzp : y ∈ Subgroup.zpowers (GxSelf z) := by
        rwa [centerOf_eq_zpowers h.orderOf_z hQ] at hycenter
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyzp
      have hqzk : q = z ^ k := by
        rw [← hyeq, ← hk]
        simp [Subgroup.coe_zpow, GxSelf]
      have hord : (orderOf z : ℤ) = 2 := by rw [h.orderOf_z]; norm_num
      rw [hqzk, ← zpow_mod_orderOf z k, hord]
      rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
      · left; rw [hk0]; simp
      · right; rw [hk1]; simp
    · simpa only [barOf] using hρshape
  · exfalso
    have h25 : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 25 :=
      card_of_isShapeZpTimesZp_five h2
    have hcontra : (25 : ℕ) = 300 := h25.symm.trans hρbar300
    norm_num at hcontra
  · exfalso
    have h50 : Nat.card ↥(Subgroup.centralizer ({barOf z ρ} : Set (Gbar z))) = 50 :=
      card_of_isShapeZpWrTwo_five h3
    have hcontra : (50 : ℕ) = 300 := h50.symm.trans hρbar300
    norm_num at hcontra

end CFSG.EvenSporadicStandard.HNRecog.Section3
