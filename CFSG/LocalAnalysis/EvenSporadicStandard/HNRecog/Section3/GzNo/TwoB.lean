module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.CSideFacts
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.A5Transfer
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberCount
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.FiberLe
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.CBridgeB
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GzClass.ShapeCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

theorem gzNo_twoB (hC : CSideFacts) {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hF3 : Vert Fusion3Facts a z) (hOrb : GzOrbitFacts a z)
    (hCls : GzClassFacts a z) (x : ↥(Gx z)) (hx2 : (x : G) ^ 2 = 1)
    (hsh : IsShapeTwoTwoTimesA5 ↥(CbarCent z x)) : IsConj z (x : G) ∧ (x : G) ∉ Qz z := by
  classical
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  have hQ : IsExtraspecialPlusByA5WrTwoWith ↥(Gx z) Q :=
    isExtraspecialPlusByA5WrTwoWith_pCore h.cent_z
  have hIrr : CIrreducible ↥(Gx z) Q := cIrreducible_pCore h hOrb
  obtain ⟨e⟩ := nonempty_mulEquiv_Gbar h
  have hx'2 : x ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hx2
  have hxbar2 : (barOf z x) ^ 2 = 1 := by
    change (QuotientGroup.mk x) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, hx'2, QuotientGroup.mk_one]
  have hcentBar : Nat.card ↥(Subgroup.centralizer ({barOf z x} : Set (Gbar z))) = 240 :=
    card_of_isShapeTwoTwoTimesA5 hsh
  have hxbar1 : barOf z x ≠ 1 := by
    refine ne_one_of_card_centralizer_ne e (u := barOf z x) ?_
    rw [hcentBar]
    norm_num
  have hxQ : (x : G) ∉ Qz z := fun hq => hxbar1 ((barOf_eq_one_iff x).mpr hq)
  have hx1 : x ≠ 1 := by
    intro h1
    have hxG : (x : G) = 1 := by rw [h1]; rfl
    exact hxQ (hxG ▸ (Qz z).one_mem)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxord : orderOf (x : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx'2 hx1
  rcases hCls.inv_two (x : G) hxord with hAx | hzx
  · exfalso
    have hQcard : Nat.card ↥Q = 512 := by
      rw [hQ.plus.2.1]
      norm_num
    have hcentK : Nat.card ↥(Subgroup.centralizer ({x} : Set ↥(Gx z))) = 3840 := by
      have h1 : Nat.card ↥(Subgroup.centralizer ({x} : Set ↥(Gx z))) = 2 ^ 8 * 15 := by
        rw [show Nat.card ↥(Subgroup.centralizer ({x} : Set ↥(Gx z))) =
            Nat.card ↥(Gx z ⊓ Gx (x : G)) from
          (card_Gx_inf_eq (z := z) (c := (x : G)) x.2).symm]
        exact hOrb.orbit_outA.2 (x : G) ⟨x.2, hxQ, hAx⟩
      rw [h1]
      norm_num
    have hfiber := card_fiber_mul_card_centralizer Q x
    have hcentBarQ : Nat.card ↥(Subgroup.centralizer
        ({(x : ↥(Gx z) ⧸ Q)} : Set (↥(Gx z) ⧸ Q))) = 240 := hcentBar
    have hFiberEq :
        Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * x * k⁻¹ = s) ∧
          (s : ↥(Gx z) ⧸ Q) = (x : ↥(Gx z) ⧸ Q)} * 3840 =
          512 * 240 := by
      rw [hQcard, hcentK, hcentBarQ] at hfiber
      exact hfiber
    have hζ : GxSelf z ∈ centerOf Q := by
      rw [centerOf_eq_zpowers h.orderOf_z hQ]
      exact Subgroup.mem_zpowers (GxSelf z)
    have hne : ∀ k : ↥(Gx z), k * x * k⁻¹ ≠ x * GxSelf z := by
      intro k hk
      have hkG : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) * z := by
        have h := congrArg (fun t : ↥(Gx z) => (t : G)) hk
        simpa [GxSelf] using h
      have hconj : IsConj (x : G) ((x : G) * z) := isConj_iff.mpr ⟨(k : G), hkG⟩
      have hf3 : Fusion3Facts (x : G) z := hF3 (x : G) z hAx (IsConj.refl z)
      exact hxQ (hf3.shape_2AB z ⟨IsConj.refl z, hconj⟩).2
    have hlt := card_fiber_lt Q hQ.plus hx'2 hζ hne
    rcases involution_cases_of_mulEquiv e hxbar2 hxbar1 with
      ⟨_, hcard120⟩ | ⟨hin, hcard240⟩ | ⟨_, hcard32⟩
    · rw [hcard120] at hcentBar
      norm_num at hcentBar
    · have hF32 :
          Nat.card {s : ↥(Gx z) // (∃ k : ↥(Gx z), k * x * k⁻¹ = s) ∧
            (s : ↥(Gx z) ⧸ Q) = (x : ↥(Gx z) ⧸ Q)} = 32 := by
        omega
      have hcentQ :
          Nat.card {q : ↥(Gx z) // q ∈ Q ∧ ⁅q, x⁆ ∈ centerOf Q} = 32 := by
        have h := hC.centQ_inv_base ↥(Gx z) Q hQ hIrr x hxbar2 hxbar1 hin
        norm_num at h
        exact h
      rw [hF32] at hlt
      rw [hcentQ] at hlt
      omega
    · rw [hcard32] at hcentBar
      norm_num at hcentBar
  · exact ⟨hzx, hxQ⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
