module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop51Proof
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma511Ns CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns CFSG.RankThree.PartTwo.Sec4

theorem exists_center_ne_one_of_isSLThreeEps {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y)
    (h : IsSLThreeEps Y) : ∃ z ∈ Subgroup.center Y, z ≠ 1 := by
  have hAny : IsSLThreeEpsAny Y := by
    rcases h with ⟨K, hKf, hF, hc, he⟩ | ⟨K, hKf, hF, q, hcard, hq3, hq8, ⟨e⟩⟩
    · exact Or.inl ⟨K, hKf, hF, hc, he⟩
    · obtain ⟨p, f, rfl, ⟨hF'⟩⟩ := exists_unitaryFieldData hcard
      have h2 : 2 < p ^ f := by
        by_contra hle
        have hs : Group.IsSolvable ↥(CFSG.Open.StatedSU 3 (p ^ f) K) :=
          (isSolvable_slPi_false_two
            (show PiField false p f K from
              ⟨hF'.prime, hF'.one_le, by rw [piCard, Bool.cond_false]; exact hcard⟩)
            (pow_eq_two_of_not_two_lt hF' hle)).1
        exact false_of_quasisimple_of_solvable hq
          (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
      exact Or.inr ⟨K, hKf, hF, p ^ f, hcard, hq3, by omega, ⟨e⟩⟩
  have h3 := card_center_of_isSLThreeEpsAny hAny
  by_contra hno
  push Not at hno
  have : Subgroup.center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact Subgroup.mem_bot.2 (hno z hz)
  rw [this, Subgroup.card_bot] at h3
  omega

theorem gapKxType_of_lemma510 (h510 : Lemma510) : Gap_KxType := by
  intro G _ _ m hS hC B hB b hb hb1 L hL hty A F hA hbA hAfld hFe hF9 hFJ x hxB hxFA hx1 hxfld
  have hBe : IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hb
  have hx3 : x ^ 3 = 1 := hBe.2 x hxB
  obtain ⟨-, -, hiv⟩ := h510 G m hS hC B hB b hb hb1 L hL
  obtain ⟨hK, hbK, -⟩ := hiv x hxB hx1 hxfld
  obtain ⟨hxN, hfld⟩ := hxfld
  intro hSL
  obtain ⟨S, hS', hZ⟩ := exists_centreless_comp hS hb3 hx3 hb1 hL.1 hty hxN hfld hK hbK
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 (pumpUp L x)) :=
    isQuasisimple_quotient_of_glaPComponent hK
  obtain ⟨z, hzc, hz1⟩ := exists_center_ne_one_of_isSLThreeEps hYq hSL
  have hfd := fixData_of_type hYq (Or.inr hSL) (barAut_pow_three hbK.1 hb3) hbK.2
  obtain ⟨S0, comp, -, -, -, hO, hcen, hZS⟩ := layer_of_fixData hfd
  have hSS : S = S0 := (comp S).1 hS'
  subst hSS
  have hzS : z ∈ S := hZS hzc
  have hzcen : (⟨z, hzS⟩ : ↥S) ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hzc) w)
  have hZS' : Subgroup.center ↥S = ⊥ :=
    center_eq_bot_of_mulEquiv' (barEquivOfCore hO) hZ
  rw [hZS', Subgroup.mem_bot] at hzcen
  exact hz1 (congrArg Subtype.val hzcen)

@[expose] def InputCoverFixedCentre : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], CFSG.Open.IsQuasisimple Y → GLAPPrimeCore 3 Y = ⊥ →
    Subgroup.center Y ≠ ⊥ →
    ∀ α : MulAut Y, α ^ 3 = 1 → IsFieldAutThree α →
      ∀ S : Subgroup Y, GLAPComponent 3 (fixSub α) S → Subgroup.center (barOf 3 S) ≠ ⊥

theorem gap515CentreK_of_inputCoverFixedCentre (hR : InputCoverFixedCentre) : Gap515CentreK := by
  intro G _ _ m hS hC B hB b L A hw x hxA hx1 hxb
  have hw' := hw
  obtain ⟨hbB, hb1, hLcomp, -, hty, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, hiii⟩ := hw
  have hBe : IsElemAbelian 3 B := hB.1.1
  have hb3 : b ^ 3 = 1 := hBe.2 b hbB
  have hx3 : x ^ 3 = 1 := hA.2.1.2 x hxA
  obtain ⟨hK, hbK, -⟩ := hiii x (hA.1 hxA) hx1 (hfld x hxA)
  obtain ⟨hxN, hfldx⟩ := hfld x hxA
  rw [kOf_eq_pumpUp hw' hxA hxb]
  have hYq : CFSG.Open.IsQuasisimple (barOf 3 (pumpUp L x)) :=
    isQuasisimple_quotient_of_glaPComponent hK
  have hcentre : Subgroup.center (barOf 3 (pumpUp L x)) = ⊥ := by
    by_contra hne
    obtain ⟨S, hS', hZ⟩ := exists_centreless_comp hS hb3 hx3 hb1 hLcomp hty hxN hfldx hK hbK
    exact hR _ hYq (glaPPrimeCore_quotient_eq_bot Nat.prime_three) hne _
      (barAut_pow_three hbK.1 hb3) hbK.2 S hS' hZ
  have e := quotEquivBarX Nat.prime_three hK.1 hK.2.1
  exact center_eq_bot_of_mulEquiv' e.symm hcentre

end CFSG.HardMathSupport.Solomon.Coordinator
