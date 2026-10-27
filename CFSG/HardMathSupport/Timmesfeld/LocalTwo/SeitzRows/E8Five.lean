module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.E8Layer
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Centralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.Main
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.E8.N2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.NormalizerSmall
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.TauCetiBridge CFSG.LieType.SeitzGeneration
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem eleven_le_of_orderOf_eq_five {p n : ℕ} (hp : p.Prime)
    (hord : orderOf ((n : ℕ) : ZMod p) = 5) : 11 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq0 : ((n : ℕ) : ZMod p) ≠ 0 := by
    intro h
    rw [h, orderOf_eq_zero_iff'.2] at hord
    · exact absurd hord (by norm_num)
    · intro m hm h'
      rw [zero_pow hm.ne'] at h'
      exact zero_ne_one h'
  have hdvd : 5 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  obtain ⟨k, hk⟩ := hdvd
  have h2 := hp.two_le
  rcases k with _ | _ | k
  · omega
  · have : p = 6 := by omega
    subst this
    exact absurd hp (by norm_num)
  · omega

section Frame


theorem innerPlaneBalance_adjointE8_five_of_layer (K : Type) [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5)
    (hlayer : LayerDichotomy p (adjointGroup .E8 K)) :
    InnerPlaneBalance p (adjointGroup .E8 K) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL .E8 K) := finite_modGL
  obtain ⟨ℓ, f, hℓ, hchar, hf, hK⟩ := exists_charP_card K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hp11 : 11 ≤ p := eleven_le_of_orderOf_eq_five hp hord
  have hcard : (Nat.card (adjointGroup .E8 K)).factorization p =
      (Nat.card SL(5, K)).factorization p + (Nat.card SL(5, K)).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8,
      padicValNat_ordE8_of_orderOf_eq_five hp (by omega) hq2 hord,
      padicValNat_card_SL_of_orderOf_eq K hp (by norm_num)
        (by rw [← Nat.card_eq_fintype_card]; exact hord), Nat.card_eq_fintype_card]
    ring
  have hAG : ∀ x, ψA x ∈ adjointGroup .E8 K := fun x => by
    have h : ψA x ∈ ψA.range ⊔ ψB.range := Subgroup.mem_sup_left ⟨x, rfl⟩
    rw [hrange] at h
    exact rootSpan_le_adjointGroup K _ h
  have hBG : ∀ x, ψB x ∈ adjointGroup .E8 K := fun x => by
    have h : ψB x ∈ ψA.range ⊔ ψB.range := Subgroup.mem_sup_right ⟨x, rfl⟩
    rw [hrange] at h
    exact rootSpan_le_adjointGroup K _ h
  let ψA' : SL(5, K) →* adjointGroup .E8 K := ψA.codRestrict (adjointGroup .E8 K) hAG
  let ψB' : SL(5, K) →* adjointGroup .E8 K := ψB.codRestrict (adjointGroup .E8 K) hBG
  have hA' : Function.Injective ψA' := fun x y h => hA (congrArg Subtype.val h)
  have hB' : Function.Injective ψB' := fun x y h => hB (congrArg Subtype.val h)
  have hcomm' : ∀ x y, Commute (ψA' x) (ψB' y) := fun x y => Subtype.ext (hcomm x y).eq
  have hAB : ¬ p ∣ Nat.card ↥(ψA'.range ⊓ ψB'.range) := by
    intro hdvd
    have hle : ψA'.range ⊓ ψB'.range ≤ (Subgroup.center SL(5, K)).map ψA' := by
      rintro z ⟨⟨c, rfl⟩, hcB⟩
      exact ⟨c, Subgroup.mem_center_iff.2 fun x =>
        (commute_of_frame_mem_range hA' hcomm' hcB x).eq, rfl⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective hA'] at h1
    have h2 := CFSG.HardMathSupport.Foote.Proving.natCard_center_SL_le (Fin 5) K
    have h3 : p ≤ Nat.card ↥(ψA'.range ⊓ ψB'.range) := Nat.le_of_dvd Nat.card_pos hdvd
    simp only [Fintype.card_fin] at h2
    omega
  have hXY : (ψA'.range ⊔ ψB'.range).map (adjointGroup .E8 K).subtype =
      rootSpan .E8 K (cosetRoots .E8 4 5) := by
    rw [Subgroup.map_sup, ← hrange]
    congr 1
    · rw [← MonoidHom.range_comp]
      rfl
    · rw [← MonoidHom.range_comp]
      rfl
  have hC : TwFrameClosing .E8 K (rootSpan .E8 K (cosetRoots .E8 4 5)) :=
    frameClosing_of_detection_E8 K (DetectE8.frameDetection_E8 K)
  have hN : TwFrameNormalizerSolvable .E8 K (rootSpan .E8 K (cosetRoots .E8 4 5)) := by
    rcases (show 4 ≤ Nat.card K ∨ Nat.card K = 3 ∨ Nat.card K = 2 by omega) with h4 | h3 | h2'
    · exact frameNormalizerSolvable_E8 K h4
    · exact frameNormalizerSolvable_E8_three K h3
    · exact DetectE8.frameNormalizerSolvable_E8_two K h2'
  have hperf : Group.IsPerfect SL(5, K) := (isQuasisimple_SL (K := K) (by norm_num)).1
  refine innerPlaneBalance_of_frames (mulAut_conj_injective_adjointGroup (τ := .E8) (K := K))
    ψA' ψB' hA' hB' hcomm' hperf hperf (closing_of_map hXY hC) (normalizerSolvable_of_map hXY hN)
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg)
    (fun g hg => isCyclic_centralizer_of_orderOf_eq K hp (by norm_num)
      (by rw [← Nat.card_eq_fintype_card]; exact hord) hg) hAB hcard ?_ hlayer
  intro F hFc hFp a b haF hbF ha1 hb1
  exact exists_offLine_nonsolvable_E8 K hf hK hp (by omega) hord F hFc hFp haF hbF ha1 hb1

theorem innerPlaneBalance_adjointE8_five (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5) :
    InnerPlaneBalance p (adjointGroup .E8 K) :=
  innerPlaneBalance_adjointE8_five_of_layer K hp hord
    (layerDichotomy_adjointE8_five K hp (by have := eleven_le_of_orderOf_eq_five hp hord; omega)
      hord)


theorem innerPlaneBalance_catE8_of_orderOf_five (q : TauCeti.PrimePower)
    (hv : (excIndex .E8 q).Valid) {p : ℕ} (hp : p.Prime)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 5) :
    InnerPlaneBalance p (CatT ⟨excIndex .E8 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e8 q hv
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 5 := by rw [hK]; exact he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointE8_five K hp hord)

theorem innerPlaneBalanceAt_E8_five : InnerPlaneBalanceAt .E8 5 :=
  fun q hv _ hp _ _ _ he => innerPlaneBalance_catE8_of_orderOf_five q hv hp he

end Frame

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
