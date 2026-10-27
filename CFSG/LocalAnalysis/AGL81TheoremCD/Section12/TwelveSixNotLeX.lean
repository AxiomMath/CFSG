module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNoExtraspecial
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixWX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixXStarPGroup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKCompCentral
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixCoprimeK
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourKerDecomp
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFixedPoints
import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem not_le_xSub_of_centralizer_le_of_pLayerIn_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {W : Subgroup G} (hW : Nat.card W = 3) (hp3 : p ≠ 3)
    (hL : pLayerIn p H ≤ M) (hCW : centralizer (W : Set G) ≤ M) :
    ¬ W ≤ xSub p M H := by
  intro hWX
  haveI : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  haveI : Fact (Nat.Prime 3) := Nat.fact_prime_three
  have hWp3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by simpa using hW)
  have hcop : Nat.Coprime p (Nat.card W) := by
    rw [hW]
    exact (Nat.coprime_primes hc.ctx.p_prime Nat.prime_three).mpr hp3
  have hWO : W ≤ relPPrimeCore p H := hc.ctx.le_relPPrimeCore_of_le_xSub hL hcop hWX
  obtain ⟨R, hR, hWR⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isSylowOf_ge_of_isPGroup
      (p := 3) hWO hWp3
  have hRM : R ≤ M := hR.le.trans (relPPrimeCore_le_M_of_twelveCtx hc.ctx)
  have hR3 : IsPGroup 3 R := hR.isPGroup
  refine not_kSub_le_M_of_nineNineOne hc.ctx hc.hI ?_
  exact kSub_le_M_of_nineTwelveKer hc.ctx hc.h912 hL hR hWR hCW
    (fun h => hc.not_extraspecial hRM hR3 ⟨h.2.1, h.2.2.1, h.2.2.2⟩)

private theorem not_le_xSub_of_centralizer_le_of_not_pLayerIn_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃) {W : Subgroup G} (hW : Nat.card W = 3)
    (hp3 : p ≠ 3) (hL : ¬ pLayerIn p H ≤ M) (hCW : centralizer (W : Set G) ≤ M) :
    ¬ W ≤ xSub p M H := by
  intro hWX
  haveI : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hWp3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by simpa using hW)
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := hc.ctx.exists_E_sq
  rcases (hc.h910 E hEQ hE hEc hΓ).1 hL with ⟨-, -, hKnorm⟩ | ⟨hp3', -⟩
  · have hKH : ((kSub p M H).subgroupOf H).Normal := hKnorm
    have hcomm := commutator_le_relPPrimeCore_kSub_of_le_xSub hc.ctx hKH hWX
    obtain ⟨hperf, hNK⟩ := hc.ctx.kSub_perfect_and_commutator_le hc.h912 hL hp3
    have hWH : W ≤ H := hWX.trans (xSub_le_H p M H)
    have hWK : W ≤ normalizer (kSub p M H : Set G) :=
      hWH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le p M H)).mp hKH)
    have hNK' : relPPrimeCore p (kSub p M H) ≤ kSub p M H :=
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_le
        (kSub p M H)
    have hdecomp := eq_inf_centralizer_sup_pCoreOf_two hWK hWp3 hNK' hperf hcomm hNK
    have hO2M : pCoreOf 2 (kSub p M H) ≤ M := by
      have hle : pCoreOf 2 (kSub p M H) ≤ pCoreOf 2 H :=
        CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (kSub_le p M H)
          ((Subgroup.normal_subgroupOf_iff_le_normalizer (kSub_le p M H)).mp hKH)
      refine hle.trans ?_
      rw [hc.ctx.pCore_two_inter]
      exact (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (H ⊓ M)).trans inf_le_right
    have hKleM : kSub p M H ≤ M := by
      rw [hdecomp]
      exact sup_le (inf_le_right.trans hCW) hO2M
    exact not_kSub_le_M_of_nineNineOne hc.ctx hc.hI hKleM
  · exact absurd hp3' hp3

theorem TwelveSixKCtx.not_le_xSub_of_centralizer_le
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {W : Subgroup G} (hW : Nat.card W = 3) (hCW : centralizer (W : Set G) ≤ M) :
    ¬ W ≤ xSub p M H := by
  by_cases hp3 : p = 3
  · subst hp3
    have hWp3 : IsPGroup 3 W := IsPGroup.of_card (n := 1) (by simpa using hW)
    exact not_le_xSub_of_isPGroup hc.ctx hc.hI hWp3 hCW
  · by_cases hL : pLayerIn p H ≤ M
    · exact not_le_xSub_of_centralizer_le_of_pLayerIn_le hc hW hp3 hL hCW
    · exact not_le_xSub_of_centralizer_le_of_not_pLayerIn_le hc hW hp3 hL hCW

theorem TwelveSixKCtx.not_le_xSub (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    {L W : Subgroup G} (hL : L ∈ weakBlockSet M H)
    (hW : Nat.card W = 3) (hWL : W ≤ L) : ¬ W ≤ xSub p M H :=
  hc.not_le_xSub_of_centralizer_le hW (hc.hC L W hL hW hWL)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
