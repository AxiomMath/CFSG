module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H113
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H611K
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8TableU43
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8TableWreath
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E614
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8E615
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8EA16L
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CQ2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13CDF
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13EV2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8L119Final

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option linter.unusedSectionVars false


theorem outerS84_false {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T E : Subgroup G} {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
    (h : OuterS8Hyp G L z t T E Q x B β S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨α, hα⟩ := h.alpha
  obtain ⟨σ, hσ⟩ := h.exists_sigma hα
  have hF := h.outerE.eFacts611 h.wFacts h.sporadic
  have hM := h.outerMFacts hα
  have hNT : OuterNoTable := outerNoTable_of_cases outerTableU43 outerTableWreath
  have hp := h.toOHyp69.outerPairing_of_noTable hα hF hM h.cardEβ h.lemma96 hNT
  let c : OI13Ctx L z t T E B β S α σ := ⟨h.toOHyp69, hα, hF, hM, hp, hσ⟩
  have hF613 := h.outerE.eFacts613 h.wFacts h.sporadic
  obtain ⟨π, hπ, -⟩ := hF613.exists_pi
  have hE614 := h.outerE.eFacts614 h.wFacts h.sporadic
  have hEQ := h.outerE.eFactsQ h.wFacts h.sporadic
  have hEA := (h.outerE.eFacts615 h.wFacts h.sporadic).ea_le
  have hT : Nat.card T ≤ 512 := h.cardT.le
  have hz2 : orderOf z = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact h.outerE.cfg.z_sq) h.outerE.cfg.z_ne
  have : IsSimpleGroup G := h.std.simple
  obtain ⟨Rs, hR, -⟩ := c.exists_isRs
  rcases c.rho_range_trichotomy hπ with hD | hA | hB
  ·
    have hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹ := fun q hq hq2 hqz =>
      hR.not_conj_z_of_mem_Qs_delta hπ hD hE614 hEQ.common_invol hT hq hq2 hqz
    have h119 : ∀ y : G, y ∈ c.Nc → y ∉ c.N1 → y * y = 1 → (∃ g : G, g * z * g⁻¹ = y) →
        ∃ g ∈ c.Nc, g * z * g⁻¹ = y := fun y hy hyN hy2 hex =>
      OI13Ctx.lemma119_gen h c hZQ hEA hπ hy hyN hy2 hex
    have hrank : ORankStatement z :=
      orank h.outerE.cfg h.cyclicC (elAb16_mulAut_of_isSporadic h.sporadic)
    exact c.caseDelta_false' h.std.nonabelian hπ hD hEA hR hZQ
      (fun y hy hy2 hyQ hev hyz =>
        hR.not_conj_z_of_even hπ (fun a b hab => (hD a b).1 hab) (c.oe64 hF613) hrank hy hy2 hyQ
          hev hyz)
      h119
  ·
    have hbig := c.hbigA hA hE614
    have hZQ : ∀ q : G, q ∈ c.Qs → q * q = 1 → ¬ ∃ g : G, q = g * z * g⁻¹ := fun q hq hq2 hqz =>
      hR.not_conj_z_of_mem_R hbig hT ⟨hR.Qs_le hq, c.Qs_le_N1 hq⟩ hq2 hqz
    have h119 := OI13Ctx.lemma119_of h c hZQ hEA hπ
    obtain ⟨Rs, R, hRs, hRR, hidx, hzRs, hzR, hfus, hcent⟩ := c.caseA_total hπ hA hE614 hT h119
    exact false_of_fusion_pair h.std.nonabelian hz2 hRs hRR hidx hzRs hzR hfus hcent
  ·
    obtain ⟨Rs, R, hRs, hRR, hidx, hzRs, hzR, hfus, hcent⟩ := c.caseB_final hB hE614 hT
    exact false_of_fusion_pair h.std.nonabelian hz2 hRs hRR hidx hzRs hzR hfus hcent

theorem outerS84_holds : Fin76bOuterS8₄ :=
  fin76bOuterS8₄_of_hyp fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => outerS84_false h

end CFSG.EvenSporadicStandard.Fin76b
