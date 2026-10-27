module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThreeFourHolds
public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6EnnolaSplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6RootKillWeyl
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwKillsRoot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option linter.unusedSectionVars false


theorem exists_two_commute_twE6Two {K₀ K : Type} [Field K₀] [Finite K₀] [Field K] [Finite K]
    (ι : K₀ →+* K) {σ₀ : K₀ ≃+* K₀} {σ : K ≃+* K} (hK₀ : Nat.card K₀ = (2 ^ 1) ^ 2)
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hσ₀ : ∀ c, σ₀ c = c ^ 2 ^ 1) (hσ : ∀ c, σ c = c ^ 2 ^ 3)
    {X₀ : Subgroup (ModGL TwistTag.E6.tag K₀)} (hX₀I : X₀ ≤ twistedE6InndiagGL K₀ σ₀)
    (hX₀ : IsElemAbelian 3 X₀) (hX₀c : Nat.card X₀ = 3 ^ 4)
    (hXI : X₀.map (baseChangeGL ι) ≤ twistedE6InndiagGL K σ)
    (hU : CFSG.StandardType.TwE6RootKill.TwNormTwo K σ (X₀.map (baseChangeGL ι))) :
    ∃ u₀ : ModGL TwistTag.E6.tag K₀, u₀ ∈ twistedE6RootGroup K₀ σ₀ ∧ u₀ ≠ 1 ∧
      (∃ n : ℕ, u₀ ^ 2 ^ n = 1) ∧ ∀ x ∈ X₀, Commute u₀ x := by
  haveI : CharP K₀ 2 := CFSG.StandardType.TwE6FieldCore.charP_two_of_card_sq hK₀
  haveI : CharP K 2 := CFSG.StandardType.TwE6FieldCore.charP_two_of_card_sq hK
  have h2₀ : ringChar K₀ = 2 := ringChar.eq K₀ 2
  have h2 : ringChar K = 2 := ringChar.eq K 2
  obtain ⟨D₀, hD₀⟩ := CFSG.StandardType.TwE6FieldCore.subfieldLangDatumThreeFour_holds K₀ K ι σ₀ σ
    (2 ^ 1) hK₀ (hK.trans (by norm_num)) hσ₀ (fun c => (hσ c).trans (by norm_num)) h2₀
    (by norm_num) X₀ hX₀I hX₀ hX₀c hU
  obtain ⟨D, -, hkill⟩ := CFSG.StandardType.TwE6FieldCore.exists_lift_twLangData ι σ (m := 1)
    (p := 3) le_rfl (by decide) (hK.trans (by norm_num)) (fun c => (hσ c).trans (by norm_num)) D₀
    hD₀ hXI
  have hcard : 3 ^ (if 3 = 3 then 4 else 5) ≤ Nat.card (X₀.map (baseChangeGL ι)) := by
    rw [if_pos rfl, Subgroup.card_map_of_injective (baseChangeGL_injective ι), hX₀c]
  obtain ⟨α, hα, hαD⟩ := StandardType.TwE6RootKill.rootKill_of_ennolaKill_weylKill
      (StandardType.TwE6RootKill.ennolaKill_of_steps StandardType.TwE6RootKill.leviSplitStep_holds
          StandardType.TwE6RootKill.ennolaSplitStep_holds) StandardType.TwE6RootKill.weylKill_holds K σ (2 ^ (1 * 3))
    (hK.trans (by norm_num)) (fun c => (hσ c).trans (by norm_num)) h2 3 Nat.prime_three
    (by norm_num) _ hXI (hX₀.map _) hcard hU D
  obtain ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.twE6KillRoot_proof K₀ σ₀ (2 ^ 1)
      (by rw [h2₀]; norm_num) hσ₀ hK₀ X₀ D₀ α hα (hkill α hαD)
  rw [h2₀] at hn
  exact ⟨u, hu, hu1, ⟨n, hn⟩, hcomm⟩

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
