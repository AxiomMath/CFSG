module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267RankAut
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFactsCore
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Yardstones.Md0ec50421ce4.Definitions

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

@[expose] noncomputable def psimpleEquivCenterQuotOfCore {p : ℕ} (hcore : GLAPPrimeCore p ↥S = ⊥) :
    PSimple p S ≃* ↥S ⧸ Subgroup.center ↥S :=
  QuotientGroup.congr _ _
    ((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot)
    (Subgroup.map_center_eq _)

theorem center_eq_bot_of_multiplier {p : ℕ} (hp : p.Prime) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) {T : Type} [Group T] (e : PSimple p S ≃* T)
    (hM : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier T)) : Subgroup.center ↥S = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hperf' : Group.IsPerfect ↥S :=
    ⟨CFSG.LocalAnalysis.GLTheoremA.S267.perfect_of_commutator_self_eq hperf⟩
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf'
    ((psimpleEquivCenterQuotOfCore hcore).symm.trans e)
  have hpg :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      hp hcore
  by_contra hne
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hpg
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  exact hM ((dvd_pow_self p hk0).trans (hk ▸ hdvd))

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
