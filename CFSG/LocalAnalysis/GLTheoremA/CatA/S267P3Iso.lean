module

public import CFSG.Open.GriessSchurMultipliersMilestoneDefs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM5Lemmas
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Base

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

variable {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

@[expose] noncomputable def pquotEquiv (H : P3Hyp q S B) : PQuot 3 S ≃* ↥S :=
  (QuotientGroup.quotientMulEquivOfEq H.core).trans QuotientGroup.quotientBot

@[expose] noncomputable def psimpleEquivCenterQuot (H : P3Hyp q S B) :
    PSimple 3 S ≃* ↥S ⧸ Subgroup.center ↥S :=
  QuotientGroup.congr _ _ (pquotEquiv H) (Subgroup.map_center_eq (pquotEquiv H))

@[expose] noncomputable def psimpleEquiv (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥) :
    PSimple 3 S ≃* ↥S :=
  (psimpleEquivCenterQuot H).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)

theorem P3Hyp.center_eq_bot_of_multiplier (H : P3Hyp q S B) {T : Type} [Group T]
    (e : PSimple 3 S ≃* T) (hM : ¬ 3 ∣ Nat.card (CFSG.Open.griessHopfMultiplier T)) :
    Subgroup.center ↥S = ⊥ := by
  have hperf : Group.IsPerfect ↥S := ⟨S267.perfect_of_commutator_self_eq H.perfect⟩
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hperf
    ((psimpleEquivCenterQuot H).symm.trans e)
  have hp := CFSG.LocalAnalysis.GLTheoremA.SFM5.isPGroup_center_of_glaPPrimeCore_eq_bot H.core
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hp
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  exact hM ((dvd_pow_self 3 hk0).trans (hk ▸ hdvd))

theorem exists_embedding_of_mulEquiv (H : P3Hyp q S B) (hZ : Subgroup.center ↥S = ⊥)
    {X : Type} [Group X] (e : X ≃* PSimple 3 S) :
    ∃ φ : X →* Ω, Function.Injective φ ∧ φ.range = S := by
  refine ⟨S.subtype.comp (e.trans (psimpleEquiv H hZ)).toMonoidHom,
    S.subtype_injective.comp (e.trans (psimpleEquiv H hZ)).injective, ?_⟩
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (e.trans (psimpleEquiv H hZ)).surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
