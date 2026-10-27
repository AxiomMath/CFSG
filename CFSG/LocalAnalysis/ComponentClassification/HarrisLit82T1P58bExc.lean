module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bInner
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2Main
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBOddCentre
import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58bLift

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank Blueprint

namespace P58b

theorem exc_model_of_lieModel {G : Type} [Group G] {τ : StatedLieTag} {n p f : ℕ}
    (hτ : τ ∈ chevalleyExceptionalTags) (h : LieModel G τ n p f) :
    n = 0 ∧ ChevalleyExceptionalModel G τ p f :=
  (CFSG.Blueprint.LieModel.chevalleyExceptional_iff hτ).1 h

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem center_quotient_eq_bot (hX : IsQuasisimple X) : center (X ⧸ center X) = ⊥ :=
  LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hX

@[expose] def quotientCenterEquiv (hX : IsQuasisimple X) :
    (X ⧸ center X) ⧸ center (X ⧸ center X) ≃* X ⧸ center X :=
  (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_bot hX)).trans QuotientGroup.quotientBot

omit [Finite X] in
theorem odd_card_center_of_odd_multiplier (hX : IsQuasisimple X)
    (hodd : Odd (Nat.card (CFSG.Open.griessHopfMultiplier (X ⧸ center X)))) :
    Odd (Nat.card (center X)) := by
  have : Group.IsPerfect X := hX.1
  have hker : (QuotientGroup.mk' (center X)).ker ≤ center X := (QuotientGroup.ker_mk' _).le
  have hdvd := Subgroup.card_dvd_of_surjective
    (f := CFSG.RankThree.PerfectCover.hopfMultiplierToKer (QuotientGroup.mk' (center X))
      (QuotientGroup.mk'_surjective _) hker)
    (CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective _
      (QuotientGroup.mk'_surjective _) hker)
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
    (X ⧸ center X)).toEquiv, QuotientGroup.ker_mk'] at hdvd
  exact hodd.of_dvd_nat hdvd

omit [Finite X] in
theorem not_odd_card_center {c : X} (hc2 : orderOf c = 2) (hcZ : c ∈ center X) :
    ¬ Odd (Nat.card (center X)) := fun hodd => by
  have h1 : orderOf (⟨c, hcZ⟩ : center X) ∣ Nat.card (center X) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hc2] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

end P58b

open P58b

theorem noConfig_exc_of
    (hE : ∀ τ ∈ chevalleyExceptionalTags, Foote5.OddLieCore.Exc.NoPSLTwoOddCentreComponent τ)
    {τ : StatedLieTag} (hτ : τ ∈ chevalleyExceptionalTags) (n : ℕ) :
    Harris82Lemma58bNoConfig τ n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q hcfg
  have : Fact p.Prime := ⟨hp⟩
  have h5 : 5 ≤ p ^ k := hcfg.2.2.2.2.2.2.1
  have hZS := center_quotient_eq_bot hX
  obtain ⟨hxx, hx1, J, hJ, hJm⟩ := exists_psl2_lieModel_component hX
    (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hp2 hcfg
  obtain ⟨rfl, hce⟩ := exc_model_of_lieModel hτ hm
  have hmS : LieModel ((X ⧸ center X) ⧸ center (X ⧸ center X)) τ 0 p f :=
    LieType.CurtisTits.lieModel_of_mulEquiv (quotientCenterEquiv hX).symm hm
  have hZ2 : IsPGroup 2 (center (X ⧸ center X)) := by
    rw [hZS]
    exact IsPGroup.of_bot
  have hxZ : QuotientGroup.mk' (center X) t ∉ center (X ⧸ center X) := by
    rw [hZS, mem_bot]
    exact hx1
  exact hE τ hτ (X ⧸ center X) hZ2 p f hp hp2 hce.1 hmS _ hxx hxZ J hJ p k hp h5 hJm

theorem noConfig_twistedG2 (hTB : CFSG.TauCetiBridge.TypewiseBridges)
    (hGA : TBLit.GriessMultipliersAllModels) (n : ℕ) : Harris82Lemma58bNoConfig .twistedG2 n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q hcfg
  obtain ⟨hc2, hcZ, -⟩ := hcfg
  have hmod : CFSG.Models.LieModel (X ⧸ center X) .twistedG2 0 p f := by
    rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', hr⟩ | ⟨-, ht', -⟩
    · exact absurd ht' (by decide)
    · exact absurd ht' (by decide)
    · exact ⟨hr.1, Or.inr ⟨rfl, CFSG.TauCetiBridge.exists_index_of_exceptional hTB hr.1.1 hp2
        (.inr ⟨ht', hr⟩)⟩⟩
    · exact absurd ht' (by decide)
  obtain ⟨-, ⟨eM⟩⟩ := hGA _ .twistedG2 0 p f hmod
  have hodd : Odd (Nat.card (CFSG.Open.griessHopfMultiplier (X ⧸ center X))) := by
    rw [Nat.card_congr eM.toEquiv]
    exact Burgoyne.B.odd_card_multiplier_twisted (Or.inr (Or.inr rfl)) hp2
  exact not_odd_card_center hc2 hcZ (odd_card_center_of_odd_multiplier hX hodd)

theorem noConfig_char_two {τ : StatedLieTag} (hτ : τ = .twistedB2 ∨ τ = .twistedF4 ∨ τ = .Tits)
    (n : ℕ) : Harris82Lemma58bNoConfig τ n := by
  intro X _ _ hX _ p f hp hp2 hm k c t Q hcfg
  rcases hm with ⟨ht', -⟩ | ⟨-, ht', -⟩ | ⟨-, ht', hr⟩ | ⟨-, ht', hsz⟩
  · rcases hτ with rfl | rfl | rfl <;> exact absurd ht' (by decide)
  · rcases hτ with rfl | rfl | rfl <;> exact absurd ht' (by decide)
  · rcases hτ with rfl | rfl | rfl
    · exact absurd ht' (by decide)
    · exact hp2 hr.1.2.2.2.1
    · exact hp2 hr.1.2.2.2.1
  · exact hp2 hsz.1

end CFSG.ComponentClassification.HarrisLit.T1
