module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadRk
public import CFSG.HardMathSupport.Dickson.Sec6.I1431LieAux.Split
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadCover

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartOne.Sec66T
  CFSG.ComponentClassification.RankTwoClassical
open CFSG.HardMathSupport.Dickson.Sec6.I923

@[expose] def FamPslBadHigh : StatedLieTag → ℕ → ℕ → ℕ → Prop :=
  fun t n p f => FamPslBad t n p f ∧ 6 ≤ n

theorem y1431_noCfg_pslBadHigh (hGA : GriessAllModelsStatement) : Y1431NoCfgAt FamPslBadHigh := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨⟨rfl, hn3, hnc⟩, hn6⟩ := hF
  have hC : StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n p f :=
    (lieModel_classical_iff (by decide)).mp hm
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  let e : (Y ⧸ Subgroup.center Y) ≃* projectiveSL n K := e0.trans (statedProjEquiv n K)
  let qY : Y →* projectiveSL n K := (e : (Y ⧸ Subgroup.center Y) →* projectiveSL n K).comp
    (QuotientGroup.mk' (Subgroup.center Y))
  have hq : Function.Surjective qY := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqe : ∀ y, qY y = 1 ↔ y ∈ Subgroup.center Y := fun y => by
    show e (QuotientGroup.mk' (Subgroup.center Y) y) = 1 ↔ _
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff y
  have hker : qY.ker ≤ Subgroup.center Y := fun y hy => (hqe y).1 (MonoidHom.mem_ker.1 hy)
  have h322 : ¬(n = 3 ∧ p = 2 ∧ f = 2) := fun h => by omega
  obtain ⟨ρ, hρ⟩ := exists_slHom_to_cover hGA hadm hK hn3 h322 hnc qY hq hker
  have h3 : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    by_contra h
    exact hnc ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
      (fun h3 => h (h3.trans (Nat.gcd_dvd_right _ _))))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
  exact rkY_false_psl c.rank hn6 hζ ρ qY hρ (fun y hy => (hqe y).2 hy)

end CFSG.HardMathSupport.Dickson.Sec6.I1431
