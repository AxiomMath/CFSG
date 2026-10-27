module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1Hyp31B

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Co1Block
  CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def Co1AutCentralizerN0 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L K : Subgroup H) (u : H) (N₀ : Subgroup H),
    OddCover .Co1 L → Co1Pair H L K u → CanLoc K N₀ →
      Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 2 ∧
        ElemBound 4 ↥(autCentralizer L N₀)


theorem co1_link_pair (hmult : OddMultTrivial .Co1) {G : Type} [Group G] [Finite G]
    {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .Co1 L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKCo1O (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ ℓ : G, Co1Pair G L K₁ ℓ ∧ CFSG.oddCore ↥K₁ = ⊥ := by
  have hL : IsSporadic ↥L .Co1 := hcov.isSporadic_of_mult hmult
  have hZL : center ↥L = ⊥ := hcov.center_eq_bot hmult
  obtain ⟨-, -, hc, -, -⟩ := isKCo1O_facts hIsK
  have hcardK : Nat.card ↥K₁ = 251596800 * Nat.card ↥(CFSG.oddCore ↥K₁) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K₁)
    rw [hc] at h1
    exact h1
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥K₁)) := odd_card_oddCore' ↥K₁
  have hcardL : Nat.card ↥L = 4157776806543360000 := co1_card_pinned ↥L hL
  have hne : K₁ ≠ L := by
    intro hKL
    have h1 : Nat.card ↥K₁ = 4157776806543360000 := hKL ▸ hcardL
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨hKL, σ, hσ1, hσ2, hσapp, hσK⟩ := link5b_aut h hK hne
  obtain ⟨l, hl⟩ := TwoCo1.HypOne.allInner_of_isSporadic hL σ
  have hll : l * l = 1 := by
    have h3 : MulAut.conj (l * l) = (1 : MulAut ↥L) := by
      rw [map_mul, ← hl]
      exact hσ2
    have h2 : l * l ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h4 := congrArg (fun f : MulAut ↥L => f g) h3
      simp only [MulAut.conj_apply, MulAut.one_apply] at h4
      calc g * (l * l) = (l * l * g * (l * l)⁻¹) * (l * l) := by rw [h4]
        _ = l * l * g := by group
    rw [hZL] at h2
    exact Subgroup.mem_bot.1 h2
  have hl1 : l ≠ 1 := by
    intro h1
    apply hσ1
    rw [hl, h1, map_one]
  have hord : orderOf l = 2 := orderOf_eq_prime (by rw [pow_two]; exact hll) hl1
  have hcomm : ∀ k ∈ K₁, k * (l : G) = (l : G) * k := by
    intro k hk
    have h1 := hσK ⟨k, hKL hk⟩ hk
    rw [hl] at h1
    have h2 : (l : G) * k * (l : G)⁻¹ = k := congrArg Subtype.val h1
    calc k * (l : G) = ((l : G) * k * (l : G)⁻¹) * l := by rw [h2]
      _ = (l : G) * k := by group
  have hpair : Co1Pair G L K₁ (l : G) :=
    co1_pair_of_involution hmult G L K₁ hcov hKL hK (j := 1) odd_one (by rw [hc, mul_one]) l hord
      hcomm
  refine ⟨(l : G), hpair, Subgroup.eq_bot_of_card_eq _ ?_⟩
  have h1 : Nat.card ↥K₁ = 251596800 := hpair.2.2.2.2.2
  omega

theorem co1_std_row (hmult : OddMultTrivial .Co1) {G : Type} [Group G] [Finite G]
    (L K₁ T : Subgroup G) (s : G) (hL : ∃ s' ∈ [TauCeti.SporadicName.Co1], OddCover s' L)
    (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKCo1O (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ, -⟩ := co1_link_pair hmult hcov h hK hIsK
  have hloc := solomonLocalQ_of_local hcov (solomonLocal_co1 (hcov.isSporadic_of_mult hmult) hQ)
  exact ⟨hloc.standard_in_L, hloc.autCentralizer_two⟩

theorem co1_hautC (hmult : OddMultTrivial .Co1) (hN0 : Co1AutCentralizerN0) {G : Type} [Group G]
    [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.Co1], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKCo1O (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 2 ∧
      ElemBound 4 ↥(autCentralizer L N₀) ∧
      (True → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ, -⟩ := co1_link_pair hmult hcov h hK hIsK
  obtain ⟨h1, h2, h3⟩ := hN0 G L K₁ ℓ N₀ hcov hQ hcan
  exact ⟨h1, h2, h3, fun _ α _ =>
    TwoCo1.HypOne.allInner_of_isSporadic (hcov.isSporadic_of_mult hmult) α⟩

theorem co1_center_eq_oddCore {G : Type} [Group G] [Finite G] {K₁ : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKCo1O (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    center ↥K₁ = CFSG.oddCore ↥K₁ := by
  obtain ⟨-, -, -, hZ, -⟩ := isKCo1O_facts hIsK
  refine le_antisymm (fun x hx => ?_) (oddCore_le_center hq)
  rw [← QuotientGroup.eq_one_iff]
  have hc : (QuotientGroup.mk x : ↥K₁ ⧸ CFSG.oddCore ↥K₁) ∈
      center (↥K₁ ⧸ CFSG.oddCore ↥K₁) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.1 hx g']
  rw [hZ] at hc
  exact hc

theorem co1_hsec {G : Type} [Group G] [Finite G] (K₁ N₀ : Subgroup G)
    (hq : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKCo1O (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) := by
  have hZO := co1_center_eq_oddCore hq hIsK
  have hodd : Odd (Nat.card ↥(center ↥K₁)) := by
    rw [hZO]
    exact odd_card_oddCore' ↥K₁
  obtain ⟨e⟩ := hIsK
  exact not_sec_of_odd_canLoc hodd hcan (SylowNonabelian.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZO).trans e) sylowNonabelian_twoBD)

theorem co1_fourA (hmult : OddMultTrivial .Co1) (hN0 : Co1AutCentralizerN0)
    (hfix : G24FixedNonsolvable) : FourAFacts IsKCo1O [.Co1] :=
  fourAFacts_of_lamProfile True 2 4 le_rfl
    (fun G _ _ L K₁ N₀ T s hL _ hdata hq hK hcan =>
      co1_hautC hmult hN0 L K₁ N₀ T s hL hdata hq hK hcan)
    (fun K₂ _ _ hperf ⟨X, _, hX, ⟨e⟩⟩ => by
      obtain ⟨-, -, -, hZX, -⟩ := isKCo1O_facts hX
      obtain ⟨f⟩ := hX
      let eX : X ⧸ center X ≃* ↥twoBD :=
        ((QuotientGroup.quotientMulEquivOfEq hZX).trans QuotientGroup.quotientBot).trans f
      exact not_lamProfile_of_nonsolvable (2 * 4) True (fun α h1 h2 =>
        not_isSolvable_fix_of_cover hperf h1 h2 fun β hβ1 hβ2 =>
          hfix _ ⟨e.trans eX⟩ β hβ1 hβ2) )
    (fun G _ _ K₁ N₀ hq hK hcan => co1_hsec K₁ N₀ hq hK hcan)

end CFSG.EvenSporadicStandard.Induction
