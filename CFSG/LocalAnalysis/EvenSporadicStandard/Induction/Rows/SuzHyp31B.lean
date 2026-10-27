module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzHyp31A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.SuzPairInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.InnerInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L3Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FourALam2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.Sporadic.SuzOddCore


theorem suz_link_pair (hout : SuzOuterNoLink) {G : Type} [Group G] [Finite G]
    {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .Suz L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKSuz (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ ℓ : G, SuzQ G L K₁ ℓ := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.Suz ≠ .M)
  have hne : K₁ ≠ L := by
    intro hKL
    subst hKL
    exact suz_kNeL ⟨.Suz, List.mem_singleton_self _, hcov.1, hcov.2.1, hcov.2.2⟩ hIsK
      ⟨MulEquiv.refl _⟩
  obtain ⟨hKL, σ, hσ1, hσ2, hσapp, hσK⟩ := link5b_aut h hK hne
  obtain ⟨l, hl⟩ := hout G L K₁ hcov hKL hK hIsK σ hσ2 hσK
  obtain ⟨l', hl'2, hl'⟩ := exists_involution_of_inner hcov.2.1 hσ1 hσ2 hl
  have ht2' : orderOf (l' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hl'2
  have hcomm : ∀ k ∈ K₁, k * (l' : G) = (l' : G) * k := by
    intro k hk
    have h1 := hσK ⟨k, hKL hk⟩ hk
    rw [hl'] at h1
    have h2 : (l' : G) * k * (l' : G)⁻¹ = k := congrArg Subtype.val h1
    calc k * (l' : G) = ((l' : G) * k * (l' : G)⁻¹) * l' := by rw [h2]
      _ = (l' : G) * k := by group
  exact ⟨(l' : G), suz_pair_of_involution G L K₁ hcov hKL hK hIsK l' ht2' hcomm⟩

theorem suz_std_row (hout : SuzOuterNoLink) {G : Type} [Group G] [Finite G]
    (L K₁ T : Subgroup G) (s : G) (hL : ∃ s' ∈ [TauCeti.SporadicName.Suz], OddCover s' L)
    (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKSuz (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ⟩ := suz_link_pair hout hcov h hK hIsK
  have hloc := (sol78SettingLocalQ_suz G L K₁ ℓ hcov hQ).1
  exact ⟨hloc.standard_in_L, hloc.autCentralizer_two⟩

theorem suz_hautC (hout : SuzOuterNoLink) (hN0 : SuzAutCentralizerN0) {G : Type} [Group G]
    [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.Suz], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKSuz (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧
      (∀ A : Subgroup ↥(autCentralizer L N₀), IsPGroup 2 A →
        (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ 4) ∧
      (∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ⟩ := suz_link_pair hout hcov h hK hIsK
  exact hN0 G L K₁ ℓ N₀ hcov hQ hcan

theorem suz_hsec (hb : LieModel ↥suzD .PSL 3 2 2) {G : Type} [Group G] [Finite G]
    (K₁ N₀ : Subgroup G) (hq : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKSuz (↥K₁ ⧸ CFSG.oddCore ↥K₁)) (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁)))) := by
  rintro ⟨h1, h2⟩
  have hodd := odd_center_of_isKSuz_quot hq hIsK
  obtain ⟨e⟩ := cq_equiv_of_isKSuz_quot hq hIsK
  have hL3 : LieModel (↥K₁ ⧸ center ↥K₁) .PSL 3 2 2 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hb
  exact not_sec_of_odd_canLoc hodd hcan (sylowNonabelian_of_lieModel_psl_three (by norm_num) hL3)
    ⟨h1, fun _ => h2⟩

theorem suz_hfix (hk2 : SuzK2FixedNotLam2) (K₂ : Type) [Group K₂] [Finite K₂]
    (hperf : Group.IsPerfect K₂)
    (hX : ∃ (X : Type) (_ : Group X), IsKSuz X ∧ Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X))) :
    InvolutionFixesNotLam2 K₂ (2 * 4) := by
  obtain ⟨X, _, hX, ⟨e⟩⟩ := hX
  obtain ⟨f⟩ := isOddCentralExt_cq hX (IsOddCentralExt.self suzD_quasisimple)
  exact hk2 K₂ hperf ⟨e.trans f⟩

theorem hyp31RowFacts_suz (lit : Sol78Lit) (lo : LieModelOrders) (inp : SuzHyp31Inputs) :
    Hyp31RowFacts IsKSuz [.Suz] [.ONan] [] where
  reach := ⟨SOR, suzReachRow lit inp⟩
  evenOut s hs := by
    rcases List.mem_singleton.1 hs with rfl
    exact inp.even.mono fun _ hx => absurd hx List.not_mem_nil
  up := upFacts_on inp.on_odd
  thm24 := suz_thm24 lo
  std_row _ _ _ L K₁ T s hL _ hdata hq hK := suz_std_row inp.outer L K₁ T s hL hdata hq hK
  four_a := fourAFacts_of_lamLike2 4 (twoSylowStd_suz lit.lemma25 suz_pRank_L)
    (fun _ _ _ L K₁ N₀ T s hL _ hdata hq hK hcan =>
      suz_hautC inp.outer inp.aut_centralizer L K₁ N₀ T s hL hdata hq hK hcan)
    (fun K₂ _ _ hperf hX => suz_hfix inp.k2_fixed K₂ hperf hX)
    (fun _ _ _ K₁ N₀ hq hK hcan => suz_hsec inp.bridge K₁ N₀ hq hK hcan)

end CFSG.EvenSporadicStandard.Induction
