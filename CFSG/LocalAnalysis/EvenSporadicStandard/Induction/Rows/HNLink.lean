module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.HNReach
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Even
public import CFSG.RankThree.PartTwo.Census.Sporadic.Centralizer
public import CFSG.Sporadic.HN.Local.Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.TwoHS
  CFSG.EvenSporadicStandard.Induction.Hyp

@[expose] def HNOuterInvCent : Prop :=
  ∀ (X : Type) [Group X], IsSporadic X .HN → ∀ σ : MulAut X, σ * σ = 1 →
    (¬ ∃ g : X, σ = MulAut.conj g) → Nat.card ↥(fixSubgroup σ) ≤ 3628800

@[expose] def HSFixedNonsolvable : Prop :=
  ∀ (X : Type) [Group X], IsSporadic X .HS → ∀ α : MulAut X, α ≠ 1 → α * α = 1 →
    ¬ Group.IsSolvable ↥(fixSubgroup α)

@[expose] def HNMultiplierOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSporadic (X ⧸ center X) .HN →
    Odd (Nat.card (center X))

section HNLink


theorem card_centralizer_singleton_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) (a : A) :
    Nat.card ↥(centralizer ({a} : Set A)) = Nat.card ↥(centralizer ({e a} : Set B)) := by
  rw [← map_centralizer_singleton e a]
  exact (Subgroup.card_map_of_injective e.injective).symm

theorem hn_native_involution_centralizer_le (g : CFSG.Blueprint.NativeSporadic.HN)
    (hg : orderOf g = 2) :
    Nat.card ↥(centralizer ({g} : Set CFSG.Blueprint.NativeSporadic.HN)) ≤ 177408000 := by
  have hg2 : g ^ 2 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg1 : g ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hg
    omega
  rcases CFSG.Sporadic.HN.Local.hn_involution_cover g hg2 hg1 with h | h
  · rw [← CFSG.RankThree.PartTwo.Census.card_centralizer_of_isConj h,
      CFSG.Sporadic.HN.Local.hn_card_centralizer_t2]
  · rw [← CFSG.RankThree.PartTwo.Census.card_centralizer_of_isConj h,
      CFSG.Sporadic.HN.Local.hn_card_centralizer_t4]
    norm_num

theorem hn_involution_centralizer_le {Y : Type} [Group Y] (hY : IsSporadic Y .HN) {a : Y}
    (ha : orderOf a = 2) : Nat.card ↥(centralizer ({a} : Set Y)) ≤ 177408000 := by
  obtain ⟨e⟩ := hY
  rw [card_centralizer_singleton_mulEquiv e a]
  have hord : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
  exact hn_native_involution_centralizer_le (e a) hord

theorem hs_cover_fixed (hsfix : HSFixedNonsolvable) (ab : Prop) {K₂ : Type} [Group K₂] [Finite K₂]
    (hperf : Group.IsPerfect K₂) (hS : IsSporadic (K₂ ⧸ center K₂) .HS) :
    ∀ α : MulAut K₂, α ≠ 1 → α * α = 1 →
      ¬ LamProfile ab 8 (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
        ((∃ k : K₂, α = MulAut.conj k) → ¬ LamProfile ab 8 ↥(fixSubgroup α)) := by
  have hle := hs_cover_card_center_le_two hperf hS
  have h0 : 0 < Nat.card (center K₂) := Nat.card_pos
  have hcases : Nat.card (center K₂) = 1 ∨ Nat.card (center K₂) = 2 := by omega
  rcases hcases with h1 | h2
  · have hZ : center K₂ = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hK2 : IsSporadic K₂ .HS := isSporadic_of_center_eq_bot hZ hS
    exact not_lamProfile_of_nonsolvable 8 ab (hsfix K₂ hK2)
  · obtain ⟨M⟩ := exists_coverModel hperf h2 hS
    exact not_lamProfile_of_fixesElem ab (involutionFixesElem_of_coverModel hperf M)
      (by norm_num : 8 < 16)

attribute [local irreducible] CFSG.Blueprint.NativeSporadic.carrierGroup

theorem hn_link_pair (hmult : OddMultTrivial .HN) (hout : HNOuterInvCent)
    {G : Type} [Group G] [Finite G] {L K₁ T : Subgroup G} {s : G}
    (hcov : OddCover .HN L) (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKHN (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ ℓ : G, PairShape (· = 88704000) G L K₁ ℓ ∧ CFSG.oddCore ↥K₁ = ⊥ := by
  have hfin : Finite (Carrier .HN) := CFSG.Sporadic.finite_carrier_of_ne_M .HN (by decide)
  have hL : IsSporadic ↥L .HN := oddCover_isSporadic hfin hmult hcov
  have hZL : center ↥L = ⊥ := hmult ↥L hcov.1 hcov.2.1 hcov.2.2
  obtain ⟨-, -, -, hc⟩ := isKHN_data hIsK
  have hcardK : Nat.card ↥K₁ = 88704000 * Nat.card ↥(CFSG.oddCore ↥K₁) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore ↥K₁)
    rw [hc] at h1
    exact h1
  have hodd : Odd (Nat.card ↥(CFSG.oddCore ↥K₁)) := odd_card_oddCore' ↥K₁
  have hcardL : Nat.card ↥L = 273030912000000 := hn_pinned_card ↥L hL
  have hne : K₁ ≠ L := by
    intro hKL
    have h1 : Nat.card ↥K₁ = 273030912000000 := hKL ▸ hcardL
    obtain ⟨j, hj⟩ := hodd
    omega
  obtain ⟨hKL, σ, hσ1, hσ2, hσapp, hσK⟩ := link5b_aut h hK hne
  have hcardK' : Nat.card ↥(K₁.subgroupOf L) = Nat.card ↥K₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have ho0 : 0 < Nat.card ↥(CFSG.oddCore ↥K₁) := Nat.card_pos
  by_cases hin : ∃ g : ↥L, σ = MulAut.conj g
  swap
  · exfalso
    have hfix : Nat.card ↥(fixSubgroup σ) ≤ 3628800 := hout ↥L hL σ hσ2 hin
    have hle : K₁.subgroupOf L ≤ fixSubgroup σ := fun k hk =>
      hσK k (Subgroup.mem_subgroupOf.1 hk)
    have h1 : Nat.card ↥(K₁.subgroupOf L) ≤ Nat.card ↥(fixSubgroup σ) :=
      Subgroup.card_le_of_le hle
    omega
  · obtain ⟨l, hl⟩ := hin
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
    have hℓ2 : orderOf (l : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hord
    have hcomm : ∀ k ∈ K₁, k * (l : G) = (l : G) * k := by
      intro k hk
      have h1 := hσK ⟨k, hKL hk⟩ hk
      rw [hl] at h1
      have h2 : (l : G) * k * (l : G)⁻¹ = k := congrArg Subtype.val h1
      calc k * (l : G) = ((l : G) * k * (l : G)⁻¹) * l := by rw [h2]
        _ = (l : G) * k := by group
    have hcent : K₁.subgroupOf L ≤ centralizer ({l} : Set ↥L) := by
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact hcomm k (Subgroup.mem_subgroupOf.1 hk))
    have h1 : Nat.card ↥(K₁.subgroupOf L) ≤ Nat.card ↥(centralizer ({l} : Set ↥L)) :=
      Subgroup.card_le_of_le hcent
    have h2 := hn_involution_centralizer_le hL hord
    have hodd' : Odd (Nat.card ↥(CFSG.oddCore ↥K₁)) := hodd
    obtain ⟨j, hj⟩ := hodd'
    have ho1 : Nat.card ↥(CFSG.oddCore ↥K₁) = 1 := by omega
    refine ⟨(l : G), ⟨l.2, hℓ2, hKL, hcomm, ?_⟩, Subgroup.eq_bot_of_card_eq _ ho1⟩
    rw [hcardK, ho1]

theorem hn_std_row (hmult : OddMultTrivial .HN) (hout : HNOuterInvCent)
    {G : Type} [Group G] [Finite G] (L K₁ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.HN], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKHN (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ, -⟩ := hn_link_pair hmult hout hcov h hK hIsK
  have hloc := solomonLocalQ_hn hmult hcov hQ
  exact ⟨hloc.standard_in_L, hloc.autCentralizer_two⟩

theorem hn_canLoc_eq {G : Type} [Group G] [Finite G] {K₁ N₀ : Subgroup G}
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKHN (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) : N₀ = K₁ ∧ Even (Nat.card ↥(center ↥K₁)) := by
  obtain ⟨-, hz, -, -⟩ := isKHN_data hIsK
  have : Group.IsPerfect ↥K₁ := hK.1
  have hev : Even (Nat.card ↥(center ↥K₁)) :=
    even_card_center_of_cover (QuotientGroup.mk' (CFSG.oddCore ↥K₁))
      (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact oddCore_le_center hK) (by rw [hz]; exact even_two)
  rcases hcan with ⟨-, h⟩ | ⟨hodd, -⟩
  · exact ⟨h, hev⟩
  · exact absurd hev (Nat.not_even_iff_odd.2 hodd)

theorem hn_hautC (hmult : OddMultTrivial .HN) (hout : HNOuterInvCent)
    {G : Type} [Group G] [Finite G] (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.HN], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKHN (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 2 ∧
      ElemBound 4 ↥(autCentralizer L N₀) ∧
      (False → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ, -⟩ := hn_link_pair hmult hout hcov h hK hIsK
  obtain ⟨rfl, -⟩ := hn_canLoc_eq hK hIsK hcan
  obtain ⟨-, -, -, -, -, hsol, htwo, -⟩ :=
    (lemma36DataQ_hn hmult (hnFixesElem_of_mult hmult)).data G L N₀ ℓ hcov hQ
  exact ⟨hsol, htwo, elemBound_of_twoAdic (m := 2) htwo, fun h => h.elim⟩

theorem hn_hsec {G : Type} [Group G] [Finite G] (K₁ N₀ : Subgroup G)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKHN (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (False → TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map
        (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨hsolv, -⟩
  obtain ⟨rfl, -⟩ := hn_canLoc_eq hK hIsK hcan
  have himg : (N₀.subgroupOf N₀).map (QuotientGroup.mk' (center ↥N₀)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [himg] at hsolv
  have hsolv' : Group.IsSolvable (↥N₀ ⧸ center ↥N₀) :=
    Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).toMonoidHom)
      (Subgroup.topEquiv (G := ↥N₀ ⧸ center ↥N₀)).surjective
  have := hK.2.1
  obtain ⟨a, b, hab⟩ := hK.2.2
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv' a b)

end HNLink

end CFSG.EvenSporadicStandard.Induction
