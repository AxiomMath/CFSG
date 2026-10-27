module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONHyp31A
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.InnerInv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowLink
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RowGen2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONPairInv

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp CFSG.ONSchreier CFSG.Sporadic.SuzOddCore Cover
  CFSG.ComponentClassification.PerfectAutomorphisms


theorem on_outer_inner (hJ1 : ONOuterFixedJ1) {H : Type} [Group H] [Finite H] (L K : Subgroup H)
    (hcov : OddCover .ONan L) (hKL : K ≤ L) (hK : IsKON (↥K ⧸ CFSG.oddCore ↥K))
    (σ : MulAut ↥L) (hσ2 : σ * σ = 1) (hσK : ∀ k : ↥L, (k : H) ∈ K → σ k = k) :
    ∃ g : ↥L, σ = MulAut.conj g := by
  by_contra hout
  push Not at hout
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have : Finite ↥K := Finite.of_injective _ (Subgroup.inclusion_injective hKL)
  have hLperf : Group.IsPerfect ↥L := hcov.1.1
  have hσ'2 : centerQuotientHom ↥L σ * centerQuotientHom ↥L σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  have hout' : ∀ y : ↥L ⧸ center ↥L, centerQuotientHom ↥L σ ≠ MulAut.conj y := by
    intro y hy
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    refine hout g (centerQuotientHom_injective ↥L ?_)
    rw [CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_conj]
    exact hy
  obtain ⟨e⟩ := hJ1 (↥L ⧸ center ↥L) hcov.2.2 _ hσ'2 hout'
  have hfix : Nat.card ↥(fixSubgroup (centerQuotientHom ↥L σ)) = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have hle : (K.subgroupOf L).map (q ↥L) ≤ fixSubgroup (centerQuotientHom ↥L σ) := by
    rintro _ ⟨k, hk, rfl⟩
    show (centerQuotientHom ↥L σ) (q ↥L k) = q ↥L k
    have h1 := onCenterQuotient_apply_mk σ k
    have h2 : σ k = k := hσK k (Subgroup.mem_subgroupOf.1 hk)
    change onCenterQuotient σ (q ↥L k) = q ↥L k
    rw [h1, h2]
  have hdvd : Nat.card ↥((K.subgroupOf L).map (q ↥L)) ∣ 175560 :=
    hfix ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨hKq', π, hπs, hπc, hπo⟩ := hK
  have hqcard : Nat.card (↥K ⧸ CFSG.oddCore ↥K) = 80640 * Nat.card π.ker := by
    rw [← card_onL, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπs).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  obtain ⟨r, hr, hcard⟩ := exists_odd_card_map_q hKL hcov.2.1
  have h256 : 256 ∣ Nat.card ↥((K.subgroupOf L).map (q ↥L)) := by
    rw [hcard, hqcard]
    exact ⟨315 * Nat.card π.ker * r, by ring⟩
  have h2 := h256.trans hdvd
  norm_num at h2

theorem on_link_pair (hJ1 : ONOuterFixedJ1) {G : Type} [Group G] [Finite G]
    {L K₁ T : Subgroup G} {s : G} (hcov : OddCover .ONan L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKON (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    ∃ ℓ : G, ONQ G L K₁ ℓ := by
  have : Finite ↥L := hcov.finite (by decide : TauCeti.SporadicName.ONan ≠ .M)
  have hne : K₁ ≠ L := by
    intro hKL
    subst hKL
    exact on_kNeL ⟨.ONan, List.mem_singleton_self _, hcov.1, hcov.2.1, hcov.2.2⟩ hIsK
      ⟨MulEquiv.refl _⟩
  obtain ⟨hKL, σ, hσ1, hσ2, hσapp, hσK⟩ := link5b_aut h hK hne
  obtain ⟨l, hl⟩ := on_outer_inner hJ1 L K₁ hcov hKL hIsK σ hσ2 hσK
  obtain ⟨l', hl'2, hl'⟩ := exists_involution_of_inner hcov.2.1 hσ1 hσ2 hl
  have ht2' : orderOf (l' : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hl'2
  have hcomm : ∀ k ∈ K₁, k * (l' : G) = (l' : G) * k := by
    intro k hk
    have h1 := hσK ⟨k, hKL hk⟩ hk
    rw [hl'] at h1
    have h2 : (l' : G) * k * (l' : G)⁻¹ = k := congrArg Subtype.val h1
    calc k * (l' : G) = ((l' : G) * k * (l' : G)⁻¹) * l' := by rw [h2]
      _ = (l' : G) * k := by group
  exact ⟨(l' : G), on_pair_of_involution G L K₁ hcov hKL hK hIsK l' ht2' hcomm⟩

theorem on_std_row (hJ1 : ONOuterFixedJ1) {G : Type} [Group G] [Finite G]
    (L K₁ T : Subgroup G) (s : G) (hL : ∃ s' ∈ [TauCeti.SporadicName.ONan], OddCover s' L)
    (h : Sol78Link5bData K₁ L T s) (hK : CFSG.IsQuasisimple ↥K₁)
    (hIsK : IsKON (↥K₁ ⧸ CFSG.oddCore ↥K₁)) :
    SolStd (K₁.subgroupOf L) ∧ twoAdic (autCentralizer L K₁) ≤ 2 := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  obtain ⟨ℓ, hQ⟩ := on_link_pair hJ1 hcov h hK hIsK
  have hloc := (sol78SettingLocalQ_on G L K₁ ℓ hcov hQ).1
  exact ⟨hloc.standard_in_L, hloc.autCentralizer_two⟩

theorem on_canLoc_eq {G : Type} [Group G] [Finite G] {K₁ N₀ : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKON (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) : N₀ = K₁ := by
  rcases hcan with ⟨-, h⟩ | ⟨hodd, -⟩
  · exact h
  · exact absurd (even_center_of_isKON_quot hq hIsK) (Nat.not_even_iff_odd.2 hodd)

theorem on_hautC (hJ1 : ONOuterFixedJ1) {G : Type} [Group G] [Finite G]
    (L K₁ N₀ T : Subgroup G) (s : G)
    (hL : ∃ s' ∈ [TauCeti.SporadicName.ONan], OddCover s' L) (h : Sol78Link5bData K₁ L T s)
    (hK : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKON (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    Group.IsSolvable ↥(autCentralizer L N₀) ∧ twoAdic (autCentralizer L N₀) ≤ 2 ∧
      ElemBound 2 ↥(autCentralizer L N₀) ∧
      (True → ∀ α ∈ autCentralizer L N₀, ∃ g : ↥L, α = MulAut.conj g) := by
  obtain ⟨s', hs', hcov⟩ := hL
  rcases List.mem_singleton.1 hs' with rfl
  rw [on_canLoc_eq hK hIsK hcan]
  obtain ⟨ℓ, hQ⟩ := on_link_pair hJ1 hcov h hK hIsK
  have hloc := (sol78SettingLocalQ_on G L K₁ ℓ hcov hQ).1
  obtain ⟨hu, hu2, hKL, hKu, hKperf, hcard⟩ := hQ
  have hLperf : Group.IsPerfect ↥L := hcov.1.1
  have hTop := isSporadic_top hcov.2.2
  have hP := onPair_quotient hcov hu hu2 hKL hKu hKperf hcard
  have hfacts := on_autFixFacts hTop hP
  exact ⟨autCentralizer_solvable_of_quotient hLperf hfacts.solvable, hloc.autCentralizer_two,
    autCentralizer_elem_of_quotient hLperf hfacts.elem,
    fun _ => autCentralizer_inner_of_quotient hLperf hfacts.inner⟩

theorem on_hsec {G : Type} [Group G] [Finite G] (K₁ N₀ : Subgroup G)
    (hq : CFSG.IsQuasisimple ↥K₁) (hIsK : IsKON (↥K₁ ⧸ CFSG.oddCore ↥K₁))
    (hcan : CanLoc K₁ N₀) :
    ¬ (Group.IsSolvable ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))) ∧
      (True → TwoSubgroupsAbelian ↥((N₀.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁))))) := by
  rintro ⟨h1, -⟩
  rw [on_canLoc_eq hq hIsK hcan] at h1
  apply not_isSolvable_cq_of_isQuasisimple hq
  set A : Subgroup (↥K₁ ⧸ center ↥K₁) :=
    (K₁.subgroupOf K₁).map (QuotientGroup.mk' (center ↥K₁)) with hA
  have hsurj : Function.Surjective A.subtype := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨QuotientGroup.mk x, ⟨x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩⟩, rfl⟩
  exact Group.isSolvable_of_surjective hsurj

theorem on_hfix (hk2 : ONK2FixedNotLam) (K₂ : Type) [Group K₂] [Finite K₂]
    (hperf : Group.IsPerfect K₂)
    (hX : ∃ (X : Type) (_ : Group X), IsKON X ∧ Nonempty ((K₂ ⧸ center K₂) ≃* (X ⧸ center X)))
    (α : MulAut K₂) (h1 : α ≠ 1) (h2 : α * α = 1) :
    ¬ LamProfile True (2 * 2) (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
      ((∃ k : K₂, α = MulAut.conj k) → ¬ LamProfile True (2 * 2) ↥(fixSubgroup α)) := by
  obtain ⟨X, _, hX, ⟨e⟩⟩ := hX
  obtain ⟨f⟩ := isKON_cq_equiv hX
  obtain ⟨hn1, hn2⟩ := hk2 K₂ hperf ⟨e.trans f⟩ α h1 h2
  exact ⟨fun hp => hn1 ⟨hp.1, hp.2.2 trivial, hp.2.1⟩,
    fun hin hp => hn2 hin ⟨hp.1, hp.2.2 trivial, hp.2.1⟩⟩

theorem hyp31RowFacts_on (lit : Sol78Lit) (lo : LieModelOrders) (inp : ONHyp31Inputs) :
    Hyp31RowFacts IsKON [.ONan] [] [.Suz] where
  reach := ⟨SOR, onReachRow lit inp⟩
  evenOut s hs := by
    rcases List.mem_singleton.1 hs with rfl
    exact evenCoverExcl_of_odd inp.on_odd
  up := upFacts_nil
  thm24 := on_thm24 lo
  std_row _ _ _ L K₁ T s hL _ hdata hq hK := on_std_row inp.outer_j1 L K₁ T s hL hdata hq hK
  four_a := fourAFacts_of_lamProfile True 2 2 le_rfl
    (fun _ _ _ L K₁ N₀ T s hL _ hdata hq hK hcan =>
      on_hautC inp.outer_j1 L K₁ N₀ T s hL hdata hq hK hcan)
    (fun K₂ _ _ hperf hX α h1 h2 => on_hfix inp.k2_fixed K₂ hperf hX α h1 h2)
    (fun _ _ _ K₁ N₀ hq hK hcan => on_hsec K₁ N₀ hq hK hcan)

end CFSG.EvenSporadicStandard.Induction
