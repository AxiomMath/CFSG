module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerSplit
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace InnerQ

open CFSG.Open CFSG.AGLEmbedding CFSG.PreuniquenessRankFour.Helpers CFSG.QuasithinUnique
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped commutatorElement

theorem pRank_top_le_one_of_isCyclic {p : ℕ} {K : Type*} [Group K] [Finite K] [Fact p.Prime]
    (T : Sylow p K) (hT : IsCyclic (T : Subgroup K)) : Open.pRank p (⊤ : Subgroup K) ≤ 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨E, -, hE, hEcard⟩ := pRank_attained p hp (⊤ : Subgroup K)
  have hle := card_le_of_isElemAbelian_of_isCyclic_sylow T hT hE
  rw [hEcard] at hle
  by_contra hlt
  push_neg at hlt
  have : p ^ 2 ≤ p ^ Open.pRank p (⊤ : Subgroup K) := Nat.pow_le_pow_right hp.pos hlt
  have : p < p ^ 2 := by nlinarith [hp.two_le]
  omega

theorem exists_outer {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}
    (h : ReducedNongeneration p Y Rb Y₀) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hLY : ¬ L ≤ Y₀)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (h3 : Open.pRank p (Rb : Subgroup Y) = 3) :
    ∃ t a : Y, t ∈ (Rb : Subgroup Y) ⊓ L ∧ orderOf t = p ∧ a ∈ (Rb : Subgroup Y) ∧
      a ^ p = 1 ∧ a * t = t * a ∧ InducesOuterOn a L := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  set N := Subgroup.normalizer (L : Set Y)
  have hRN : (Rb : Subgroup Y) ≤ N := fun v hv => h.sylow_le_normalizer_component hL hv
  obtain ⟨t, ht, htp, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core_eq_bot Rb hL
  obtain ⟨A, hAR, hA, hAcard⟩ := pRank_attained p hp (Rb : Subgroup Y)
  rw [h3] at hAcard
  have hout : ∃ a ∈ A, ¬ ∃ y ∈ L, ∀ w ∈ L, a * w * a⁻¹ = y * w * y⁻¹ := by
    by_contra hall
    push_neg at hall
    set f := L.normalizerMonoidHom
    set S := A.subgroupOf N
    have hineq := pRank_le_pRank_inf_ker_add_pRank_map hp f S
    have h₁ : 3 ≤ Open.pRank p S := by
      rw [← pRank_map_of_injective p hp N.subtype N.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le (hAR.trans hRN)]
      exact le_csSup (pRank_bddAbove p hp _) ⟨A, le_rfl, hA, hAcard⟩
    have h₂ : Open.pRank p (S ⊓ f.ker) ≤ 1 := by
      refine le_trans ?_ (h.pRank_inf_centralizer_le_one_of_not_le hL hLY)
      rw [Subgroup.normalizerMonoidHom_ker,
        ← pRank_map_of_injective p hp N.subtype N.subtype_injective]
      refine pRank_mono p hp ?_
      rintro _ ⟨x, ⟨hxA, hxC⟩, rfl⟩
      exact ⟨hAR hxA, hxC⟩
    have hZ : Subgroup.center L = ⊥ := h.center_eq_bot_of_isCyclic hL hcyc
    have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
      intro g g' hgg
      have hc : g'⁻¹ * g ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro w
        have := congrArg (fun φ : MulAut L => φ w) hgg
        simp only [MulAut.conj_apply] at this
        calc w * (g'⁻¹ * g) = g'⁻¹ * (g' * w * g'⁻¹) * g := by group
          _ = g'⁻¹ * (g * w * g⁻¹) * g := by rw [this]
          _ = g'⁻¹ * g * w := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact (inv_mul_eq_one.mp hc).symm
    have hle : S.map f ≤ (⊤ : Subgroup L).map (MulAut.conj : L →* MulAut L) := by
      rintro _ ⟨⟨x, hxN⟩, hxS, rfl⟩
      obtain ⟨y, hyL, hy⟩ := hall x hxS
      refine ⟨⟨y, hyL⟩, Subgroup.mem_top _, ?_⟩
      ext w
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, f,
        Subgroup.normalizerMonoidHom_apply_apply_coe]
      exact (hy w w.2).symm
    obtain ⟨T, hT⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
      (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
        Subgroup.IsSubnormal.top)
    have hTc : IsCyclic (T : Subgroup L) := by
      have e : (T : Subgroup L) ≃* ((Rb : Subgroup Y) ⊓ L : Subgroup Y) :=
        ((T : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective).trans
          (MulEquiv.subgroupCongr hT)
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    have h₃ : Open.pRank p (S.map f) ≤ 1 := by
      refine (pRank_mono p hp hle).trans ?_
      rw [pRank_map_of_injective p hp _ hinj]
      exact pRank_top_le_one_of_isCyclic T hTc
    omega
  obtain ⟨a, haA, ha⟩ := hout
  have hap : a ^ p = 1 := hA.2 a haA
  have haN : a ∈ N := hRN (hAR haA)
  have hcomm : Commute a t :=
    commute_of_mem_normalizer_zpowers_of_pow_eq_one hp htp
      (mem_normalizer_zpowers_of_mem_zpowers (h.conj_mem_zpowers_of_component hL hcyc ht (hAR haA)))
      hap
  exact ⟨t, a, ht, htp, hAR haA, hap, hcomm.eq, haN, ha⟩

theorem not_gamma_le_of_two_components {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {M H E : Subgroup G} {L L' : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hne : L ≠ L')
    (hL'X : ¬ L' ≤ d1X0 p M H) (hE : IsElemAbelian p E)
    (hEL : (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ⊓ L ≠ ⊥) :
    ¬ rankThreeGamma 1 p E ≤ M := by
  intro hΓ
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  obtain ⟨⟨y, hy⟩, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hEL
  obtain ⟨⟨e, heE, rfl⟩, heL⟩ := hy
  have heE' : (e : G) ∈ E := heE
  have hep : (e : G) ^ p = 1 := hE.2 _ heE'
  have he1 : (e : G) ≠ 1 := by
    intro h1
    apply hne1
    have : e = 1 := Subtype.ext h1
    exact Subtype.ext (by simp [this])
  have hord : orderOf (e : G) = p := orderOf_eq_prime hep he1
  have hordH : orderOf e = p := (Subgroup.orderOf_coe e).symm.trans hord
  have heP : IsPGroup p (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hordH, pow_one])
  have hN : Subgroup.normalizer ((Subgroup.zpowers (e : G) : Subgroup G) : Set G) ≤ M := by
    refine le_trans ?_ hΓ
    refine le_sSup ⟨Subgroup.zpowers (e : G), Subgroup.zpowers_le.mpr heE', ?_, rfl⟩
    exact le_csSup (pRank_bddAbove p hp _) ⟨Subgroup.zpowers (e : G), le_rfl,
      isElemAbelian_zpowers hep, by rw [Nat.card_zpowers, hord, pow_one]⟩
  apply hL'X
  intro l hl
  have hcomm : l ∈ Subgroup.centralizer ({π e} : Set (H ⧸ primeComplementCore (G := H) p)) := by
    have hc : ⁅L, L'⁆ = ⊥ := by
      rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open L).mpr hL)
        ((CFSG.isComponent_iff_open L').mpr hL') with h | h
      · exact absurd h hne
      · exact h
    have hmem : ⁅π e, l⁆ ∈ ⁅L, L'⁆ := Subgroup.commutator_mem_commutator heL hl
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact Subgroup.mem_centralizer_singleton_iff.mpr hmem.symm
  obtain ⟨g, hg, hgl⟩ := exists_mem_centralizer_mk_eq hp _ (primeComplementCore_coprime p) heP hcomm
  have hgC : (g : G) ∈ Subgroup.normalizer ((Subgroup.zpowers (e : G) : Subgroup G) : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hge : g * e = e * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hge' : (e : G) * g = g * e := by
      have := congrArg Subtype.val hge
      simpa [Subgroup.coe_mul] using this.symm
    exact ((Commute.zpow_left hge' k).eq)
  exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hN hgC⟩, hgl⟩

end InnerQ

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

@[expose] def D1CaseTwoCentral3InnerQOne (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ D1CaseTwoAlphaR p M H R →
      (∀ L L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        IsComponentOf L' ⊤ → L ≠ L' → ¬ L ≤ d1X0 p M H → L' ≤ d1X0 p M H) →
      ∃ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
        ¬ L ≤ d1X0 p M H ∧ ∃ E : Subgroup G, IsFieldOmegaA p M H R L E ∧
          rankThreeGamma 1 p E ≤ M

@[expose] def D1CaseTwoCentral3InnerTwoB (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)), D1ComponentConfig3 p P M H R Rbar →
    (∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
      IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L :
        Subgroup (H ⧸ primeComplementCore (G := H) p))) →
    ∀ z : H, D1CaseTwoCand p M H R z →
      (∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
        Subgroup.centralizer ({(z : G)} : Set G)) →
      ¬ D1CaseTwoAlphaR p M H R →
      ∀ L L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ →
        IsComponentOf L' ⊤ → L ≠ L' → ¬ L ≤ d1X0 p M H → ¬ L' ≤ d1X0 p M H → False

theorem d1CaseTwoCentral3InnerQ_of_split {G : Type} [Group G] [Finite G]
    (h1 : D1CaseTwoCentral3InnerQOne G) (h2 : D1CaseTwoCentral3InnerTwoB G) :
    D1CaseTwoCentral3InnerQ G := by
  intro p P M H R Rbar hcfg hcyc z hz hcen hα
  by_cases htwo : ∃ L L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ ∧
      IsComponentOf L' ⊤ ∧ L ≠ L' ∧ ¬ L ≤ d1X0 p M H ∧ ¬ L' ≤ d1X0 p M H
  · obtain ⟨L, L', hL, hL', hne, hLX, hL'X⟩ := htwo
    exact (h2 p P M H R Rbar hcfg hcyc z hz hcen hα L L' hL hL' hne hLX hL'X).elim
  · refine h1 p P M H R Rbar hcfg hcyc z hz hcen hα fun L L' hL hL' hne hLX => ?_
    by_contra hL'X
    exact htwo ⟨L, L', hL, hL', hne, hLX, hL'X⟩

theorem d1CaseTwoCentral3InnerTwoB_of_innerQ {G : Type} [Group G] [Finite G]
    (hQ : D1CaseTwoCentral3InnerQ G) : D1CaseTwoCentral3InnerTwoB G := by
  intro p P M H R Rbar hcfg hcyc z hz hcen hα L₁ L₂ hL₁ hL₂ hne hL₁X hL₂X
  obtain ⟨L, hL, -, E, hE, hΓ⟩ := hQ p P M H R Rbar hcfg hcyc z hz hcen hα
  have hp : p.Prime := hcfg.ext.prime
  obtain ⟨L', hL', hne', hL'X⟩ : ∃ L' : Subgroup (H ⧸ primeComplementCore (G := H) p),
      IsComponentOf L' ⊤ ∧ L ≠ L' ∧ ¬ L' ≤ d1X0 p M H := by
    by_cases h : L = L₁
    · exact ⟨L₂, hL₂, h ▸ hne, hL₂X⟩
    · exact ⟨L₁, hL₁, h, hL₁X⟩
  exact InnerQ.not_gamma_le_of_two_components hp hL hL' hne' hL'X hE.2.1 hE.2.2.2.1 hΓ

theorem d1CaseTwoCentral3InnerQ_iff {G : Type} [Group G] [Finite G] :
    D1CaseTwoCentral3InnerQ G ↔ D1CaseTwoCentral3InnerQOne G ∧ D1CaseTwoCentral3InnerTwoB G :=
  ⟨fun hQ => ⟨fun p P M H R Rbar hcfg hcyc z hz hcen hα _ =>
      hQ p P M H R Rbar hcfg hcyc z hz hcen hα, d1CaseTwoCentral3InnerTwoB_of_innerQ hQ⟩,
    fun h => d1CaseTwoCentral3InnerQ_of_split h.1 h.2⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
