module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7.Orbit
import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.Sub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.Thm3A
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7Ident

@[expose] def RowClassAEmpty : Prop :=
  ∀ (X : Type) [Group X] [Finite X], classicalInvolutionOddCore X = ⊥ → NoNormalTwo X →
    (CFSG.Blueprint.LieModel X .G2 0 3 1 ∨
      (∃ (N : Subgroup X) (_ : N.Normal), N.index = 2 ∧ CFSG.Blueprint.LieModel ↥N .PSU 3 3 1) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic X .M12) →
    ∀ K : Subgroup X, TypeRHyp (CoreAssembly.conjClass K) → AEmpty (CoreAssembly.conjClass K) K

section Aux

theorem noNormalTwo_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : NoNormalTwo B) : NoNormalTwo A := by
  intro P hP hP2
  have h1 := h (P.map e.toMonoidHom) (hP.map _ e.surjective) (hP2.map _)
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1

theorem not_noNormalTwo_dihedralGroup_six : ¬ NoNormalTwo (DihedralGroup 6) := by
  intro h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := DihedralGroup.center_eq_closure_of_even_ne_two (n := 6) (by decide) (by decide)
  have h2 : IsPGroup 2 (Subgroup.center (DihedralGroup 6)) := by
    rw [hc]
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r]
    decide
  have hb := h _ inferInstance h2
  rw [hc] at hb
  have h1 : (DihedralGroup.r ((6 / 2 : ℕ) : ZMod 6) : DihedralGroup 6) = 1 :=
    Subgroup.mem_bot.mp (hb ▸ Subgroup.mem_zpowers _)
  exact absurd h1 (by decide)

end Aux

section Excl

variable {G : Type} [Group G] [Finite G]

theorem false_of_conclG (hR : RowClassAEmpty) {M : Subgroup G}
    (hO : classicalInvolutionOddCore G = ⊥) (h2 : NoNormalTwo G) (hF : FStarSimple G)
    (hΨ : TypeRHyp (CoreAssembly.conjClass M)) (hgen : omegaGen (CoreAssembly.conjClass M) = ⊤)
    (hsub : SubClass (CoreAssembly.conjClass M) M (genFittingFStar G))
    (hA : ¬ AEmpty (CoreAssembly.conjClass M) M)
    (hC : Thm3RConclG (CoreAssembly.conjClass M) M) : False := by
  set Ψ := CoreAssembly.conjClass M with hΨdef
  set L := genFittingFStar G with hLdef
  set X := omegaGen (aStar Ψ M) with hXdef
  haveI : IsSimpleGroup ↥L := hF.1
  have hLn : L.Normal := genFittingFStar_normal G
  have hCL : Subgroup.centralizer (L : Set G) = ⊥ := centralizer_eq_bot_of_fStarSimple hF
  have hMΨ : M ∈ Ψ := CoreAssembly.mem_conjClass_self M
  obtain ⟨J, zM, zJ, hv⟩ := not_aEmpty_iff.mp hA
  have hXn : X.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
    refine iSup₂_le fun N hN => ?_
    by_cases hNA : N ∈ aStar Ψ M
    · exact (T3Core.le_conjStab_aStar hΨ.hyp.conjInvariant hMΨ hNA).trans
        (T3Core.conjStab_le_normalizer_omegaGen _)
    · obtain ⟨⟨heq, hcomm⟩, -⟩ := hC
      refine le_normalizer_omegaGen fun P hP => ?_
      rw [heq] at hNA hP
      exact le_normalizer_of_commutator_le_oddCoreOf ((hcomm N hN hNA P hP).trans inf_le_right)
  have hMX : M ≤ X := le_omegaGen Relation.ReflTransGen.refl
  have hXne : X ≠ ⊥ := fun h => hv.hzK.ne_one (Subgroup.mem_bot.mp (h ▸ hMX hv.hzK.mem))
  have hLX : L ≤ X := le_of_le_normalizer hLn hCL
    (by rw [Subgroup.normalizer_eq_top_iff.mpr hXn]; exact le_top) hXne
  have hOX := oddCore_eq_bot_of_le hO hLn hCL hLX
  have h2X := noNormalTwo_of_le h2 hLn hCL hLX
  let e : CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.SecQuot X ≃* ↥X :=
    (QuotientGroup.quotientMulEquivOfEq hOX).trans QuotientGroup.quotientBot
  have h2Q : NoNormalTwo (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.SecQuot X) :=
    noNormalTwo_of_mulEquiv e h2X
  have hmod : CFSG.Blueprint.LieModel ↥X .G2 0 3 1 ∨
      (∃ (N : Subgroup X) (_ : N.Normal), N.index = 2 ∧ CFSG.Blueprint.LieModel ↥N .PSU 3 3 1) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic ↥X .M12 := by
    rcases hC.2 with hG | ⟨N, hN, hidx, hLie⟩ | hM12 | ⟨E, hE, -, hcard, -⟩ | ⟨W, hW, hWset, ⟨d⟩⟩
    · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hG)
    · haveI := hN
      exact Or.inr (Or.inl ⟨N.map e.toMonoidHom, hN.map _ e.surjective,
        (Subgroup.index_map_equiv N e).trans hidx,
        CFSG.Blueprint.LieModel.of_mulEquiv (N.equivMapOfInjective e.toMonoidHom e.injective)
          hLie⟩)
    · obtain ⟨f⟩ : Nonempty (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf.SecQuot X ≃*
          CFSG.Blueprint.NativeSporadic.Carrier .M12) := hM12
      exact Or.inr (Or.inr ⟨e.symm.trans f⟩)
    · exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hE2 : IsPGroup 2 ↥E := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
      rw [h2Q E hE hE2, Subgroup.card_bot] at hcard
      norm_num at hcard
    · exfalso
      haveI := hW
      have hW2 : IsPGroup 2 ↥W := by
        obtain ⟨η, ⟨S, hS, -⟩, hWη⟩ : W ∈ WSet _ := by rw [hWset]; exact Set.mem_singleton W
        rw [hWη]
        exact S.isPGroup'.to_le (iSup₂_le fun U hU => (hS.1 hU).2)
      have hWb : W = ⊥ := h2Q W hW hW2
      exact not_noNormalTwo_dihedralGroup_six (noNormalTwo_of_mulEquiv
        (d.symm.trans ((QuotientGroup.quotientMulEquivOfEq hWb).trans QuotientGroup.quotientBot))
        h2Q)
  have hsubX : CoreAssembly.conjClass (M.subgroupOf X) ⊆ restrictFamily Ψ X := by
    rintro _ ⟨x, rfl⟩
    refine ⟨conjSub (x : G) M, hΨ.hyp.conjInvariant x M hMΨ, ?_, conjSub_subgroupOf X x M⟩
    have := conjSub_mono (n := (x : G)) hMX
    rwa [conjSub_eq_self_of_mem x.2] at this
  have hΨX : TypeRHyp (CoreAssembly.conjClass (M.subgroupOf X)) :=
    typeRHyp_of_subset (hΨ.restrict X) hsubX (TL4.conjInvariant_conjClass _)
  obtain ⟨l, hl, hlJ⟩ := hsub J hv.mem
  have hlX : l ∈ X := hLX hl
  have hJX : J ≤ X := by
    rw [← hlJ]
    have := conjSub_mono (n := l) hMX
    rwa [conjSub_eq_self_of_mem hlX] at this
  have hJmem : J.subgroupOf X ∈ CoreAssembly.conjClass (M.subgroupOf X) :=
    ⟨⟨l, hlX⟩, (conjSub_subgroupOf X ⟨l, hlX⟩ M).trans (congrArg (fun P => P.subgroupOf X) hlJ)⟩
  have hvX := (aViol_sub_iff (Frame.hypOmegaGen_restrict hΨ.hyp X) hsubX hJmem).mpr
    (aViol_restrict_gen hΨ.hyp hMX hJX hv)
  exact not_aEmpty_iff.mpr ⟨_, _, _, hvX⟩ (hR ↥X hOX h2X hmod _ hΨX)

end Excl

section Ctx


theorem aEmpty_lOrbit (hR : RowClassAEmpty) {m : ℕ} {Y : Type} [Group Y] [Finite Y]
    {Φ : Set (Subgroup Y)} {K : Subgroup Y} (hc : Ctx m Y Φ K) (h2 : NoNormalTwo Y)
    (hF : FStarSimple Y) (hcl : ¬ SubClass Φ K (genFittingFStar Y)) {M : Subgroup Y}
    (hM : M ∈ Φ) : AEmpty (lOrbit (genFittingFStar Y) M) M := by
  by_contra hA
  set L := genFittingFStar Y with hLdef
  set Ψ := lOrbit L M with hΨdef
  set H := omegaGen Ψ with hHdef
  haveI : IsSimpleGroup ↥L := hF.1
  have hLn : L.Normal := genFittingFStar_normal Y
  have hC := centralizer_eq_bot_of_fStarSimple hF
  have hΨΦ : Ψ ⊆ Φ := lOrbit_subset hc.hyp.hyp.conjInvariant hM
  obtain ⟨J, zM, zJ, hv⟩ := not_aEmpty_iff.mp hA
  have hMne : M ≠ ⊥ := fun h => hv.hzK.ne_one (Subgroup.mem_bot.mp (h ▸ hv.hzK.mem))
  have hLH : L ≤ H := le_omegaGen_lOrbit hLn hC hMne
  have hMH : M ≤ H := le_omegaGen mem_lOrbit_self
  have hstab : H ≤ conjStab Ψ := omegaGen_le_conjStab_lOrbit hLn
  by_cases htop : H = ⊤
  ·
    have hinv : ConjInvariant Ψ := fun g N hN =>
      (mem_conjStab_iff.mp (hstab (htop ▸ Subgroup.mem_top g)) N).mpr hN
    have hΨc : Ψ = CoreAssembly.conjClass M := by
      ext N
      constructor
      · rintro ⟨l, -, rfl⟩
        exact ⟨l, rfl⟩
      · rintro ⟨g, rfl⟩
        exact hinv g M mem_lOrbit_self
    have hne : Ψ ≠ Φ := by
      intro h
      apply hcl
      obtain ⟨l, hl, hlK⟩ : K ∈ Ψ := by rw [h]; exact hc.mem
      intro N hN
      obtain ⟨l', hl', rfl⟩ : N ∈ Ψ := by rw [h]; exact hN
      refine ⟨l' * l⁻¹, L.mul_mem hl' (L.inv_mem hl), ?_⟩
      rw [← hlK, ← conjSub_mul, inv_mul_cancel_right]
    have hlt : Ψ.ncard < Φ.ncard :=
      Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hΨΦ, hne⟩) (Set.toFinite Φ)
    have hΨR : TypeRHyp Ψ := typeRHyp_of_subset hc.hyp hΨΦ hinv
    have hCo := hc.inner Ψ hlt hΨR M mem_lOrbit_self hA
    have hsub : SubClass (CoreAssembly.conjClass M) M L := by
      rintro _ ⟨g, rfl⟩
      exact hinv g M mem_lOrbit_self
    rw [hΨc] at hΨR hCo hA
    exact false_of_conclG hR hc.odd h2 hF hΨR (by rw [← hΨc]; exact htop) hsub hA hCo
  ·
    have hlt : Nat.card H < m := hc.card ▸ lt_of_le_of_ne (Subgroup.card_le_card_group _)
      fun h => htop ((Subgroup.card_eq_iff_eq_top _).mp h)
    have hcls := conjClass_subgroupOf_eq hLn hLH
    have hOH := oddCore_eq_bot_of_le hc.odd hLn hC hLH
    have h2H := noNormalTwo_of_le h2 hLn hC hLH
    have hFH := fStarSimple_of_le hLn hF.2 hC hLH
    have hsubΦ : CoreAssembly.conjClass (M.subgroupOf H) ⊆ restrictFamily Φ H := by
      rw [hcls]
      rintro _ ⟨N, hN, hNH, rfl⟩
      exact ⟨N, hΨΦ hN, hNH, rfl⟩
    have hΨH : TypeRHyp (CoreAssembly.conjClass (M.subgroupOf H)) :=
      typeRHyp_of_subset (hc.hyp.restrict H) hsubΦ (TL4.conjInvariant_conjClass _)
    have hJH : J ≤ H := le_omegaGen hv.mem
    have hJmem : J.subgroupOf H ∈ CoreAssembly.conjClass (M.subgroupOf H) := by
      rw [hcls]
      exact subgroupOf_mem_restrictFamily hv.mem hJH
    have hvH := (aViol_sub_iff (Frame.hypOmegaGen_restrict hc.hyp.hyp H) hsubΦ hJmem).mpr
      (aViol_restrict_gen hc.hyp.hyp hMH hJH ((aViol_sub_iff hc.hyp.hyp hΨΦ hv.mem).mp hv))
    have hAH : ¬ AEmpty (CoreAssembly.conjClass (M.subgroupOf H)) (M.subgroupOf H) :=
      not_aEmpty_iff.mpr ⟨_, _, _, hvH⟩
    have hCo := hc.ih.below _ hlt ↥H rfl hOH _ hΨH _ (CoreAssembly.mem_conjClass_self _) hAH
    refine false_of_conclG hR hOH h2H hFH hΨH
      (by rw [hcls]; exact omegaGen_restrictFamily_eq_top _ _ rfl) ?_ hAH hCo
    rw [genFittingFStar_eq_of_le hLn hF.2 hC hLH]
    rintro _ ⟨h, rfl⟩
    obtain ⟨l, hl, hlh⟩ := (mem_conjStab_iff.mp (hstab h.2) M).mpr mem_lOrbit_self
    exact ⟨⟨l, hLH hl⟩, Subgroup.mem_subgroupOf.mpr hl, (conjSub_subgroupOf H ⟨l, hLH hl⟩ M).trans
      ((congrArg (fun P => P.subgroupOf H) hlh).trans (conjSub_subgroupOf H h M).symm)⟩

end Ctx

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.S7
