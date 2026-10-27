module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvAltCD
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvAltLeaves
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvAux
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvBlock
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvChevLeaves
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvGamma7
import CFSG.LocalAnalysis.GLTheoremB.Prop95IvGammaApp

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem a7Facts_holds : A7Facts := ⟨a7Fact1_holds, a7Fact2_holds, a7Fact3_holds, a7Fact4_holds⟩

theorem notCovered_of_lemma96 (h96 : Lemma96) (h : IvSetting m p M D L) : NotCovered M D L := by
  intro T₀ hT₀ hch
  have hp : p.Prime := prime_of_standing h.standing
  have hp2 : p ≠ 2 := ne_two_of_standing h.standing
  exact (h96 G m p h.standing M D h.hyp (tl M L) (isComponentOf_tl hp hp2 h.hyp h.hL h.hn h.hnc h.hQ)
    (tl_commutator_gammaD hp h.hyp h.hL h.hn h.hnc)).1 T₀ hT₀ hch

theorem isGLBlock_of_subgroupOf (hLM : L ≤ M) (hb : IsGLBlock (⊤ : Subgroup ↥M) (L.subgroupOf M)) :
    IsGLBlock M L :=
  ⟨hLM, (CFSG.Open.IsSubnormal.iff_subgroupOf hLM).2 (CFSG.Open.IsSubnormal.top_iff.1 hb.subnormal),
    glBlock_residual_of_subgroupOf hLM hb.residual, glBlock_simple_of_subgroupOf hLM hb.simple,
    glBlock_commutator_of_subgroupOf hLM hb.commutator_le,
    glBlock_unique_noncentral_of_subgroupOf hLM hb.unique_noncentral⟩

theorem prop95IvChev_of_cov (h96 : Lemma96) (hC : Prop95IvChevCov) : Prop95IvChev :=
  fun G _ _ m p hS M D hD hQ L hL hn hc hFF hAlt =>
    hC G m p hS M D hD hQ L hL hn hc (notCovered_of_lemma96 h96 ⟨hS, hD, hQ, hL, hn, hc⟩) hFF hAlt

theorem prop95IvAlt_of_cov (h96 : Lemma96) (hA : Prop95IvAltCov) : Prop95IvAlt :=
  fun G _ _ m p hS M D hD hQ L hL hn hc hAlt =>
    hA G m p hS M D hD hQ L hL hn hc (notCovered_of_lemma96 h96 ⟨hS, hD, hQ, hL, hn, hc⟩) hAlt

theorem chev_beta_action {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (h : IvSetting m p M D L) (hψ : Function.Bijective (psiL h)) (e : ↥(tl M L) ≃* ↥(StatedOmega Q))
    (hc : Nat.card (inducedAutGroup (tl M (gammaD D)) (tl M L)) = 2 ∧
      ActsLikeTransvection Q (tl M (gammaD D)) (tl M L) e) :
    Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
      ActsLikeTransvection Q (barX p M (gammaD D)) (barX p M L)
        ((MulEquiv.ofBijective (psiL h) hψ).symm.trans e) := by
  have hWM : gammaD D ≤ M := gammaD_le h.hyp
  have hWN : gammaD D ≤ Subgroup.normalizer (L : Set G) :=
    gammaD_le_normalizer (prime_of_standing h.standing) h.hyp h.hL h.hn
  refine ⟨(card_inducedAutGroup_tl_eq_bar h hWM hWN).symm.trans hc.1, ?_⟩
  obtain ⟨t, ht, hQt, htr, hact⟩ := hc.2
  refine ⟨t, ht, hQt, htr, ?_⟩
  rw [actsLike_tl_iff_bar h hψ _ _ hWM hWN]
  have he : (MulEquiv.ofBijective (psiL h) hψ).trans
      ((MulEquiv.ofBijective (psiL h) hψ).symm.trans e) = e :=
    MulEquiv.ext fun x => by
      simp only [MulEquiv.coe_trans, Function.comp_apply, MulEquiv.symm_apply_apply]
  rw [he]
  exact hact

theorem concl28aWith_module {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (h : IvSetting m p M D L) (e : ↥(tl M L) ≃* ↥(StatedOmega Q))
    (hmod : ∀ V U : Subgroup ↥M, IsNoncentralChiefFactor (L.subgroupOf M)
      (pCoreOf 2 (L.subgroupOf M)) V U →
      ChiefFactorIso (L.subgroupOf M) U V
        (e.toMonoidHom.comp (toBar (CFSG.pCore 2 ↥M) (L.subgroupOf M)))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v)) :
    ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
      ChiefFactorIso L U V (e.toMonoidHom.comp (toTl M L h.hL.1))
        (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v) := by
  intro V U hVU
  have h1 := hmod (V.subgroupOf M) (U.subgroupOf M) (isNoncentralChiefFactor_subgroupOf h.hL.1 hVU)
  have hpL : pCoreOf 2 L ≤ L := by
    unfold pCoreOf
    exact Subgroup.map_subtype_le _
  have hU : U ≤ M := (hVU.2.1.trans hpL).trans h.hL.1
  have h2 := chiefFactorIso_of_subgroupOf h.hL.1 V U hU _ _ h1
  have h3 : (e.toMonoidHom.comp (toBar (CFSG.pCore 2 ↥M) (L.subgroupOf M))).comp
      (Subgroup.subgroupOfEquivOfLe h.hL.1).symm.toMonoidHom =
        e.toMonoidHom.comp (toTl M L h.hL.1) := by
    refine MonoidHom.ext fun x => ?_
    exact congrArg e (DFunLike.congr_fun (toBar_comp_subgroupOfEquiv h.hL.1) x)
  rwa [h3] at h2

theorem concl28aWith_to_prop95BetaWith {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → ZMod 2) → ZMod 2) (hZ : Subgroup.center ↥(StatedOmega Q) = ⊥)
    (h : IvSetting m p M D L)
    (hc : Concl28aWith Q (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M)) :
    IsGLBlock M L ∧ Prop95BetaWith Q p M D L := by
  obtain ⟨e, hcard, hact, hblock, hmod⟩ := hc
  have hψ : Function.Bijective (psiL h) := chev_psiL_bijective Q hZ h e
  obtain ⟨hcard', hact'⟩ := chev_beta_action Q h hψ e ⟨hcard, hact⟩
  exact ⟨isGLBlock_of_subgroupOf h.hL.1 hblock, h.hL.1,
    (MulEquiv.ofBijective (psiL h) hψ).symm.trans e, hcard', hact',
    chev_beta_module Q h hψ e (concl28aWith_module Q h e hmod)⟩

theorem prop95IvChevCov_of (h1 : Input19_20_2) (h2 : Input19_20_3) (h3 : Input28_10)
    (hΩ : OmegaCentreTrivial) : Prop95IvChevCov := by
  intro G _ _ m p hS M D hD hQ L hL hn hc hcov hFF hAlt
  have h : IvSetting m p M D L := ⟨hS, hD, hQ, hL, hn, hc⟩
  have hch : IsChevTwo (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) := by
    rcases hFF with hCh | ⟨n, hn5, he⟩
    · exact hCh
    · exact absurd ⟨n, hn5, he⟩ hAlt
  have hH1 := chev_hyp28One h h1 hch hAlt
  have hSN : ((gammaD D).subgroupOf M) ≤ Subgroup.normalizer
      ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) := (gammaD_descends h).2.1
  rcases input28_10_applied hcov h3 h (Or.inl rfl) hSN (Or.inl hH1) with hA | hB | hC
  · obtain ⟨-, n, hn2, hQp | hQm⟩ := hA
    · obtain ⟨hblock, hβ⟩ := concl28aWith_to_prop95BetaWith _ (hΩ n hn2).1 h hQp
      have hiso : IsOmegaTwo true (n + 1) ↥(tl M L) := by
        obtain ⟨e, -⟩ := hQp
        exact ⟨e⟩
      exact ⟨hblock, n, by omega, Or.inl ⟨chev_fpf h h2 hch n true (by omega) hiso, hβ⟩⟩
    · obtain ⟨hblock, hβ⟩ := concl28aWith_to_prop95BetaWith _ (hΩ n hn2).2 h hQm
      have hiso : IsOmegaTwo false (n + 1) ↥(tl M L) := by
        obtain ⟨e, -⟩ := hQm
        exact ⟨e⟩
      exact ⟨hblock, n, by omega, Or.inr ⟨chev_fpf h h2 hch n false (by omega) hiso, hβ⟩⟩
  · exact absurd hB.1.1.2 hAlt
  · obtain ⟨e, -⟩ := hC
    exact absurd ⟨7, by norm_num, ⟨e⟩⟩ hAlt

theorem prop95IvChev_of (h96 : Lemma96) (h1 : Input19_20_2) (h2 : Input19_20_3) (h3 : Input28_10)
    (hΩ : OmegaCentreTrivial) : Prop95IvChev :=
  prop95IvChev_of_cov h96 (prop95IvChevCov_of h1 h2 h3 hΩ)

theorem alt_cases (h : IvSetting m p M D L) (h2 : Input19_21_2)
    (hAlt : ∃ n : ℕ, 5 ≤ n ∧
      Nonempty ((↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* alternatingGroup (Fin n))) :
    ActsAsTransposition p (barX p M (gammaD D)) (barX p M L) ∨
      (∃ (k : ℕ) (e : (↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃*
          ↥(alternatingGroup (Fin (k * p + 4)))),
        ActsLikeSubRootFourCQ (barX p M (gammaD D)) (barX p M L) (k * p + 4) e) ∨
      (Nonempty ((↥(barX p M L) ⧸ Subgroup.center ↥(barX p M L)) ≃* alternatingGroup (Fin 6)) ∧
        p = 5 ∧ Nat.card (inducedAutGroup (barX p M (gammaD D)) (barX p M L)) = 2 ∧
        Nonempty (↥(inducedAutGroup (barX p M L ⊔ barX p M (gammaD D)) (barX p M L)) ≃*
          ↥CFSG.QuasithinUnique.A6Models.pgl29)) := by
  obtain ⟨hcomp, ho, hA⟩ := bar_component_data h hAlt
  obtain ⟨hfam, hcinv⟩ := hbar_family h
  obtain ⟨hsig, hle, hinv⟩ := sigmaFam_hbar h
  have hle' : barX p M (gammaD D) ≤ pCoreOf 2 (sigmaFam (barX p M D) (Hbar p M D)) := hle
  rcases h2 (↥M ⧸ GLAPPrimeCore p ↥M) p (prime_of_standing h.standing) (ne_two_of_standing h.standing)
    (barX p M L) hcomp ho hA (barX p M D) (Hbar p M D) hfam hcinv (barX p M (gammaD D)) hle' hinv with
    hc | hb | hC | hd
  · exact absurd hc h.hnc
  · exact Or.inl hb
  · exact Or.inr (Or.inl hC)
  · exact Or.inr (Or.inr hd)

theorem alt_hyp28Two (hI : HatSevenOddInverts) (h : IvSetting m p M D L)
    (hT : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L)) :
    Hyp28Two (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M) := by
  obtain ⟨hAlt, k, e, hk, hact⟩ := alt_transposition_tl h hT
  obtain ⟨h6, h6'⟩ := not_A6_of_degree (prime_of_standing h.standing) (ne_two_of_standing h.standing) hk e
  exact ⟨hAlt, h6, h6', not_isHatSeven_tl_of_transposition hI h hT, k * p + 2, e, hact⟩

theorem alt_prop95Alpha (h : IvSetting m p M D L)
    (hT : ActsAsTransposition p (barX p M (gammaD D)) (barX p M L))
    (hc : Concl28b (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M)) :
    IsGLBlock M L ∧ Prop95Alpha p M D L := by
  obtain ⟨-, n, e₂, hn5, hTr, hblock, hmod⟩ := hc
  obtain ⟨k, hk, rfl, hZ⟩ := alt_degree_kp h hT e₂ hn5
  obtain ⟨e, τ, hτ, hcard, hact, hlink⟩ := alt_alpha_action h hZ e₂ hTr
  refine ⟨isGLBlock_of_subgroupOf h.hL.1 hblock, k, hk, h.hL.1, e, τ, hτ, hcard, hact,
    fun V U hVU => ?_⟩
  have hρ : e.toMonoidHom.comp (barMap p h.hL.1) =
      (e₂.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(tl M L)))).comp
        (toTl M L h.hL.1) := MonoidHom.ext hlink
  rw [hρ]
  exact concl28b_module h e₂ hmod V U hVU

theorem gamma_sigma_data (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1)
    (h : IvSetting m p M D L) (hp3 : p = 3)
    (e : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin 7))) :
    Gamma7Concl (tl M L) e (tl M D) (Hfam M D) :=
  gamma7_sigma hA hM h1 e (gamma7Data_tl hM h hp3 ⟨e⟩)
    (fun hle => not_tl_gammaD_le_centralizer h ((tl_gammaD_le_pCore h).trans hle))

theorem gamma_second (hcov : NotCovered M D L) (h3 : Input28_10) (hAC : AltNotChevTwo)
    (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1) (h : IvSetting m p M D L)
    (hp3 : p = 3)
    (e : (↥(tl M L) ⧸ Subgroup.center ↥(tl M L)) ≃* ↥(alternatingGroup (Fin 7))) :
    IsGLBlock M L ∧ Nonempty (↥(tl M L) ≃* ↥(alternatingGroup (Fin 7))) ∧
      ∀ V U : Subgroup G, IsNoncentralChiefFactor L (pCoreOf 2 L) V U →
        Nat.card U = 16 * Nat.card V := by
  obtain ⟨hyp, hSN, hcard⟩ := hyp28Three_sigma hAC h e (gamma_sigma_data hA hM h1 h hp3 e)
  rcases input28_10_applied hcov h3 h (Or.inr rfl) hSN (Or.inr (Or.inr (Or.inl hyp))) with
    hA' | hB | hC
  · exact absurd hyp.1 hA'.1.2.1
  · exact (not_concl28b_of_hyp28Three _ _ _ hyp hB).elim
  · obtain ⟨e', -, hblk⟩ := hC
    obtain ⟨hb, hiso, hchief⟩ := hblk hcard
    refine ⟨isGLBlock_of_subgroupOf h.hL.1 hb, hiso, fun V U hVU => ?_⟩
    have hUL : U ≤ L := hVU.2.1.trans (Subgroup.map_subtype_le _)
    have hVL : V ≤ L := (hVU.1.1.le).trans hUL
    have := hchief (V.subgroupOf M) (U.subgroupOf M) (isNoncentralChiefFactor_subgroupOf h.hL.1 hVU)
    rwa [card_subgroupOf_eq (hUL.trans h.hL.1), card_subgroupOf_eq (hVL.trans h.hL.1)] at this

theorem prop95Gamma_of_concl28c (hcov : NotCovered M D L) (h3 : Input28_10) (hAC : AltNotChevTwo)
    (hA : A7Facts) (hM : AltSixSevenCentre) (h1 : Input19_21_1) (h : IvSetting m p M D L)
    (hp3 : p = 3)
    (hc : Concl28c (CFSG.pCore 2 ↥M) (L.subgroupOf M) ((gammaD D).subgroupOf M)) :
    IsGLBlock M L ∧ Prop95Gamma p M D L := by
  obtain ⟨e, hR, -⟩ := hc
  obtain ⟨hb, ⟨eA⟩, hchief⟩ := gamma_second hcov h3 hAC hA hM h1 h hp3 e
  have hZ : Subgroup.center ↥(tl M L) = ⊥ := center_eq_bot_of_equiv_alt7 eA
  have hψ := psiL_bijective_of_center_eq_bot h hZ
  obtain ⟨e_bar, hcard, hact⟩ := gamma_action h hψ hZ e hR
  exact ⟨hb, hp3, e_bar, hcard, hact, hchief⟩

theorem prop95IvAltCov_of (h2 : Input19_21_2) (h1 : Input19_21_1) (h3 : Input28_10)
    (hAC : AltNotChevTwo) (hI : HatSevenOddInverts) (hM : AltSixSevenCentre) (hA7 : A7Facts) :
    Prop95IvAltCov := by
  intro G _ _ m p hS M D hD hQ L hL hn hc hcov hAlt
  have h : IvSetting m p M D L := ⟨hS, hD, hQ, hL, hn, hc⟩
  have hSN := (gammaD_descends h).2.1
  rcases alt_cases h h2 hAlt with hT | ⟨k, e, hR⟩ | hd
  · have hyp := alt_hyp28Two hI h hT
    rcases input28_10_applied hcov h3 h (Or.inl rfl) hSN (Or.inr (Or.inl hyp)) with hA | hB | hC
    · exact absurd hyp.1 hA.1.2.1
    · obtain ⟨hb, hα⟩ := alt_prop95Alpha h hT hB
      exact ⟨hb, Or.inl hα⟩
    · exact (not_concl28c_of_hyp28Two _ _ _ hyp hC).elim
  · have hyp := alt_hyp28Three hAC h k e hR
    rcases input28_10_applied hcov h3 h (Or.inl rfl) hSN (Or.inr (Or.inr (Or.inl hyp))) with
      hA | hB | hC
    · exact absurd hyp.1 hA.1.2.1
    · exact (not_concl28b_of_hyp28Three _ _ _ hyp hB).elim
    · have hp3 := prime_eq_three_of_concl28c h k e hC
      obtain ⟨hb, hγ⟩ := prop95Gamma_of_concl28c hcov h3 hAC hA7 hM h1 h hp3 hC
      exact ⟨hb, Or.inr hγ⟩
  · have hyp := alt_hyp28Four hM h hd
    exact ((not_concl28abc_of_hyp28Four _ _ _ hyp)
      (input28_10_applied hcov h3 h (Or.inl rfl) hSN (Or.inr (Or.inr (Or.inr hyp))))).elim

theorem prop95IvAlt_of (h96 : Lemma96) (h2 : Input19_21_2) (h1 : Input19_21_1) (h3 : Input28_10)
    (hAC : AltNotChevTwo) (hI : HatSevenOddInverts) (hM : AltSixSevenCentre) (hA7 : A7Facts) :
    Prop95IvAlt :=
  prop95IvAlt_of_cov h96 (prop95IvAltCov_of h2 h1 h3 hAC hI hM hA7)

theorem prop95Iv_of (h96 : Lemma96) (h1920_2 : Input19_20_2) (h1920_3 : Input19_20_3)
    (h1921_1 : Input19_21_1) (h1921_2 : Input19_21_2) (h2810 : Input28_10)
    (hΩ : OmegaCentreTrivial) (hAC : AltNotChevTwo) (hI : HatSevenOddInverts)
    (hM : AltSixSevenCentre) (hA7 : A7Facts) : Prop95IvChev ∧ Prop95IvAlt :=
  ⟨prop95IvChev_of h96 h1920_2 h1920_3 h2810 hΩ,
    prop95IvAlt_of h96 h1921_2 h1921_1 h2810 hAC hI hM hA7⟩

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
