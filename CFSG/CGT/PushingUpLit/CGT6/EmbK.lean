module

public import CFSG.CGT.PushingUpLit.CGT6.SixThreeNat
public import CFSG.CGT.PushingUpLit.CGT6.EmbAssembly
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictArrow
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictMinus
public import CFSG.CGT.PushingUpLit.CGT6.EmbDictPlus
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmega
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoConj
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoThree
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightHolds
public import CFSG.CGT.PushingUpLit.SixThree
public import CFSG.CGT.PushingUpLit.SixThreeSylow
public import CFSG.CGT.PushingUpLit.SixThreeV

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.SixThree
open CFSG.Quasithin CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.Open (IsElemAbelian)
open scoped commutatorElement Pointwise

@[expose] def AschbacherEmbeddingFourK : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G →
      ∀ T Y : Subgroup (MulAut V), T ≤ G → T ≠ ⊥ → IsPGroup 2 ↥T →
        Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) →
        (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal →
        ⁅Y, Y⁆ = Y → InClassX ↥(yuHol Y) →
        ∃ X : Subgroup (MulAut V), Y ≤ X ∧ X ≤ G ∧ (X.subgroupOf G).IsSubnormal ∧
          ((InClassX ↥(yuHol X) ∧ ArrowNat (yuHol Y) (yuHol X)) ∨
            ∃ n : ℕ, 2 ≤ n ∧
              (IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥ ∨
                IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥) ∧
              (Y = X ∨ (InClassX ↥(yuHol Y) ∧
                Nonempty (↥Y ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq n)) ∧
                Nat.card ↥(commV Y) = 2 ^ (3 * n))))

@[expose] def AschbacherEmbeddingFiveK : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G : Subgroup (MulAut V), CFSG.IsKGroup ↥G →
      ∀ T Y : Subgroup (MulAut V), T ≤ G → T ≠ ⊥ → IsPGroup 2 ↥T →
        Y ≤ G ⊓ Subgroup.centralizer (T : Set (MulAut V)) →
        (Y.subgroupOf (G ⊓ Subgroup.centralizer (T : Set (MulAut V)))).IsSubnormal →
        Nat.card ↥Y = 3 → Nat.card ↥(commV Y) = 4 →
        ∃ X : Subgroup (MulAut V), Y ≤ X ∧ X ≤ G ∧ (X.subgroupOf G).IsSubnormal ∧
          InClassX ↥(yuHol X) ∧ ArrowNat (yuHol Y) (yuHol X)

@[expose] def AschbacherEmbeddingK : Prop :=
  AschbacherEmbeddingFourK ∧ AschbacherEmbeddingFiveK

theorem isKGroup_of_surjective {G Q : Type} [Group G] [Group Q] (hK : CFSG.IsKGroup G)
    (φ : G →* Q) (hφ : Function.Surjective φ) : CFSG.IsKGroup Q :=
  hK.of_surjective φ hφ

@[expose] def AschbacherEmbeddingAmbK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G → IsCharacteristicP 2 G →
    ∀ (Y V : Subgroup G), InClassX ↥Y → V.Normal → IsElementaryAbelian 2 V →
      ¬ Y ≤ Subgroup.centralizer (V : Set G) →
      (∃ P : Subgroup G, IsPGroup 2 P ∧ ¬ P ≤ Subgroup.centralizer (V : Set G) ∧
        Y ≤ Subgroup.normalizer ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer
          ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal) →
      ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧
        Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (X : Set G) ∧
        IsPGroup 2 ↥(X ⊓ Subgroup.centralizer (V : Set G)) ∧
        ((InClassX ↥X ∧ ⁅oTwoIn X, X⁆ ≤ V ∧ ArrowNat Y X) ∨ OmegaFourOutcome V Y X)

theorem aschbacherEmbeddingAmbK_of_embedding (hE : AschbacherEmbeddingK) (hPlus : EmbDictPlus)
    (hMinus : EmbDictMinus) (hArrow : EmbDictArrow) (hOmega : EmbOmega) :
    AschbacherEmbeddingAmbK := by
  intro G _ _ hK hchar Y V hY hVn hVe hYV hP
  have := hVn
  obtain ⟨P, hP2, hPC, hYN, hs⟩ := hP
  have hV : IsElemAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hVe
  obtain ⟨hVY, hU, hQU, hCY⟩ := emb_stage_one hchar hVe hY hYV hYN hs
  obtain ⟨-, hTG, hTne, hT2, hYc, hYs, -⟩ :=
    emb_hyp_data (kProper_of_isKGroup' hK) hV hY hP2 hPC hYN hs hU
  have hKp : CFSG.IsKGroup ↥(autOn (⊤ : Subgroup G) V) :=
    isKGroup_of_surjective hK (ambRhoHat V) (ambRhoHat_surjective V)
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV.2 v v.2)
  have hYU : InClassX ↥(yuHolOf hV (autOn Y V)) := hPlus G V Y hV hY hVY hU
  rcases hY.1.quotient_type with hq | hp
  ·
    have hperf : ⁅Y, Y⁆ = Y := commutator_self_eq_of_isShortGroup hY.1 hq
    have hperf' : ⁅autOn Y V, autOn Y V⁆ = autOn Y V := by
      rw [← map_ambRho V Y, ← Subgroup.map_commutator, hperf]
    obtain ⟨Xh, hYX, hXG, hXs, hout⟩ := @hE.1 ↥V (commGroupOfElemAbelian hV) _ hV2
      (autOn (⊤ : Subgroup G) V) hKp (autOn P V) (autOn Y V) hTG hTne hT2 hYc hYs hperf' hYU
    refine emb_concl hMinus hArrow hOmega hchar hV hY hVY hU hQU hCY Xh hYX hXG hXs ?_
    rcases hout with h | ⟨n, hn, hnat, hh⟩
    · exact Or.inl h
    · exact Or.inr ⟨hperf, n, hn, hnat, hh.imp id (fun h => ⟨h.2.1, h.2.2⟩)⟩
  ·
    have h3 := card_autOn_eq_three hV hY hp hU
    have h4 := card_commOn_eq_four hV hY hp hU
    obtain ⟨Xh, hYX, hXG, hXs, hXhat, harr⟩ := @hE.2 ↥V (commGroupOfElemAbelian hV) _ hV2
      (autOn (⊤ : Subgroup G) V) hKp (autOn P V) (autOn Y V) hTG hTne hT2 hYc hYs h3 h4
    exact emb_concl hMinus hArrow hOmega hchar hV hY hVY hU hQU hCY Xh hYX hXG hXs
      (Or.inl ⟨hXhat, harr⟩)

@[expose] def AschbacherSixTwoKNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.IsKGroup G → IsCharacteristicP 2 G →
    ∀ (Y V : Subgroup G), InClassX ↥Y → V.Normal → IsElementaryAbelian 2 V →
      ¬ Y ≤ Subgroup.centralizer (V : Set G) →
      (∃ P : Subgroup G, IsPGroup 2 P ∧ ¬ P ≤ Subgroup.centralizer (V : Set G) ∧
        Y ≤ Subgroup.normalizer ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer
          ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal) →
      ∀ R : Subgroup G, IsSylowOf 2 R (centralizerModCore Y) →
        (Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ ∨
          (Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
            (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal)) →
        ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ ArrowNat Y X ∧
          (Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → X = ⁅jIn (⊤ : Subgroup G), X⁆) ∧
          (¬ Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ → Y = X)

theorem aschbacherSixTwoKNat_of_inputs (hA : AschbacherEmbeddingAmbK)
    (h28 : AschbacherTwoEight) : AschbacherSixTwoKNat := by
  intro G _ _ hK hchar Y V hY hVn hVe hYV hP R hR h12
  have hV' : CFSG.Open.IsElemAbelian 2 V :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hVe
  have hV2 : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 ↥V
  have hVQ : V ≤ pCore 2 G := le_sSup ⟨hVn, hV2⟩
  have hVC : V ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hVe.toIsMulCommutative
  have hCY : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y := by
    obtain ⟨P, hP2, hPC, hYN, hs⟩ := hP
    exact centralizer_le_centralizerModCore (H := Subgroup.normalizer
        ((P ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) pCore_isPGroup hchar
      (fun N hN hN2 => le_sSup ⟨hN, hN2⟩) hVQ hVC hY.1 hYN
      (le_sup_right.trans Subgroup.le_normalizer) hs
      (fun h => hYV (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact h)))
  obtain ⟨X, hYX, hXs, hCX, hN0, hX⟩ := hA G hK hchar Y V hY hVn hVe hYV hP
  have hNoY := SubTwo.noTwoQuotient_of_oResidualTwo hY.1.residual_eq
  have hYn := inClassX_not_le_oTwoIn hY
  have hYstar : ∀ K : Subgroup G, K ≤ Y → (K.subgroupOf Y).Normal → ¬ K ≤ oTwoIn Y → K = Y :=
    fun K hKY hn hnot => inClassX_eq_of_normal_not_le hY hKY hn hnot
  have hXC : ¬ X ≤ Subgroup.centralizer (V : Set G) := fun h => hYV (hYX.trans h)
  rcases hX with ⟨hXc, hUX, harr⟩ | hΩ'
  · have hNoX := SubTwo.noTwoQuotient_of_oResidualTwo hXc.1.residual_eq
    have hXstar : ∀ K : Subgroup G, K ≤ X → (K.subgroupOf X).Normal → ¬ K ≤ oTwoIn X → K = X :=
      fun K hKX hn hnot => inClassX_eq_of_normal_not_le hXc hKX hn hnot
    rcases hXc.1.quotient_type with hq | hp
    ·
      have hperf := inClassX_commutator_eq_self hXc hq
      have hP' : PerfCtx V Y X :=
        { hYX := hYX, hXs := hXs, hNoY := hNoY, hNoX := hNoX, hperf := hperf, hCX := hCX,
          hN0 := hN0, hOX := hUX.trans hVC, hCY := hCY }
      have hconj : OffConj V Y X := by
        by_cases hEq : Y = X
        · subst hEq
          exact OffConj.of_eq
        · exact offConj_of_arrowNat hV' hP' hXc hY hUX harr
      have hP1 : ∀ A : Subgroup G, IsOffG V A → A ≤ Subgroup.normalizer (X : Set G) :=
        fun A hA => offender_le_normalizer hV' hP' hXc hXC hA
      have hsol := endgame_a hV' hP'.toXCtx hP1 hconj hXstar hYstar hYn hR h12
      exact ⟨X, hYX, hXs, hXc, harr, hsol.1, hsol.2⟩
    ·
      have hEq : Y = X := by
        rcases harr with h | ⟨a, b, φ, F, -, -, -, hU, hYX2, -⟩
        · exact h
        · exact eq_of_prime_top hY.1 hXc.1 hYX (InClassX.not_isPGroup hY) hp hU
      subst hEq
      have hXC' : XCtx V Y Y := XCtx.of_eq hNoY hXs hCY hN0
      refine ⟨Y, le_rfl, hXs, hY, Or.inl rfl, fun h1 => ?_, fun _ => rfl⟩
      exact endgame_prime hYstar hYn (fun _ A hA =>
        normalizes_of_prime_type hchar hV' hY hp hXC' hYV hUX hA) h1
  ·
    obtain ⟨hXC', hP1, hII⟩ :=
      sixTwoOmegaInput_of_twoEight h28 G V Y X hV' hΩ' hYX hXs hCX hN0 hCY hY hYV
    exact absurd (endgame_b hV' hXC' hP1 hII hYn hΩ'.2.2.choose_spec.2.2.2.2 hR h12) id

theorem sixThree_of_VKNat (h : AschbacherSixTwoKNat) {G : Type} [Group G] [Finite G]
    (hK : CFSG.IsKGroup G) (hchar : IsCharacteristicP 2 G) {Y R V : Subgroup G} [V.Normal]
    (hX : InClassX ↥Y) (hRsyl : IsSylowOf 2 R (centralizerModCore Y))
    (hYR : Y ≤ Subgroup.normalizer (R : Set G))
    (hsub : (Y.subgroupOf (Subgroup.normalizer (R : Set G))).IsSubnormal)
    (hdisj : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆ ∨
      (Y ≤ Subgroup.normalizer ((jIn R : Subgroup G) : Set G) ∧
        (Y.subgroupOf (Subgroup.normalizer ((jIn R : Subgroup G) : Set G))).IsSubnormal))
    (hVe : IsElementaryAbelian 2 V) (hnot : ¬ Y ≤ Subgroup.centralizer (V : Set G))
    (hCC : Subgroup.centralizer (V : Set G) ≤ centralizerModCore Y) :
    ∃ X : Subgroup G, Y ≤ X ∧ X.IsSubnormal ∧ InClassX ↥X ∧ ArrowNat Y X ∧
      (X = Y ∨ X = ⁅jIn (⊤ : Subgroup G), X⁆) := by
  have hCY : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (Y : Set G) :=
    fun g hg => (hCC hg).1
  have hsubC := isSubnormal_normalizer_sup hYR hsub hCY
  by_cases hRC : R ≤ Subgroup.centralizer (V : Set G)
  ·
    have hRC' : IsSylowOf 2 R (Subgroup.centralizer (V : Set G)) :=
      isSylowOf_of_le hRsyl hRC hCC
    have hfr : Subgroup.normalizer (R : Set G) ⊔ Subgroup.centralizer (V : Set G) = ⊤ :=
      eq_top_iff.mpr fun g _ => le_normalizer_sup_of_isSylowOf hRC'
        (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top g)
    rw [hfr] at hsubC
    exact ⟨Y, le_rfl, isSubnormal_of_subgroupOf_top hsubC, hX, Or.inl rfl, Or.inl rfl⟩
  ·
    have hRRC : IsSylowOf 2 R (R ⊔ Subgroup.centralizer (V : Set G)) :=
      isSylowOf_of_le hRsyl le_sup_left (sup_le hRsyl.1 hCC)
    have hN : Subgroup.normalizer ((R ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) =
        Subgroup.normalizer (R : Set G) ⊔ Subgroup.centralizer (V : Set G) := by
      refine le_antisymm (fun g hg => ?_) (sup_le ?_ ?_)
      · exact sup_le le_sup_left (sup_le (Subgroup.le_normalizer.trans le_sup_left) le_sup_right)
          (le_normalizer_sup_of_isSylowOf hRRC hg)
      · refine le_trans (le_inf le_rfl ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _)
        rw [Subgroup.normalizer_eq_top (Subgroup.centralizer (V : Set G))]
        exact le_top
      · exact le_sup_right.trans Subgroup.le_normalizer
    have hYN : Y ≤ Subgroup.normalizer
        ((R ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
      rw [hN]
      exact hYR.trans le_sup_left
    have hsub' : (Y.subgroupOf (Subgroup.normalizer
        ((R ⊔ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))).IsSubnormal := by
      rw [hN]
      exact hsubC
    obtain ⟨X, hYX, hXsub, hXX, harrow, h1, h2⟩ := h G hK hchar Y V hX inferInstance hVe hnot
      ⟨R, hRsyl.2.1, hRC, hYN, hsub'⟩ R hRsyl hdisj
    by_cases hJ : Y = ⁅jIn (Subgroup.normalizer (Y : Set G)), Y⁆
    · exact ⟨X, hYX, hXsub, hXX, harrow, Or.inr (h1 hJ)⟩
    · exact ⟨X, hYX, hXsub, hXX, harrow, Or.inl (h2 hJ).symm⟩

theorem aschbacherSixThreeCoreNat_of_sixTwoKNat (h : AschbacherSixTwoKNat) :
    AschbacherSixThreeCoreNat := by
  intro G _ _ hK hchar Y hY
  obtain ⟨hX, hYG⟩ := hY
  have hsh : IsShortGroup ↥Y := hX.1
  have hNo : SubTwo.NoTwoQuotient Y := SubTwo.noTwoQuotient_of_oResidualTwo hsh.residual_eq
  obtain ⟨R, hRsyl, -⟩ := Nine.exists_isSylowOf_ge (K := centralizerModCore Y) (Q := ⊥)
    IsPGroup.of_bot bot_le
  obtain ⟨⟨hYR, hsub⟩, hdisj⟩ := hYG R hRsyl
  have hchar' : Subgroup.centralizer ((pCore 2 G : Subgroup G) : Set G) ≤ pCore 2 G := hchar
  have hmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ pCore 2 G := fun N hN hp =>
    le_sSup ⟨hN, hp⟩
  have hQ2 : IsPGroup 2 (pCore 2 G) := pCore_isPGroup
  have hQR : pCore 2 G ≤ R := normal_le_of_isSylowOf hNo hRsyl hYR hsub hQ2
  have hQC : pCore 2 G ≤ centralizerModCore Y := hQR.trans hRsyl.1
  have hQY : pCore 2 G ≤ Subgroup.normalizer (Y : Set G) := fun g hg => (hQC hg).1
  obtain ⟨hQU, -, hUV, hnot⟩ := step_two hsh hQ2 hchar' hQC
  have hVn : (omegaOneCenterIn (pCore 2 G)).Normal := normal_omegaOneCenterIn (pCore 2 G)
  have hCC : Subgroup.centralizer ((omegaOneCenterIn (pCore 2 G) : Subgroup G) : Set G) ≤
      centralizerModCore Y := step_three hNo hQ2 hchar' hmax hQY (hQU.le.trans hUV)
  obtain ⟨X, hYX, hsubX, hXcl, harrow, -⟩ := sixThree_of_VKNat h hK hchar hX hRsyl hYR hsub hdisj
    (isElementaryAbelian_omegaOneCenterIn (pCore 2 G)) hnot hCC
  exact ⟨X, hYX, hsubX, hXcl, harrow⟩

theorem aschbacherSixThreeCoreNat_of_embeddingK (hE : AschbacherEmbeddingK) :
    AschbacherSixThreeCoreNat :=
  aschbacherSixThreeCoreNat_of_sixTwoKNat (aschbacherSixTwoKNat_of_inputs
    (aschbacherEmbeddingAmbK_of_embedding hE embDictPlus_holds embDictMinus_holds
      embDictArrow_holds embOmega_holds) aschbacherTwoEight_holds)

theorem aschbacherSixThreeCore_of_embeddingK (hE : AschbacherEmbeddingK) :
    AschbacherSixThreeCore :=
  aschbacherSixThreeCore_of_coreNat (aschbacherSixThreeCoreNat_of_embeddingK hE)

end CFSG.CGT.PushingUpLit.CGT6
