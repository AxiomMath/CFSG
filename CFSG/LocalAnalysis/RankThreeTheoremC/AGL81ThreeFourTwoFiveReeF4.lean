module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.CGT.T75P.SylowSplit
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.HardMathSupport.Malle.Coordinator.KFactReeF4LocalProof
import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreInternal
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoFiveBase
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
public import CFSG.LieType.Ree.LargeReeModelSchreier

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

open CFSG.LieType.Ree.ReeTag (F4)

open CFSG.LieType.Chevalley (fixSubfield)



private theorem reeF4_simple {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2) {A : Type}
    [Group A] (e : A ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Finite A ∧ IsSimpleGroup A ∧ (∃ a b : A, a * b ≠ b * a) ∧ Group.IsSolvable (Outer A) := by
  obtain ⟨F, _, _, _, hF, ⟨eΓ⟩⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_reeGamma_model hd ⟨e⟩
  haveI : Finite (F4.reeGamma F 2) := Subtype.finite
  haveI : Finite A := Finite.of_equiv _ eΓ.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.AGLEmbedding.CatGroup d) :=
    CFSG.AGLEmbedding.isSimpleGroup_of_catGroup_reeF4 hd
  haveI hs : IsSimpleGroup A := e.isSimpleGroup
  have h25 : 5 ^ 2 ∣ Nat.card A := by
    rw [Nat.card_congr e.toEquiv, CFSG.AGLEmbedding.card_catGroup_reeF4 hd]
    norm_num [CFSG.Open.ordTwistedF4]
  refine ⟨inferInstance, hs, CFSG.AGLEmbedding.nonabelian_of_simple_of_sq_dvd Nat.prime_five h25,
    ?_⟩
  have hO : Nat.card (Outer A) ∣ 5 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eΓ).toEquiv]
    exact (CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hF).2
  haveI : Finite (Outer A) := Nat.finite_of_card_ne_zero fun h => by
    rw [h] at hO
    norm_num at hO
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hP : IsPGroup 5 (Outer A) := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hO with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [h]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [h]; norm_num)
  haveI := hP.isNilpotent
  infer_instance

private theorem le_of_forall_centralizer_le_reeF4 {Y : Type} [Group Y] [Finite Y]
    {K Y₀ Z : Subgroup Y} {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2)
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZK : Z ≤ K) (hZ : CFSG.Open.IsElemAbelian 5 Z)
    (hZc : Nat.card Z = 5 ^ 2) (h : ∀ x ∈ Z, x ≠ 1 → ∀ k ∈ K, k * x = x * k → k ∈ Y₀) :
    K ≤ Y₀ := by
  have hgen := CFSG.HardMathSupport.Malle.LocalAction.reeF4_generation hd ⟨e⟩ (Z.subgroupOf K)
    (CFSG.Open.IsElemAbelian.comap hZ K.subtype_injective)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv, hZc])
  have hle : Subgroup.closure {k : K | ∃ x ∈ Z.subgroupOf K, x ≠ 1 ∧ k * x = x * k} ≤
      Y₀.subgroupOf K := by
    rw [Subgroup.closure_le]
    rintro k ⟨x, hx, hx1, hkx⟩
    exact Subgroup.mem_subgroupOf.mpr (h x hx (fun h1 => hx1 (Subtype.ext h1)) k k.2
      (congrArg Subtype.val hkx))
  rw [hgen] at hle
  exact Subgroup.subgroupOf_eq_top.mp (eq_top_iff.mpr hle)

private theorem exists_elemAbelian_of_ne_top {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    [K.Normal] (d : TauCeti.ValidLieTypeIndex) (hd : CFSG.AGLEmbedding.IsReeFFourFiveIndex d)
    (e : Nonempty (K ≃* CFSG.AGLEmbedding.CatGroup d)) (hC : centralizer (K : Set Y) = ⊥)
    (hK : K ≠ ⊤) : ∃ F : Subgroup Y, CFSG.Open.IsElemAbelian 5 F ∧ Nat.card F = 5 ^ 3 := by
  classical
  obtain ⟨e⟩ := e
  have hmodel := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 hd
  have hS := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier (CFSG.AGLEmbedding.CatGroup d) 2
    (2 * 2 + 1) hmodel
  obtain ⟨-, a, hfa, F, _, _, hF, ⟨e'⟩⟩ := hmodel
  have hFc : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have : CharP F F4.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hF
  obtain ⟨eΓ⟩ := hS.2.2.2.2.2 a F hfa hF ⟨e'⟩
  have ha : a = 2 := by omega
  subst ha
  let eK : K ≃* F4.reeGamma F 2 := e.trans eΓ
  have : Finite (F4.reeGamma F 2) := Subtype.finite
  obtain ⟨σ₀, -, hσ₀, -⟩ :=
    CFSG.Semidihedral.FixedFieldData.finite_field_automorphism_fixed_field_cardinality
      2 5 Nat.prime_two (by norm_num) F (by simpa using hFc)
  have hk := (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two
    (by norm_num : 1 ≤ 5) (by simpa using hFc) σ₀).2
  rw [hσ₀] at hk
  have hk1 : Nat.card (fixSubfield σ₀) = 2 ^ 1 := by simpa using hk
  obtain ⟨-, hnf⟩ := CFSG.RankThree.PartTwo.KFacts.largeRee_automorphism_normal_form
    (a := 2) (K := F) (by norm_num) hFc
  have hinj : Function.Injective (F4.reeGammaFieldAutHom F 2) := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    refine hnf β ⟨1, ?_⟩
    rw [← F4.reeGammaFieldAutHom_apply, hβ, map_one]
  set τ : MulAut (F4.reeGamma F 2) := F4.reeGammaFieldAut F 2 σ₀ with hτdef
  have hτ : orderOf τ = 5 := by
    rw [hτdef, ← F4.reeGammaFieldAutHom_apply]
    exact (orderOf_injective _ hinj σ₀).trans hσ₀
  have hni : τ ∉ inner (F4.reeGamma F 2) := by
    intro h
    have h1 := hnf σ₀ h
    rw [h1, orderOf_one] at hσ₀
    omega
  have hOut : Nat.card (Outer (F4.reeGamma F 2)) ∣ 5 :=
    (CFSG.AGLEmbedding.outer_reeGamma (a := 2) (K := F) (by norm_num) hFc).2
  obtain ⟨-, σ, hσK, hσ5, hact⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_sigma_of_outer K eK hC hK hOut τ hτ hni
  have hcentK : ∀ k : K, τ (eK k) = eK k → (k : Y) * σ = σ * (k : Y) := by
    intro k hk
    have hk' : σ * k * σ⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance (k : Y) k.2 σ
    have h2 := hact k k.2 hk'
    rw [hk] at h2
    have h3 : σ * k * σ⁻¹ = k := congrArg Subtype.val (eK.injective h2)
    calc (k : Y) * σ = (σ * k * σ⁻¹) * σ := by rw [h3]
      _ = σ * k := by group
  obtain ⟨E', hE', hcard', hfixE'⟩ :=
    CFSG.HardMathSupport.Malle.LocalAction.exists_plane_fixed_reeGamma σ₀ hk1
  let f : F4.reeGamma F 2 →* Y := K.subtype.comp eK.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp eK.symm.injective
  have hfK : E'.map f ≤ K := by
    rintro _ ⟨γ, -, rfl⟩
    exact (eK.symm γ).2
  have hcomm : ∀ a ∈ E'.map f, ∀ b ∈ zpowers σ, a * b = b * a := by
    rintro _ ⟨γ, hγ, rfl⟩ b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have h1 : f γ * σ = σ * f γ := by
      refine hcentK (eK.symm γ) ?_
      rw [MulEquiv.apply_symm_apply]
      exact hfixE' γ hγ
    exact (Commute.zpow_right h1 j).eq
  have hσbot : zpowers σ ⊓ K = ⊥ := by
    have hdvd : Nat.card (zpowers σ ⊓ K : Subgroup Y) ∣ 5 := by
      rw [← hσ5, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq : zpowers σ ⊓ K = zpowers σ :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hσ5, h5])
      exact hσK ((heq ▸ inf_le_right : zpowers σ ≤ K) (Subgroup.mem_zpowers σ))
  have hinf : E'.map f ⊓ zpowers σ = ⊥ := by
    rw [eq_bot_iff, ← hσbot]
    exact fun x hx => ⟨hx.2, hfK hx.1⟩
  refine ⟨E'.map f ⊔ zpowers σ,
    (CFSG.SectionRank.isElemAbelian_map hE' f).sup_of_commute
      (CFSG.Open.isElemAbelian_zpowers (hσ5 ▸ pow_orderOf_eq_one σ)) hcomm, ?_⟩
  rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, Subgroup.card_map_of_injective hf, hcard',
    Nat.card_zpowers, hσ5]
  norm_num

theorem threeFourTwoNoneAt_reeF4 {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .reeF4 2) :
    ThreeFourTwoNoneAt 5 (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨-, hX1, hX2, hX3⟩ := reeF4_simple hd (MulEquiv.refl _)
  refine threeFourTwoNoneAt_of_inf hX1 hX2 hX3 ?_
  intro Y _ _ K Y₀ E R _ _ hKn hKX _ _ _ hER hE hEc hcore _ hKY
  haveI := hKn
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := hKX
  obtain ⟨-, hKs, hKnab, -⟩ := reeF4_simple hd e
  have hZK : center K = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot K hKnab
  obtain ⟨T', hT'⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  set T : Subgroup Y := (R : Subgroup Y) ⊓ K with hTdef
  set C : Subgroup Y := centralizer (K : Set Y) with hCdef
  have hKC : K ⊓ C = ⊥ := inf_centralizer_self_eq_bot_of_center hZK
  have hTR : T ≤ R := inf_le_left
  have hTK : T ≤ K := inf_le_right
  by_cases hRC : (R : Subgroup Y) ⊓ C = ⊥
  · set H : Subgroup Y := K ⊔ (R : Subgroup Y) with hHdef
    have hY'C := centralizer_subgroupOf_sup_sylow_eq_bot R hKC hRC
    have eH : K.subgroupOf H ≃* CFSG.AGLEmbedding.CatGroup d :=
      (Subgroup.subgroupOfEquivOfLe le_sup_left).trans e
    by_cases h3 : 3 ≤ CFSG.pRank 5 (R : Subgroup Y)
    ·
      rw [if_pos h3] at hcore
      left
      have h3' : 3 ≤ CFSG.Open.pRank 5 ((R.subtype le_sup_right : Sylow 5 H) : Subgroup H) := by
        rw [Sylow.coe_subtype, CFSG.LargeEvenClassification.Helpers.pRank_subgroupOf
          (by norm_num) _ _ le_sup_right, ← CFSG.SectionRank.pRank_coe_eq_openPRank]
        exact h3
      have hcore' : CFSG.Open.GLBWeakCore 5 ((R.subtype le_sup_right : Sylow 5 H) : Subgroup H) ≤
          Y₀.subgroupOf H := by
        rw [Sylow.coe_subtype]
        exact glbWeakCore_subgroupOf_le_subgroupOf (by norm_num) le_sup_right hcore
      have hne : Y₀.subgroupOf H ≠ ⊤ := fun htop =>
        hKY ((le_sup_left : K ≤ H).trans (Subgroup.subgroupOf_eq_top.mp htop))
      obtain ⟨hsitu, -⟩ := CFSG.HardMathSupport.Malle.Coordinator.kFactReeF4Local_of_certs ↥H
        (K.subgroupOf H) d hd inferInstance ⟨eH⟩ hY'C (R.subtype le_sup_right) (Y₀.subgroupOf H)
        h3' hcore' hne
      exact isSolvable_inf_of_isSolvable_subgroupOf le_sup_left hsitu.solvable
    ·
      exfalso
      rw [if_neg h3] at hcore
      have hRK : (R : Subgroup Y) ≤ K := by
        by_contra hRK
        have hne : K.subgroupOf H ≠ ⊤ := fun htop =>
          hRK ((le_sup_right : (R : Subgroup Y) ≤ H).trans (Subgroup.subgroupOf_eq_top.mp htop))
        obtain ⟨F, hF, hFc⟩ := exists_elemAbelian_of_ne_top (K.subgroupOf H) d hd ⟨eH⟩ hY'C hne
        apply h3
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank,
          CFSG.LargeEvenClassification.Helpers.pRank_sylow_eq_ambient Nat.prime_five R]
        exact CFSG.SectionRank.le_pRank (by norm_num) le_top
          (CFSG.SectionRank.isElemAbelian_map hF H.subtype)
          (by rw [Subgroup.card_map_of_injective H.subtype_injective, hFc])
      refine hKY (le_of_forall_centralizer_le_reeF4 hd e (hER.trans hRK) hE hEc ?_)
      intro x hx hx1 k _ hkx
      refine hcore (normalizer_zpowers_le_glbCoreOne (by norm_num) hx
        (orderOf_eq_prime (hE.2 x hx) hx1) ?_)
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hkx j).symm.eq
  ·
    exfalso
    obtain ⟨c, hcRC, hc5, -⟩ := exists_orderOf_eq_mem_center_of_le_sylow R.isPGroup'
      inf_le_left (self_le_normalizer_inf_normal (N := C)) hRC
    have hcC : c ∈ C := (Subgroup.mem_inf.mp hcRC).2
    have hcR : c ∈ (R : Subgroup Y) := (Subgroup.mem_inf.mp hcRC).1
    have hcE : CFSG.Open.IsElemAbelian 5 (zpowers c) :=
      CFSG.Open.isElemAbelian_zpowers (hc5 ▸ pow_orderOf_eq_one c)
    have hcc : Nat.card (zpowers c) = 5 ^ 1 := by rw [Nat.card_zpowers, hc5, pow_one]
    obtain ⟨Z', -, -, hZ'P, hZ'e, hZ'c⟩ := CFSG.HardMathSupport.Malle.LocalAction.exists_omega_one
      (CFSG.HardMathSupport.Malle.LocalAction.sylowShape_five_of_catGroup hd ⟨e⟩) T'
    set Z : Subgroup Y := Z'.map K.subtype with hZdef
    have hZT : Z ≤ T := by
      rw [← hT']
      exact Subgroup.map_mono hZ'P
    have hZK : Z ≤ K := hZT.trans hTK
    have hZe : CFSG.Open.IsElemAbelian 5 Z := CFSG.SectionRank.isElemAbelian_map hZ'e K.subtype
    have hZc : Nat.card Z = 5 ^ 2 := by
      rw [hZdef, Subgroup.card_map_of_injective K.subtype_injective, hZ'c]
    have hKc : ∀ a ∈ K, ∀ b ∈ zpowers c, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.mp ((zpowers_le.mpr hcC) hb) a ha
    have hKcbot : ∀ A : Subgroup Y, A ≤ K → A ⊓ zpowers c = ⊥ := by
      intro A hA
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ K ⊓ C := ⟨hA hx.1, (zpowers_le.mpr hcC) hx.2⟩
      rwa [hKC] at hx'
    have h3 : 3 ≤ CFSG.pRank 5 (R : Subgroup Y) := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact le_openPRank_sup_of_commute (by norm_num) hZe hcE (fun a ha => hKc a (hZK ha))
        (hKcbot Z hZK) hZc hcc (sup_le (hZT.trans hTR) (zpowers_le.mpr hcR))
    rw [if_pos h3] at hcore
    refine hKY (le_of_forall_centralizer_le_reeF4 hd e hZK hZe hZc ?_)
    intro x hx hx1 k hk hkx
    have hxK : x ∈ K := hZK hx
    have hx5 : orderOf x = 5 := orderOf_eq_prime (hZe.2 x hx) hx1
    have hXR : zpowers x ⊔ zpowers c ≤ (R : Subgroup Y) :=
      sup_le (zpowers_le.mpr (hTR (hZT hx))) (zpowers_le.mpr hcR)
    have h2X : 1 + 1 ≤ CFSG.Open.pRank 5 (zpowers x ⊔ zpowers c) :=
      le_openPRank_sup_of_commute (by norm_num)
        (CFSG.Open.isElemAbelian_zpowers (hx5 ▸ pow_orderOf_eq_one x)) hcE
        (fun a ha => hKc a ((zpowers_le.mpr hxK) ha)) (hKcbot _ (zpowers_le.mpr hxK))
        (by rw [Nat.card_zpowers, hx5, pow_one]) hcc le_rfl
    have hZX :
        Z ≤ (R : Subgroup Y) ⊓ centralizer ((zpowers x ⊔ zpowers c : Subgroup Y) : Set Y) := by
      refine le_inf (hZT.trans hTR) ?_
      rw [Subgroup.le_centralizer_iff]
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh => hZe.comm hh hx
      · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
          Subgroup.mem_centralizer_iff.mp hcC h (hZK hh)
    have h3X : 2 + 1 ≤ CFSG.Open.pRank 5 ((zpowers x ⊔ zpowers c) ⊔
        ((R : Subgroup Y) ⊓ centralizer ((zpowers x ⊔ zpowers c : Subgroup Y) : Set Y))) :=
      le_openPRank_sup_of_commute (by norm_num) hZe hcE (fun a ha => hKc a (hZK ha))
        (hKcbot Z hZK) hZc hcc (sup_le (hZX.trans le_sup_right) (le_sup_right.trans le_sup_left))
    have hNX := (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 5 hXR h2X
      h3X).trans hcore
    refine hNX (Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨?_, ?_⟩)
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hkx j).symm.eq
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro h hh
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hcC k hk) j).symm.eq

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
