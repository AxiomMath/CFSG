module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalize
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotBLiftY
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitClassical
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Generic

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

theorem exists_normalized_model_mulEquiv_of_comp [Finite K]
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {X : Subgroup G}
    (htX : t ∈ centralizer (X : Set G)) (ht2 : orderOf t = 2)
    {M DM : Subgroup (ModGL TwistTag.E6.tag K)} (hDMM : DM ≤ M)
    (hDMC : DM ≤ graphFixedRootGroup TwistTag.E6 K σ) (hsimple : IsSimpleGroup DM)
    {β₀ : MulAut M} (hfix : fixedSubgroup β₀ = DM.subgroupOf M) {D : Subgroup G}
    (hDe : D = ((DM.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype)
    (hDX : D ≤ centralizer (X : Set G)) (hDt : D ≤ centralizer ({t} : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hDcomp : CFSG.IsComponent ((((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc).subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))))
    (hψ : Nonempty (M ≃* Kc)) (hdesc : InvolutionDescentComp β₀ (DM.subgroupOf M))
    (hext : AutExtensionComm (DM.subgroupOf M).subtype β₀) :
    ∃ Ψ : M ≃* Kc,
      (∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ DM)
        (hyX : ((e.symm y : L) : G) ∈ centralizer (X : Set G)),
        (Ψ ⟨y, hDMM hy⟩ : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hyX⟩) ∧
      ∀ x, Ψ (β₀ x) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (Ψ x) := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  obtain ⟨ψ₀⟩ := hψ
  set A := DM.subgroupOf M with hAdef
  set π := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) with hπ
  set Db := (D.subgroupOf (centralizer (X : Set G))).map π with hDbdef
  set θ := Kc.normalizerMonoidHom ⟨_, hsN⟩ with hθdef
  have htt : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : θ * θ = 1 := by
    have hs : π ⟨t, htX⟩ * π ⟨t, htX⟩ = 1 := by
      rw [← map_mul, show (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 from
        Subtype.ext htt, map_one]
    rw [hθdef, ← map_mul, show (⟨π ⟨t, htX⟩, hsN⟩ : normalizer (Kc : Set _)) * ⟨_, hsN⟩ = 1 from
      Subtype.ext hs, map_one]
  have hyC : ∀ x : A, ((x : M) : ModGL TwistTag.E6.tag K) ∈ graphFixedRootGroup TwistTag.E6 K σ :=
    fun x => hDMC (mem_subgroupOf.1 x.2)
  let κ : A →* graphFixedRootGroup TwistTag.E6 K σ :=
    { toFun := fun x => ⟨((x : M) : ModGL TwistTag.E6.tag K), hyC x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hmemD : ∀ x : A, ((e.symm (κ x) : L) : G) ∈ D := fun x => by
    rw [hDe]
    exact ⟨e.symm (κ x), ⟨κ x, mem_subgroupOf.2 (mem_subgroupOf.1 x.2), rfl⟩, rfl⟩
  let ε₁ : A →* centralizer (X : Set G) :=
    (L.subtype.comp (e.symm.toMonoidHom.comp κ)).codRestrict _ fun x => hDX (hmemD x)
  have hε₁D : ∀ x : A, π (ε₁ x) ∈ Db := fun x => ⟨ε₁ x, mem_subgroupOf.2 (hmemD x), rfl⟩
  let ε : A →* Kc := (π.comp ε₁).codRestrict Kc fun x => hDK (hε₁D x)
  have hεrange : ε.range = Db.subgroupOf Kc := by
    ext z
    rw [mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact hε₁D x
    · rintro ⟨⟨d, hdX⟩, hd, hdz⟩
      have hd' : d ∈ D := mem_subgroupOf.1 hd
      rw [hDe] at hd'
      obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hd'
      refine ⟨⟨⟨y, hDMM (mem_subgroupOf.1 hy)⟩, mem_subgroupOf.2 (mem_subgroupOf.1 hy)⟩, ?_⟩
      apply Subtype.ext
      rw [← hdz]
      rfl
  have hsimpleA : IsSimpleGroup A := (subgroupOfEquivOfLe hDMM).isSimpleGroup
  have hε : Function.Injective ε := by
    rcases hsimpleA.eq_bot_or_eq_top_of_normal ε.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ε).1 h
    · exfalso
      have hbot : ε.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, rfl⟩
        exact (MonoidHom.mem_ker.1 (h ▸ mem_top x : x ∈ ε.ker)).symm ▸ one_mem _
      rw [hεrange] at hbot
      have hbot' := (Subgroup.eq_bot_iff_forall _).1 hbot
      have hsub : Subsingleton ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)) :=
        ⟨fun a b => by
          have ha : (a : fixedSubgroup θ) = 1 :=
            Subtype.ext (by simpa using hbot' _ (mem_subgroupOf.1 a.2))
          have hb : (b : fixedSubgroup θ) = 1 :=
            Subtype.ext (by simpa using hbot' _ (mem_subgroupOf.1 b.2))
          exact Subtype.ext (ha.trans hb.symm)⟩
      have hns := hDcomp.1.2.1.toNontrivial
      have hss : Subsingleton (((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)) ⧸
          center ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ))) :=
        (QuotientGroup.mk'_surjective _).subsingleton
      exact false_of_nontrivial_of_subsingleton (((Db.subgroupOf Kc).subgroupOf
        (fixedSubgroup θ)) ⧸ center ((Db.subgroupOf Kc).subgroupOf (fixedSubgroup θ)))
  have hεθ : ε.range ≤ fixedSubgroup θ := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    change π ⟨t, htX⟩ * π (ε₁ x) * (π ⟨t, htX⟩)⁻¹ = π (ε₁ x)
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hc := mem_centralizer_singleton_iff.1 (hDt (hmemD x))
    change t * ((e.symm (κ x) : L) : G) * t⁻¹ = ((e.symm (κ x) : L) : G)
    rw [← hc, mul_inv_cancel_right]
  have hεC : CFSG.IsComponent (ε.range.subgroupOf (fixedSubgroup θ)) := by
    rw [hεrange]
    exact hDcomp
  have hj₀ : A.subtype.range = fixedSubgroup β₀ := by rw [range_subtype, hfix]
  obtain ⟨Ψ, hΨj, hΨβ⟩ := exists_normalized_mulEquiv_of_fix_eq A.subtype_injective hj₀ hdesc hext
    ψ₀ hθθ hε hεθ hεC
  refine ⟨Ψ, fun y hy hyX => ?_, hΨβ⟩
  have h1 := hΨj ⟨⟨y, hDMM hy⟩, mem_subgroupOf.2 hy⟩
  have h2 := congrArg (fun z : Kc => (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))
    h1
  exact h2

end Generic

section Bijective

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

theorem nonempty_fieldNeighbourIso2E6_of_bijective (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    {t : G} {X : Subgroup G} (htX : t ∈ centralizer (X : Set G))
    {M DM : Subgroup (ModGL TwistTag.E6.tag K)} (hDMM : DM ≤ M) {β₀ : MulAut M}
    (hD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ, (y : ModGL TwistTag.E6.tag K) ∈ DM →
      ((e.symm y : L) : G) ∈ centralizerPerfectCore X)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    {q : centralizerPerfectCore X →* Kc} (hqbij : Function.Bijective q)
    (hqapp : ∀ y : centralizerPerfectCore X, (q y : centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))) = QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨(y : G), F4Pilot.centralizerPerfectCore_le_centralizer X y.2⟩)
    (Ψ : M ≃* Kc)
    (hΨ1 : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ DM)
      (hyX : ((e.symm y : L) : G) ∈ centralizer (X : Set G)),
      (Ψ ⟨y, hDMM hy⟩ : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hyX⟩)
    (hΨ3 : ∀ x, Ψ (β₀ x) = Kc.normalizerMonoidHom ⟨_, hsN⟩ (Ψ x)) :
    Nonempty (FieldNeighbourIso2E6 e t X M β₀ DM) := by
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X
      (Subgroup.centralizer_le_normalizer _ htX)
  set qe := MulEquiv.ofBijective q hqbij with hqe
  have hqt : ∀ z : centralizerPerfectCore X,
      q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ z) =
        Kc.normalizerMonoidHom ⟨_, hsN⟩ (q z) := by
    intro z
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hqapp, hqapp]
    have e1 : (⟨(((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ z :
        centralizerPerfectCore X) : G), F4Pilot.centralizerPerfectCore_le_centralizer X
          ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ z).2⟩ :
            centralizer (X : Set G)) =
        ⟨t, htX⟩ * ⟨(z : G), F4Pilot.centralizerPerfectCore_le_centralizer X z.2⟩ *
          ⟨t, htX⟩⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rfl
    rw [e1, map_mul, map_mul, map_inv]
  refine ⟨⟨Ψ.trans qe.symm, fun y hyD hyM => ?_, fun x => ?_⟩⟩
  · have h1 : q ⟨((e.symm y : L) : G), hD y hyD⟩ = Ψ ⟨y, hyM⟩ := Subtype.ext (by
      rw [hqapp, ← hΨ1 y hyD])
    have h2 : qe.symm (Ψ ⟨y, hyM⟩) = ⟨((e.symm y : L) : G), hD y hyD⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    change ((qe.symm (Ψ ⟨y, hyM⟩) : centralizerPerfectCore X) : G) = _
    rw [h2]
  · have h1 : qe.symm (Ψ (β₀ x)) =
        (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ (qe.symm (Ψ x)) := by
      rw [MulEquiv.symm_apply_eq, hΨ3]
      change _ = q ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ (qe.symm (Ψ x)))
      rw [hqt]
      congr 1
      exact (qe.apply_symm_apply (Ψ x)).symm
    change ((qe.symm (Ψ (β₀ x)) : centralizerPerfectCore X) : G) =
      t * ((qe.symm (Ψ x) : centralizerPerfectCore X) : G) * t⁻¹
    rw [h1, Subgroup.normalizerMonoidHom_apply_apply_coe]

end Bijective

section LeafInputs

open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem nonempty_fieldNeighbourIso2E6_Y_of_leafInputs (hGLS : GLS3OddLieAutComponentsInput)
    (hXodd : OmegaNotOddLieInputAt 4) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((shortRootTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((omegaMinusLevi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDKc : ⁅(D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc)
    (hdesc : InvolutionDescentComp (d4LeviTwist (apply_apply_eq hK hσ))
      ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)))
    (hext : AutExtensionComm
      ((omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD)).subtype
      (d4LeviTwist (apply_apply_eq hK hσ))) :
    Nonempty (FieldNeighbourIso2E6 e t X (subsystemGroup TwistTag.E6.tag K setD)
      (d4LeviTwist (apply_apply_eq hK hσ)) (omegaMinusLevi σ)) := by
  have hf : 1 ≤ f := by omega
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  obtain ⟨-, hmodel, -, -, q, hq, hqker, hqodd, hqapp⟩ :=
    neighbourCore_field_2E6_Y_of_leafInputs hGLS hXodd hMinn hMcomp hset hf2 hk hK hσ e htC ht hX
      htX hDe hKc hDKc hKt
  obtain ⟨⟨_, -, hall, -⟩, -⟩ := exists_isComponent_2E6_Y_of_leafInputs hGLS hXodd hMinn hMcomp
    hset hf2 hk hK hσ e htC ht hX hDe
  obtain ⟨-, ⟨-, hDK, -, hsN, -⟩ | ⟨hne, -⟩⟩ := hall Kc hKc hDKc
  swap
  · exact absurd hKt hne
  have : Group.IsPerfect (centralizerPerfectCore X) :=
    Subgroup.isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
  have hqinj : Function.Injective q :=
    SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel _ inferInstance q hq hqker hqodd
  have hψ : Nonempty (subsystemGroup TwistTag.E6.tag K setD ≃* Kc) := by
    have hd4 : LieModel (d4Levi K) .POmegaPlus 4 2 (2 * f) :=
      lieModel_d4Levi (K := K) (by omega) (by rw [hK, ← pow_mul, mul_comm])
    rcases hd4 with ⟨-, hcl₁⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · rcases hmodel with ⟨-, hcl₂⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · exact CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hcl₁ hcl₂
      all_goals exact absurd h0 (by norm_num)
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_Y hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, -, hDXc, hDq, -, -⟩ := neighbour_data_2E6_Y hset hf2 hk hK hσ e htC ht hX hDe
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd => by
    rw [hDe] at hd
    exact mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hDs := hcomp.1
  have hDc : CFSG.IsComponent (((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := F4Pilot.isComponent_subgroupOf_subgroupOf
    (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN)
    (CFSG.SeitzReduction.CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc
      hDK.le)
  have hle : omegaMinusLevi σ ≤ subsystemGroup TwistTag.E6.tag K setD := inf_le_left
  obtain ⟨Ψ, hΨ1, hΨ3⟩ := exists_normalized_model_mulEquiv_of_comp e htX ht hle
    (omegaMinusLevi_le_graphFixedRootGroup σ) (isSimpleGroup_omegaMinusLevi hf hK hσ)
    (fixedSubgroup_d4LeviTwist hf hK hσ) hDe hDXc hDt hDK.le hsN hDcomp hψ hdesc hext
  have hmemD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ omegaMinusLevi σ → ((e.symm y : L) : G) ∈ D := fun y hy => by
    rw [hDe]
    exact ⟨e.symm y, ⟨y, mem_subgroupOf.2 hy, rfl⟩, rfl⟩
  have hDE : D ≤ centralizerPerfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDXc (Subgroup.isPerfect_iff.mp hDq.1)
  exact nonempty_fieldNeighbourIso2E6_of_bijective e htX hle (fun y hy => hDE (hmemD y hy)) hsN
    ⟨hqinj, hq⟩ hqapp Ψ hΨ1 hΨ3

end LeafInputs

end CFSG.SeitzReduction.TwistedE6Pilot
