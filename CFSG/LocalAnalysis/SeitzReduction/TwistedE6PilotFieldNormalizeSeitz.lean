module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldNormalizeX
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR8Lift
public import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {k K : Type} [Field k]
  [Field K] [Algebra k K]

theorem nonempty_fieldCoverParamX_2E6_of_perfectCore (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : UnitaryPilot.SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 f)
    (hψ : Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc))
    (hcore : ∀ z : Kc, z ∈ perfectCore (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)) ↔
      ∃ (y : graphFixedRootGroup TwistTag.E6 K σ) (_ : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ)
        (hyX : ((e.symm y : L) : G) ∈ centralizer (X : Set G)),
        (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hyX⟩)
    (hdesc : InvolutionDescent (a5LeviTwist (apply_apply_eq hK hσ))
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)))
    (hext : AutExtensionComm
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype
      (a5LeviTwist (apply_apply_eq hK hσ))) :
    Nonempty (FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t X) := by
  have hf : 1 ≤ f := by omega
  obtain ⟨-, hDXc, hDq, -, -⟩ :=
    (neighbour_data_2E6_X hset hf2 hk hK hσ e htC ht hX hDe).2
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, -, q, hq, hqker, -, hqapp⟩ := exists_surjective_neighbourCore_2E6_X hset hf2 hk hK
    hσ e htC ht hX htX hDe hKc hDK hsN hov
  have hmemD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ D := fun y hy => by
    rw [hDe]
    exact ⟨e.symm y, ⟨y, mem_subgroupOf.2 hy, rfl⟩, rfl⟩
  have hDX : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ centralizer (X : Set G) :=
    fun y hy => hDXc (hmemD y hy)
  have hDE : D ≤ centralizerPerfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDXc (Subgroup.isPerfect_iff.mp hDq.1)
  have hD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ centralizerPerfectCore X :=
    fun y hy => hDE (hmemD y hy)
  have hDK' : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩ ∈ Kc :=
    fun y hy => hDK ⟨⟨_, hDX y hy⟩, mem_subgroupOf.2 (hmemD y hy), rfl⟩
  have hDne : ∃ (y : graphFixedRootGroup TwistTag.E6 K σ)
      (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply ne_bot_of_isQuasisimple hcomp.2.2
    rw [eq_bot_iff]
    rintro _ ⟨⟨d, hdX⟩, hd, rfl⟩
    have hd' : d ∈ D := mem_subgroupOf.1 hd
    rw [hDe] at hd'
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hd'
    exact (hall y (mem_subgroupOf.1 hy)).symm ▸ Subgroup.one_mem _
  have hcore' : ∀ z : Kc, z ∈ perfectCore (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)) ↔
      ∃ (y : graphFixedRootGroup TwistTag.E6 K σ) (hy : (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ),
        (z : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨((e.symm y : L) : G), hDX y hy⟩ :=
    fun z => (hcore z).trans ⟨fun ⟨y, hy, _, h⟩ => ⟨y, hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hy, hDX y hy, h⟩⟩
  obtain ⟨Ψ, hΨ1, hΨ3⟩ := exists_normalized_a5Levi_mulEquiv (G := G) hf hk hK hσ e htX ht hDX
    hDK' hDne hsN hcore' hψ hdesc hext
  exact nonempty_fieldCoverParamX_of_normalized hf hK hσ _ e htX hD hsN hq hqker hqapp Ψ
    (fun y hy => hΨ1 y hy) hΨ3

theorem nonempty_fieldCoverParamX_2E6 (hset : SeitzSetting G L) (hf2 : 2 ≤ f)
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = (((E6GraphLevi.thetaTorus (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G} (hDe : D = (((su6Levi σ).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hov : UnitaryPilot.SUmOvergroup Kc (Kc.normalizerMonoidHom ⟨_, hsN⟩) 6 f)
    (hψ : Nonempty (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ≃* Kc))
    (hdesc : InvolutionDescentComp (a5LeviTwist (apply_apply_eq hK hσ))
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)))
    (hext : AutExtensionComm
      ((su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)).subtype
      (a5LeviTwist (apply_apply_eq hK hσ))) :
    Nonempty (FieldCoverParamX σ (E6GraphLevi.two_eq_zero_of_card_sq (by omega) hK) e t X) := by
  have hf : 1 ≤ f := by omega
  obtain ⟨-, hDXc, hDq, -, -⟩ :=
    (neighbour_data_2E6_X hset hf2 hk hK hσ e htC ht hX hDe).2
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_2E6_X hset hf2 hk hK hσ e htC ht hX htX hDe
  obtain ⟨-, -, q, hq, hqker, -, hqapp⟩ := exists_surjective_neighbourCore_2E6_X hset hf2 hk hK
    hσ e htC ht hX htX hDe hKc hDK hsN hov
  have hmemD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ D := fun y hy => by
    rw [hDe]
    exact ⟨e.symm y, ⟨y, mem_subgroupOf.2 hy, rfl⟩, rfl⟩
  have hDE : D ≤ centralizerPerfectCore X :=
    CFSG.Quasithin.le_perfectCore_of_perfect hDXc (Subgroup.isPerfect_iff.mp hDq.1)
  have hD : ∀ y : graphFixedRootGroup TwistTag.E6 K σ,
      (y : ModGL TwistTag.E6.tag K) ∈ su6Levi σ → ((e.symm y : L) : G) ∈ centralizerPerfectCore X :=
    fun y hy => hDE (hmemD y hy)
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
    (CFSG.SeitzReduction.CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK)
  obtain ⟨Ψ, hΨ1, hΨ3⟩ := exists_normalized_a5Levi_mulEquiv_of_comp (G := G) hf hk hK hσ e htX
    ht hDe hDXc hDt hDK hsN hDcomp hψ hdesc hext
  exact nonempty_fieldCoverParamX_of_normalized hf hK hσ _ e htX hD hsN hq hqker hqapp Ψ
    (fun y hy => hΨ1 y hy _) hΨ3

end CFSG.SeitzReduction.TwistedE6Pilot
