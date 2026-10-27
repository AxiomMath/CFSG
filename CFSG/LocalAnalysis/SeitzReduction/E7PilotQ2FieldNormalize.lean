module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2FieldLift
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2SwapMain
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Fixed


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

theorem eqLocus_leviEntrywiseEquiv_high_of_charTwo :
    (leviEntrywiseEquiv σ .high).toMonoidHom.eqLocus (MonoidHom.id _) =
      (leviInclusion σ .high).range := by
  have : CharP (fixSubfield σ) 2 := (fixSubfield σ).subtype.charP Subtype.val_injective 2
  set ι := (fixSubfield σ).subtype with hι
  ext d
  constructor
  · intro hd
    have hd' : leviEntrywiseEquiv σ .high d = d := hd
    have hfixC : (d : adjointGroup .E7 K) ∈
        (entrywiseAdjointAut .E7 σ).toMonoidHom.eqLocus (MonoidHom.id _) := by
      change entrywiseAdjointAut .E7 σ (d : adjointGroup .E7 K) = d
      apply Subtype.ext
      rw [coe_entrywiseAdjointAut]
      have h1 := congrArg (fun z : E7Neighbour.high.levi K => ((z : adjointGroup .E7 K) :
        ModGL .E7 K)) hd'
      simp only [coe_leviEntrywiseEquiv] at h1
      rw [← CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self] at h1
      exact h1
    rw [E8Pilot.eqLocus_entrywiseAdjointAut_E7 ι
      (F4Pilot.apply_eq_iff_mem_range_fixSubfield_subtype σ)] at hfixC
    obtain ⟨g₀, hg₀⟩ := hfixC
    have hg₀d : baseChangeGL ι (g₀ : ModGL .E7 (fixSubfield σ)) =
        ((d : adjointGroup .E7 K) : ModGL .E7 K) := congrArg Subtype.val hg₀
    have hdD : ((d : adjointGroup .E7 K) : ModGL .E7 K) ∈
        rootSpan .E7 K (EPilot.perpRoots .E7) := by
      rw [perpRoots_eq_orthRoots]
      exact mem_subgroupOf.1 d.2
    have hg₀D : (g₀ : ModGL .E7 (fixSubfield σ)) ∈
        rootSpan .E7 (fixSubfield σ) (EPilot.perpRoots .E7) := by
      rw [← adjointGroup_inf_centralizer_highRootSL2_eq_of_charTwo (Or.inr (Or.inl rfl))]
      refine Subgroup.mem_inf.2 ⟨g₀.2, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
      have hjJ := baseChangeGL_mem_highRootSL2_E7 ι hj
      have hdJ := Subgroup.mem_centralizer_iff.1
        (EPilot.rootSpan_perpRoots_le_centralizer_highRootSL2 (K := K)
          (Or.inr (Or.inl rfl)) hdD) _ hjJ
      apply baseChangeGL_injective ι
      rw [map_mul, map_mul, hg₀d]
      exact hdJ
    rw [perpRoots_eq_orthRoots] at hg₀D
    refine ⟨⟨g₀, mem_subgroupOf.2 hg₀D⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [coe_leviInclusion]
    exact hg₀d
  · rintro ⟨x, rfl⟩
    exact leviEntrywiseEquiv_leviInclusion σ .high x

theorem range_leviInclusion_eq_perfectCore_of_charTwo :
    (leviInclusion σ .high).range =
      perfectCore (fixedSubgroup (leviEntrywiseEquiv σ .high)) := by
  have : CharP (fixSubfield σ) 2 := (fixSubfield σ).subtype.charP Subtype.val_injective 2
  have h1 : fixedSubgroup (leviEntrywiseEquiv σ .high) = (leviInclusion σ .high).range :=
    eqLocus_leviEntrywiseEquiv_high_of_charTwo σ
  have hperf : ⁅(leviInclusion σ .high).range, (leviInclusion σ .high).range⁆ =
      (leviInclusion σ .high).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_levi_high (fixSubfield σ)]
  rw [h1, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

theorem normalizationProperty_leviInclusion_high_of_orderOf (hσ : orderOf σ = 2) :
    NormalizationProperty (leviInclusion σ .high) := by
  have : CharP (fixSubfield σ) 2 := (fixSubfield σ).subtype.charP Subtype.val_injective 2
  have := finite_levi K .high
  exact NormalizationProperty.of_mulEquiv (normalizationProperty_incl hσ (by norm_num))
    (leviHighModelEquiv (fixSubfield σ)) (leviHighModelEquiv K) (leviBaseChange_injective _ _)
    (leviEntrywiseEquiv_mul_self hσ) (range_leviInclusion_eq_perfectCore_of_charTwo σ)

end Fixed

section Identification


variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
  {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_mulEquiv_levi_high_nonsplit_E7_eq (hσ : orderOf σ = 2)
    (hset : StandardSetting G L) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (e : L ≃* adjointGroup .E7 (fixSubfield σ))
    {A : Subgroup (adjointGroup .E7 (fixSubfield σ))} (hAJ : A ≤ posJE7 (fixSubfield σ))
    (hA : Nat.card A = Nat.card (fixSubfield σ) + 1) (hcyc : IsCyclic A)
    {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (hψ : Nonempty (E7Neighbour.high.levi K ≃* centralizerPerfectCore X)) :
    ∃ Φ : E7Neighbour.high.levi K ≃* centralizerPerfectCore X,
      ∀ g : E7Neighbour.high.levi (fixSubfield σ),
        ((Φ (leviInclusion σ .high g) : centralizerPerfectCore X) : G) =
          ((e.symm (g : adjointGroup .E7 (fixSubfield σ)) : L) : G) := by
  have : CharP (fixSubfield σ) 2 := (fixSubfield σ).subtype.charP Subtype.val_injective 2
  obtain ⟨ψ₀⟩ := hψ
  have htX : t ∈ centralizer (X : Set G) := by
    rw [hX]
    exact centralizer_le (map_subtype_le _) htC
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore X (centralizer_le_normalizer _ htX)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hθθ : (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ *
      (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (centralizerPerfectCore X : Set G)) * ⟨t, hN⟩ = 1
      from Subtype.ext htt, map_one]
  have hfix := perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_E7 hset htC ht e hAJ hA
    hcyc hX rfl
  set D : Subgroup G := ((EPilot.perpLevi .E7 (fixSubfield σ)).map e.symm.toMonoidHom).map
    L.subtype with hDdef
  have hD : D ≤ centralizerPerfectCore X := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  have hmem : ∀ g : E7Neighbour.high.levi (fixSubfield σ),
      (g : adjointGroup .E7 (fixSubfield σ)) ∈ EPilot.perpLevi .E7 (fixSubfield σ) := fun g => by
    rw [← E7Neighbour.levi_high]
    exact g.2
  set ε₀ : E7Neighbour.high.levi (fixSubfield σ) →* G := L.subtype.comp
    (e.symm.toMonoidHom.comp (E7Neighbour.high.levi (fixSubfield σ)).subtype) with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ centralizerPerfectCore X := fun g => hD ⟨_, ⟨_, hmem g, rfl⟩, rfl⟩
  set ε : E7Neighbour.high.levi (fixSubfield σ) →* centralizerPerfectCore X :=
    ε₀.codRestrict _ hε₀M with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : centralizerPerfectCore X => (z : G)) h
  have hεrange : ε.range.map (centralizerPerfectCore X).subtype = D := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact ⟨_, ⟨_, hmem g', rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      have hx' : x ∈ E7Neighbour.high.levi (fixSubfield σ) := by
        rw [E7Neighbour.levi_high]
        exact hx
      exact ⟨ε ⟨x, hx'⟩, ⟨_, rfl⟩, rfl⟩
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (centralizerPerfectCore X).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, F4Pilot.map_eqLocus_normalizerMonoidHom hN, hfix,
      hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_leviInclusion_high_eq_of_normalization
    (normalizationProperty_leviInclusion_high_of_orderOf σ hσ) ψ₀ hθθ ε hεinj hεr
  exact ⟨ψ', fun g => by rw [hψ' g]; rfl⟩

theorem E7Work.exists_fieldIdentification_nonsplit_two (hσ : orderOf σ = 2)
    (hK : Nat.card K = 4) (e : L ≃* adjointGroup .E7 (fixSubfield σ)) {t : G}
    (hw : E7Work L (fixSubfield σ) t 1) (hF : HR8FieldE7Two e t 1) :
    ∃ A : Subgroup (adjointGroup .E7 (fixSubfield σ)), A ≤ posJE7 (fixSubfield σ) ∧
      Nat.card A = Nat.card (fixSubfield σ) + 1 ∧
      ∃ Φ : E7Neighbour.high.levi K ≃*
          centralizerPerfectCore ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G),
        ∀ g : E7Neighbour.high.levi (fixSubfield σ),
          ((Φ (leviInclusion σ .high g) :
              centralizerPerfectCore ((A.map e.symm.toMonoidHom).map L.subtype : Subgroup G)) :
            G) = ((e.symm (g : adjointGroup .E7 (fixSubfield σ)) : L) : G) := by
  obtain ⟨A, hAJ, hA, htX, Kb, hKb, -, -, hlt, -, hsN, hov⟩ := hF
  have hk2 : Nat.card (fixSubfield σ) = 2 := by rw [hw.card_eq, pow_one]
  have hcyc : IsCyclic A := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (by rw [hA, hk2])
  have hψ := nonempty_levi_high_mulEquiv_centralizerPerfectCore_nonsplit_E7
    hw.standard.standard hw.mem_centralizer hw.orderOf_eq (hw.inf_eq e) hw.card_eq e hAJ hA hcyc
    rfl htX rfl hKb hlt.le hsN hov K (by rw [hK]; norm_num)
  exact ⟨A, hAJ, hA, exists_mulEquiv_levi_high_nonsplit_E7_eq hσ hw.standard hw.mem_centralizer
    hw.orderOf_eq e hAJ hA hcyc rfl hψ⟩

end Identification

end CFSG.SeitzReduction.E7Pilot
