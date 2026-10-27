module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotAlignFieldFamily
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotFieldNormalizeE7

public section

namespace CFSG.SeitzReduction.E7Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open E6Pilot (modelToG mem_modelToG symm_mem_modelToG)

local instance e7PilotFieldNormalizeExistsNeZeroRank : NeZero Tag.E7.rank := ⟨by decide⟩

section Basic

variable (k : Type) [Field k] [Finite k] [CharP k 2]

theorem isQuasisimple_levi_high : CFSG.IsQuasisimple (E7Neighbour.high.levi k) := by
  rw [E7Neighbour.levi_high]
  exact isQuasisimple_perpLevi_E7

theorem commutator_top_levi_high :
    ⁅(⊤ : Subgroup (E7Neighbour.high.levi k)), (⊤ : Subgroup (E7Neighbour.high.levi k))⁆ = ⊤ :=
  (isQuasisimple_levi_high k).1.commutator_eq_top

end Basic

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit
  [CharP K 2] in
theorem leviEntrywiseEquiv_leviInclusion (N : E7Neighbour) (x : N.levi (fixSubfield σ)) :
    leviEntrywiseEquiv σ N (leviInclusion σ N x) = leviInclusion σ N x := by
  refine Subtype.ext (Subtype.ext ?_)
  have hcomp : (σ : K →+* K).comp (fixSubfield σ).subtype = (fixSubfield σ).subtype :=
    RingHom.ext fun c => c.2
  rw [coe_leviEntrywiseEquiv, coe_leviInclusion, F4Pilot.baseChangeGL_baseChangeGL, hcomp]

theorem eqLocus_leviEntrywiseEquiv_high (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    (leviEntrywiseEquiv σ .high).toMonoidHom.eqLocus (MonoidHom.id _) =
      (leviInclusion σ .high).range := by
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
      rw [← EPilot.centralizer_highRootSL2_eq (Or.inr (Or.inl rfl)) hq]
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

end Fixed

section Normalization

variable {K : Type} [Field K] [Finite K] [CharP K 2]

variable {σ : K ≃+* K}

@[expose] def NormalizationProperty {A B : Type} [Group A] [Group B] (j : A →* B) : Prop :=
  ∀ β : MulAut B, β * β = 1 → ∀ ε : A →* B, Function.Injective ε →
    ε.range = perfectCore (fixedSubgroup β) → ∃ ψ : MulAut B, ∀ a, ψ (ε a) = j a

theorem NormalizationProperty.of_mulEquiv {A B A' B' : Type} [Group A] [Group B] [Group A']
    [Group B'] [Finite B] [Finite B'] {j : A →* B} {j' : A' →* B'} (h' : NormalizationProperty j')
    (αA : A ≃* A') (αB : B ≃* B') (hj : Function.Injective j) {β₀ : MulAut B} (hβ₀ : β₀ * β₀ = 1)
    (hj₀ : j.range = perfectCore (fixedSubgroup β₀)) : NormalizationProperty j := by
  have key : ∀ (β : MulAut B), β * β = 1 → ∀ ε : A →* B, Function.Injective ε →
      ε.range = perfectCore (fixedSubgroup β) →
        ∃ ψ : MulAut B', ∀ a, ψ (αB (ε (αA.symm a))) = j' a := by
    intro β hβ ε hε hεr
    have hβ' : MulAut.congr αB β * MulAut.congr αB β = 1 := by rw [← map_mul, hβ, map_one]
    set ε' : A' →* B' := αB.toMonoidHom.comp (ε.comp αA.symm.toMonoidHom) with hε'
    have hε'inj : Function.Injective ε' := αB.injective.comp (hε.comp αA.symm.injective)
    have hε'r : ε'.range = perfectCore (fixedSubgroup (MulAut.congr αB β)) := by
      rw [CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr,
        ← CFSG.Quasithin.map_perfectCore, ← hεr, hε', MonoidHom.range_comp, MonoidHom.range_comp,
        MonoidHom.range_eq_top.2 αA.symm.surjective, ← MonoidHom.range_eq_map]
    exact h' _ hβ' ε' hε'inj hε'r
  intro β hβ ε hε hεr
  obtain ⟨ψ₁, hψ₁⟩ := key β hβ ε hε hεr
  obtain ⟨ψ₂, hψ₂⟩ := key β₀ hβ₀ j hj hj₀
  refine ⟨((αB.trans ψ₁).trans ψ₂.symm).trans αB.symm, fun a => ?_⟩
  have h1 := hψ₁ (αA a)
  have h2 := hψ₂ (αA a)
  rw [MulEquiv.symm_apply_apply] at h1 h2
  simp only [MulEquiv.trans_apply]
  rw [h1, ← h2, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem range_leviInclusion_eq_perfectCore (hq : 4 ≤ Nat.card (fixSubfield σ)) :
    (leviInclusion σ .high).range =
      perfectCore (fixedSubgroup (leviEntrywiseEquiv σ .high)) := by
  have h1 : fixedSubgroup (leviEntrywiseEquiv σ .high) = (leviInclusion σ .high).range :=
    eqLocus_leviEntrywiseEquiv_high σ hq
  have hperf : ⁅(leviInclusion σ .high).range, (leviInclusion σ .high).range⁆ =
      (leviInclusion σ .high).range := by
    rw [MonoidHom.range_eq_map, ← map_commutator, commutator_top_levi_high (fixSubfield σ)]
  rw [h1, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

omit
  [CharP K 2] in
theorem leviEntrywiseEquiv_mul_self (hσ : orderOf σ = 2) :
    leviEntrywiseEquiv σ .high * leviEntrywiseEquiv σ .high = 1 := by
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  refine MulEquiv.ext fun x => Subtype.ext (Subtype.ext ?_)
  change baseChangeGL (σ : K →+* K) (baseChangeGL (σ : K →+* K) ((x : adjointGroup .E7 K) :
    ModGL .E7 K)) = _
  have hc : (σ : K →+* K).comp (σ : K →+* K) = RingHom.id K :=
    RingHom.ext fun c => by
      change (σ * σ) c = c
      rw [hσσ]
      rfl
  rw [F4Pilot.baseChangeGL_baseChangeGL, hc]
  exact CFSG.LieType.Chevalley.baseChangeGL_id K _

omit
  [CharP K 2] in
theorem exists_mulEquiv_leviInclusion_high_eq_of_normalization
    (hnorm : NormalizationProperty (leviInclusion σ .high)) {M : Type} [Group M] [Finite M]
    (ψ : E7Neighbour.high.levi K ≃* M) {θ : MulAut M} (hθ : θ * θ = 1)
    (ε : E7Neighbour.high.levi (fixSubfield σ) →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : E7Neighbour.high.levi K ≃* M, ∀ g, ψ' (leviInclusion σ .high g) = ε g := by
  have := finite_levi K .high
  set β := MulAut.congr ψ.symm θ with hβdef
  have hβ : β * β = 1 := by rw [hβdef, ← map_mul, hθ, map_one]
  set ε' := ψ.symm.toMonoidHom.comp ε with hε'
  have hε'inj : Function.Injective ε' := ψ.symm.injective.comp hε
  have hε'r : ε'.range = perfectCore (fixedSubgroup β) := by
    rw [hβdef, CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr,
      ← CFSG.Quasithin.map_perfectCore, hε', MonoidHom.range_comp, hεr]
    rfl
  obtain ⟨ψ₂, hψ₂⟩ := hnorm β hβ ε' hε'inj hε'r
  refine ⟨ψ₂.symm.trans ψ, fun g => ?_⟩
  rw [MulEquiv.trans_apply, ← hψ₂ g, MulEquiv.symm_apply_apply]
  exact MulEquiv.apply_symm_apply ψ (ε g)

end Normalization

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  [Finite G] {L : Subgroup G} {e : L ≃* adjointGroup .E7 (fixSubfield σ)}

omit
  [CharP K 2] in
theorem nonempty_fieldNeighbourIso (hnorm : NormalizationProperty (leviInclusion σ .high))
    (N : E7Neighbour)
    (hψ : Nonempty (N.levi K ≃* neighbourCore e N)) {t : G} (htL : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2)
    (hfix : perfectCore (neighbourCore e N ⊓ centralizer ({t} : Set G)) =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E7 (fixSubfield σ)).subtype)) :
    Nonempty (FieldNeighbourIso σ e N) := by
  obtain ⟨ψ₀⟩ := hψ
  have hN : t ∈ normalizer (neighbourCore e N : Set G) := le_normalizer_neighbourCore e htL N
  have ht : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
  have hθθ : (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ *
      (neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
    rw [← map_mul, show (⟨t, hN⟩ : normalizer (neighbourCore e N : Set G)) * ⟨t, hN⟩ = 1 from
      Subtype.ext ht, map_one]
  have hD : modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E7 (fixSubfield σ)).subtype) ≤
      neighbourCore e N := by
    rw [← hfix]
    exact (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  set ε₀ : E7Neighbour.high.levi (fixSubfield σ) →* G := L.subtype.comp (e.symm.toMonoidHom.comp
    ((N.levi (fixSubfield σ)).subtype.comp (highLeviConjEquiv (fixSubfield σ) N).toMonoidHom))
    with hε₀
  have hε₀M : ∀ g, ε₀ g ∈ neighbourCore e N := fun g =>
    hD (symm_mem_modelToG e ⟨_, (highLeviConjEquiv (fixSubfield σ) N g).2, rfl⟩)
  set ε : E7Neighbour.high.levi (fixSubfield σ) →* neighbourCore e N := ε₀.codRestrict _ hε₀M
    with hε
  have hεinj : Function.Injective ε := by
    intro g₁ g₂ h
    apply (highLeviConjEquiv (fixSubfield σ) N).injective
    apply Subtype.ext
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg (fun z : neighbourCore e N => (z : G)) h
  have hεrange : ε.range.map (neighbourCore e N).subtype =
      modelToG e ((N.levi (fixSubfield σ)).map (adjointGroup .E7 (fixSubfield σ)).subtype) := by
    ext g
    constructor
    · rintro ⟨_, ⟨g', rfl⟩, rfl⟩
      exact symm_mem_modelToG e ⟨_, (highLeviConjEquiv (fixSubfield σ) N g').2, rfl⟩
    · intro hg
      obtain ⟨x, ⟨y, hy, hyx⟩, rfl⟩ := (mem_modelToG e).1 hg
      have hxy : x = y := Subtype.ext hyx.symm
      subst hxy
      obtain ⟨g', hg'⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective ⟨x, hy⟩
      refine ⟨ε g', ⟨g', rfl⟩, ?_⟩
      change ((e.symm ((highLeviConjEquiv (fixSubfield σ) N g' : N.levi (fixSubfield σ)) :
        adjointGroup .E7 (fixSubfield σ)) : L) : G) = _
      rw [hg']
  have hεr : ε.range = perfectCore (MonoidHom.eqLocus
      ((neighbourCore e N).normalizerMonoidHom ⟨t, hN⟩).toMonoidHom (MonoidHom.id _)) := by
    apply map_injective (neighbourCore e N).subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, F4Pilot.map_eqLocus_normalizerMonoidHom hN, hfix,
      hεrange]
  obtain ⟨ψ', hψ'⟩ := exists_mulEquiv_leviInclusion_high_eq_of_normalization hnorm
    ((highLeviConjEquiv K N).trans ψ₀) hθθ ε hεinj hεr
  refine ⟨⟨(highLeviConjEquiv K N).symm.trans ψ', fun x => ?_⟩⟩
  obtain ⟨g, rfl⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective x
  rw [MulEquiv.trans_apply, leviInclusion, leviBaseChange_highLeviConjEquiv,
    MulEquiv.symm_apply_apply, ← leviInclusion, hψ']
  rfl

theorem exists_isFieldRowFamily (hq : 4 ≤ Nat.card (fixSubfield σ))
    (hnorm : NormalizationProperty (leviInclusion σ .high))
    (hψ : Nonempty (E7Neighbour.high.levi K ≃* neighbourCore e .high)) {t : G}
    (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hfix : perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E7Neighbour.high.levi (fixSubfield σ)).map
        (adjointGroup .E7 (fixSubfield σ)).subtype)) :
    ∃ φ : ∀ J, (adjDatumE7 K).leviAmalgam J →* G, IsFieldRowFamily e φ := by
  obtain ⟨hX⟩ := nonempty_fieldNeighbourIso hnorm .high hψ htL ht2 hfix
  exact exists_isFieldRowFamily_of_fieldNeighbourIso hX hq

end Main

end CFSG.SeitzReduction.E7Pilot
