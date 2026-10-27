module

public import CFSG.LargeExtraspecial.DWRtAbstract
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition
public import CFSG.LieType.Chevalley.GraphFixedParabolicLevi
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage

public section

namespace CFSG.LargeExtraspecial.DW

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K]

theorem mem_simpleOrbitRoots_of_parabolicPosRoots
    {a : Fin t.foldedTag.rank} {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ parabolicPosRoots t.tag (t.orbitUnion {a})) : α ∈ simpleOrbitRoots t a := by
  obtain ⟨⟨hr, hz⟩, -, hp⟩ := hα
  have key : ∀ k < t.tag.rootCertificate.roots.length, ∀ c : Fin t.foldedTag.rank,
      0 < height (t.tag.rootCertificate.root k) ∧
        (∀ i, t.orbitIndex i ≠ c → t.tag.rootCertificate.root k i = 0) →
      ∃ j ∈ t.orbit c, t.tag.rootCertificate.root k = Pi.single j 1 := by
    cases t <;> decide +kernel
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check t.tag) hr
  obtain ⟨j, hj, he⟩ := key k hk a ⟨hp, fun i hi => hz i fun h =>
    hi ((mem_orbitUnion_iff_orbitIndex).1 h)⟩
  exact ⟨j, hj, he.symm⟩

theorem graphFixedSimpleComplement_le_graphFixedParabolicRadical
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    graphFixedSimpleComplement t K σ a ≤ graphFixedParabolicRadical t K σ {a} := by
  refine inf_le_inf_right _ (rootSpan_mono fun α hα => ?_)
  obtain ⟨hpos, hnot⟩ := hα
  exact ⟨hpos, fun h => hnot (mem_simpleOrbitRoots_of_parabolicPosRoots h)⟩

theorem orbitRankOneHom_range_le_parabolicLevi
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    (orbitRankOneHom t K σ a).range ≤ parabolicLevi t.tag K (t.orbitUnion {a}) := by
  have hA : ∀ i ∈ t.orbit a, i ∈ t.orbitUnion {a} := fun i hi =>
    (mem_orbitUnion_iff_orbitIndex).2 ((t.mem_orbit_iff).1 hi)
  rw [orbitRankOneHom_range]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · have hx := (Subgroup.mem_inf.1 (orbitX_mem t σ a c)).1
    refine (iSup₂_le fun α hα => ?_ : rootSpan t.tag K _ ≤ _) hx
    obtain ⟨i, hi, rfl⟩ := hα
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c', rfl⟩
    rw [SetLike.mem_coe, pinnedX_single]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hA i hi, c', Or.inl rfl⟩)
  · have hy : (orbitY t K σ a c : ModGL t.tag K) ∈
        rootSpan t.tag K ((fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)) ⊓
          twistedFixedGroup t K σ :=
      (mem_rootSpan_negSimpleOrbitRoots_iff a).2 ⟨c, rfl⟩
    refine (iSup₂_le fun α hα => ?_ : rootSpan t.tag K _ ≤ _) (Subgroup.mem_inf.1 hy).1
    obtain ⟨i, hi, rfl⟩ := hα
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c', rfl⟩
    rw [SetLike.mem_coe, pinnedX_neg_single]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, hA i hi, c', Or.inr rfl⟩)

theorem orbitRankOneHom_range_le_graphFixedRootGroup
    (σ : K →+* K) (a : Fin t.foldedTag.rank) :
    (orbitRankOneHom t K σ a).range ≤ graphFixedRootGroup t K σ := by
  rw [orbitRankOneHom_range]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a c)
  · exact graphFixedNegUnipotent_le_graphFixedRootGroup t K σ
      (orbitY_mem_graphFixedNegUnipotent t σ a c)

theorem not_isTransClass34_graphFixedRootGroup
    [Finite K] [CharP K 2] (σ : K ≃+* K)
    (hL : ∀ a, 4 ≤ Nat.card (orbitField t K σ.toRingHom a))
    (D : Set (graphFixedRootGroup t K σ.toRingHom)) : ¬ IsTransClass34 D := by
  intro hD
  have hfin : Finite (ModGL t.tag K) := finite_modGL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element t.tag
  obtain ⟨⟨S, hS⟩, -, hUV, -⟩ := exceptional_fixed_Sylow_opposition t K 2 σ w₀ hw₀
  let C := graphFixedRootGroup t K σ.toRingHom
  let U : Subgroup C := (graphFixedPosUnipotent t K σ.toRingHom).subgroupOf C
  have hDU : ∃ d ∈ D, d ∈ U := by
    obtain ⟨d₀, hd₀, -⟩ := hD.2.1
    obtain ⟨hne, hsq⟩ := hD.2.2.1 d₀ hd₀
    have h2 : IsPGroup 2 (Subgroup.zpowers d₀) := by
      rintro ⟨g, hg⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      refine ⟨1, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, sq, hsq, one_zpow]
    obtain ⟨T, hT⟩ := h2.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C T S
    refine ⟨g * d₀ * g⁻¹, hD.conj_mem g hd₀, ?_⟩
    have hmem : g * d₀ * g⁻¹ ∈ ((g • T : Sylow 2 C) : Subgroup C) := by
      rw [coe_smul_sylow_eq_map]
      exact ⟨d₀, hT (Subgroup.mem_zpowers d₀), rfl⟩
    rw [hg, hS] at hmem
    exact hmem
  let R : ∀ a, SL2 (orbitField t K σ.toRingHom a) →* ModGL t.tag K := fun a =>
    orbitRankOneHom t K σ.toRingHom a
  have hRinj : ∀ a, Function.Injective (R a) := fun a =>
    injective_of_ker_scalar _ fun g hg => eq_smul_one_of_mem_ker_orbitRankOneHom hg
  have hRC : ∀ a g, R a g ∈ C := fun a g =>
    orbitRankOneHom_range_le_graphFixedRootGroup σ.toRingHom a ⟨g, rfl⟩
  have hRM : ∀ a g, R a g ∈ graphFixedParabolicLevi t K σ.toRingHom {a} := fun a g =>
    ⟨orbitRankOneHom_range_le_parabolicLevi σ.toRingHom a ⟨g, rfl⟩, hRC a g⟩
  have hU : U ≠ ⊤ := by
    intro htop
    let a₀ : Fin t.foldedTag.rank := ⟨0, by cases t <;> decide⟩
    have hy : (⟨R a₀ (vSL 1), hRC a₀ _⟩ : C) ∈ U := htop ▸ Subgroup.mem_top _
    have hy' : R a₀ (vSL 1) ∈ graphFixedPosUnipotent t K σ.toRingHom ⊓
        graphFixedNegUnipotent t K σ.toRingHom := by
      refine ⟨hy, ?_⟩
      change orbitRankOneHom t K σ.toRingHom a₀ (vSL 1) ∈ _
      rw [orbitRankOneHom_vSL]
      exact orbitY_mem_graphFixedNegUnipotent t σ.toRingHom a₀ 1
    rw [hUV, Subgroup.mem_bot, ← map_one (R a₀)] at hy'
    have h1 := congrArg (fun g : SL2 (orbitField t K σ.toRingHom a₀) => g.1 1 0) (hRinj a₀ hy')
    have e1 : (vSL (1 : orbitField t K σ.toRingHom a₀)).1 1 0 = 1 := rfl
    have e2 : (1 : SL2 (orbitField t K σ.toRingHom a₀)).1 1 0 = 0 := by
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact Matrix.one_apply_ne (by decide)
    exact one_ne_zero (e1.symm.trans (h1.trans e2))
  let φ : ∀ a, SL2 (orbitField t K σ.toRingHom a) →* C := fun a => (R a).codRestrict C (hRC a)
  choose s hs0 hs1 using fun a => exists_ne_zero_ne_one_of_four_le (hL a)
  have hfac := fun a => diagram_fixed_parabolic_root_radical_Levi_factors t K σ {a}
  refine false_of_parabolic_family hD U hDU hU
    (fun a => (graphFixedParabolic t K σ.toRingHom {a}).subgroupOf C)
    (fun a => (graphFixedParabolicRadical t K σ.toRingHom {a}).subgroupOf C)
    (fun a => (graphFixedParabolicLevi t K σ.toRingHom {a}).subgroupOf C) ?_ ?_ ?_ ?_ ?_
    (fun a => orbitField t K σ.toRingHom a) s hs0 hs1 φ ?_ ?_ ?_
  ·
    intro a x hx
    exact inf_le_inf_right _ (parabolicRadical_le_posUnipotent _) hx
  ·
    intro a p hp x hx
    obtain ⟨-, -, -, -, -, -, -, -, hQX, hQn, -⟩ := hfac a
    have hn := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).1 hQn hp
    have := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
    exact Subgroup.mem_subgroupOf.2 this
  ·
    intro a x hx
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hLP, -⟩ := hfac a
    exact hLP hx
  ·
    intro a
    obtain ⟨-, -, -, -, -, -, hQM, -⟩ := hfac a
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : (x : ModGL t.tag K) ∈ graphFixedParabolicRadical t K σ.toRingHom {a} ⊓
        (parabolicLevi t.tag K (t.orbitUnion {a}) ⊓ twistedFixedGroup t K σ.toRingHom) :=
      ⟨hx.1, (Subgroup.mem_inf.1 hx.2).1, graphFixedRootGroup_le t K σ.toRingHom x.2⟩
    rw [hQM, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).2 (Subtype.ext hx')
  ·
    rw [eq_top_iff]
    intro g _
    let a₀ : Fin t.foldedTag.rank := ⟨0, by cases t <;> decide⟩
    have hle : C ≤ (⨆ a, (graphFixedParabolic t K σ.toRingHom {a}).subgroupOf C).map
        C.subtype := by
      change graphFixedRootGroup t K σ.toRingHom ≤ _
      rw [graphFixedRootGroup_eq_sup_closure σ.surjective]
      refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
      · have hbC : b ∈ C := graphFixedRootBorel_le t K σ.toRingHom hb
        exact ⟨⟨b, hbC⟩, Subgroup.mem_iSup_of_mem a₀
          (graphFixedRootBorel_le_graphFixedParabolic t K σ.toRingHom {a₀} hb), rfl⟩
      · rintro _ ⟨a, rfl⟩
        have hn := canonicalRep_orbitReflection_mem_graphFixedRootGroup (K := K)
          (σ := σ.toRingHom) a
        exact ⟨⟨_, hn⟩, Subgroup.mem_iSup_of_mem a
          (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨a, rfl, rfl⟩)), rfl⟩
    obtain ⟨y, hy, hyg⟩ := hle g.2
    rwa [show y = g from Subtype.ext hyg] at hy
  ·
    intro a x y h
    exact hRinj a (congrArg Subtype.val h)
  ·
    rintro a _ ⟨g, rfl⟩
    exact hRM a g
  ·
    intro a u hu
    obtain ⟨-, -, hmul, -⟩ := fixed_simple_positive_complement t K σ a
    have hu' : (u : ModGL t.tag K) ∈ (graphFixedSimpleComplement t K σ.toRingHom a :
        Set (ModGL t.tag K)) * Set.range (fun c : orbitField t K σ.toRingHom a =>
          (orbitX t K σ.toRingHom a c : ModGL t.tag K)) := by
      rw [← hmul]
      exact hu
    obtain ⟨v, hv, _, ⟨c, rfl⟩, hvc⟩ := hu'
    have hvQ := graphFixedSimpleComplement_le_graphFixedParabolicRadical σ.toRingHom a hv
    have hRu : R a (uSL c) = (orbitX t K σ.toRingHom a c : ModGL t.tag K) :=
      orbitRankOneHom_uSL a c
    have hvC : v ∈ C := by
      have : v = (u : ModGL t.tag K) * (R a (uSL c))⁻¹ := by rw [hRu, ← hvc]; group
      rw [this]
      exact C.mul_mem u.2 (C.inv_mem (hRC a _))
    refine ⟨⟨v, hvC⟩, hvQ, uSL c, Subtype.ext ?_⟩
    change (u : ModGL t.tag K) = v * R a (uSL c)
    rw [hRu]
    exact hvc.symm

end CFSG.LargeExtraspecial.DW
