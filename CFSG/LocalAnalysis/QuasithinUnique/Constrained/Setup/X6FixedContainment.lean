module

public import CFSG.LieType.Chevalley.GraphFixedSimplePairs
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public section

namespace CFSG.QuasithinUnique.Setup.X6

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

section Fixed

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem conj_mem_graphFixedRootTorus
    {m h : ModGL t.tag K}
    (hm : m ∈ graphFixedRootMonomial t K σ) (hh : h ∈ graphFixedRootTorus t K σ) :
    m * h * m⁻¹ ∈ graphFixedRootTorus t K σ := by
  have hN := graphFixedRootTorus_subgroupOf_normal t K σ
  have hHN : graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)
  exact Subgroup.mem_subgroupOf.1
    (hN.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨m, hm⟩)

theorem canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent
    {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α)
    (hpos : ∀ α ∈ S, 0 < height (w⁻¹ • α)) {g : ModGL t.tag K}
    (hg : g ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) :
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹ * g * canonicalRep (coxeterSystem t.tag) K w ∈
      graphFixedPosUnipotent t K σ := by
  set n := canonicalRep (coxeterSystem t.tag) K w
  have hn : n ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ ((mem_relWeylTwist t).1 hw)
  obtain ⟨hgS, hgΓ⟩ := Subgroup.mem_inf.1 hg
  have hmap := (canonical_weyl_root_transport t.tag K).1 w ((fun α => w⁻¹ • α) '' S)
    (by rintro _ ⟨α, hα, rfl⟩; exact IsRoot.smul (hS α hα) w⁻¹)
  rw [Set.image_image, Set.image_congr fun α _ => smul_inv_smul w α, Set.image_id'] at hmap
  rw [← hmap] at hgS
  obtain ⟨y, hy, hyg⟩ := hgS
  have hyg' : n * y * n⁻¹ = g := hyg
  have e : n⁻¹ * g * n = y := by rw [← hyg']; group
  rw [e]
  have hyΓ : y ∈ twistedFixedGroup t K σ := by
    rw [← e]
    exact mul_mem (mul_mem (inv_mem hn) hgΓ) hn
  refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hy, hyΓ⟩
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨IsRoot.smul (hS α hα) w⁻¹, hpos α hα⟩

theorem orbitY_mem_of_posUnipotent
    {M : Subgroup (ModGL t.tag K)}
    (hU : graphFixedPosUnipotent t K σ ≤ M) {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {h : ModGL t.tag K} (hh : h ∈ graphFixedRootTorus t K σ)
    (hz : h * canonicalRep (coxeterSystem t.tag) K w ∈ M) {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0)
    (c : orbitField t K σ a) : (orbitY t K σ a c : ModGL t.tag K) ∈ M := by
  set n := canonicalRep (coxeterSystem t.tag) K w
  set S : Set (Fin t.tag.rank → ℤ) :=
    (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a)
  have hSr : ∀ α ∈ S, IsRoot t.tag α := by
    rintro _ ⟨i, -, rfl⟩
    exact isRoot_neg_single _ i
  have hSp : ∀ α ∈ S, 0 < height (w⁻¹ • α) := by
    rintro _ ⟨i, hi, rfl⟩
    rw [smul_neg, height_neg]
    linarith [hneg i hi]
  have hyS : (orbitY t K σ a c : ModGL t.tag K) ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
    have := (orbitYEquiv t σ a (Multiplicative.ofAdd c)).2
    rwa [coe_orbitYEquiv] at this
  have hhT : h ∈ torusGroup t.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have hhΓ : h ∈ twistedFixedGroup t K σ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).2
  have hg : h⁻¹ * (orbitY t K σ a c : ModGL t.tag K) * h ∈
      rootSpan t.tag K S ⊓ twistedFixedGroup t K σ := by
    refine Subgroup.mem_inf.2 ⟨?_, mul_mem (mul_mem (inv_mem hhΓ) (Subgroup.mem_inf.1 hyS).2) hhΓ⟩
    have := (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (K := K) hSr (inv_mem hhT)) _).1
      (Subgroup.mem_inf.1 hyS).1
    rw [inv_inv] at this
    exact this
  have h1 := canonicalRep_inv_mul_mul_mem_graphFixedPosUnipotent (σ := σ) hw hSr hSp hg
  have e : (orbitY t K σ a c : ModGL t.tag K) = (h * n) *
      (n⁻¹ * (h⁻¹ * (orbitY t K σ a c : ModGL t.tag K) * h) * n) * (h * n)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hz (hU h1)) (inv_mem hz)

theorem canonicalRep_orbitReflection_mem_of_posUnipotent
    {M : Subgroup (ModGL t.tag K)}
    (hU : graphFixedPosUnipotent t K σ ≤ M) {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {h : ModGL t.tag K} (hh : h ∈ graphFixedRootTorus t K σ)
    (hz : h * canonicalRep (coxeterSystem t.tag) K w ∈ M) {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M := by
  have hx : ∀ c : orbitField t K σ a, (orbitX t K σ a c : ModGL t.tag K) ∈ M := fun c =>
    hU (orbitX_mem_graphFixedPosUnipotent t σ a c)
  rw [canonicalRep_orbitReflection_eq_orbitN t σ a, orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
  exact mul_mem (mul_mem (hx _) (orbitY_mem_of_posUnipotent hU hw hh hz hneg _)) (hx _)

theorem canonicalRep_orbitReflection_mem_of_reduced_of_posUnipotent
    {M : Subgroup (ModGL t.tag K)} (hU : graphFixedPosUnipotent t K σ ≤ M)
    (ω : List (Fin t.foldedTag.rank)) :
    ∀ w ∈ relWeylTwist t, (ω.map t.orbitReflection).prod = w → ω.length = t.orbitLength w →
      ∀ h ∈ graphFixedRootTorus t K σ, h * canonicalRep (coxeterSystem t.tag) K w ∈ M →
        ∀ a ∈ ω, canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M := by
  induction ω with
  | nil => intro _ _ _ _ _ _ _ a ha; exact absurd ha List.not_mem_nil
  | cons a ω ih =>
    intro w hw hprod hlen h hh hz
    set w' := (ω.map t.orbitReflection).prod
    have hw' : w' ∈ relWeylTwist t := t.list_prod_orbitReflection_mem ω
    have hww' : w = t.orbitReflection a * w' := by
      rw [← hprod, List.map_cons, List.prod_cons]
    have hle : t.orbitLength w' ≤ ω.length := orbitLength_le t ω
    have hle' := orbitLength_orbitReflection_mul_le hw' a
    rw [← hww', ← hlen, List.length_cons] at hle'
    have hlen' : ω.length = t.orbitLength w' := by omega
    have hup : t.orbitLength (t.orbitReflection a * w') = t.orbitLength w' + 1 := by
      rw [← hww', ← hlen, List.length_cons, hlen']
    have hpos := forall_height_inv_smul_pos_of_orbitLength hw' hup
    have hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 := by
      intro i hi
      rw [hww', mul_inv_rev, t.orbitReflection_inv, mul_smul, t.orbitReflection_smul_single hi,
        smul_neg, height_neg]
      linarith [hpos i hi]
    have hNA := canonicalRep_orbitReflection_mem_of_posUnipotent hU hw hh hz hneg
    obtain ⟨h', hh', hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ)
      (t.orbitReflection_mem a) hw'
    rw [← hww'] at hrep
    set N := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
    set W := canonicalRep (coxeterSystem t.tag) K w
    set V := canonicalRep (coxeterSystem t.tag) K w'
    have hNm : N ∈ graphFixedRootMonomial t K σ :=
      canonicalRep_mem_graphFixedRootMonomial t K σ (t.orbitReflection_mem a)
    have hVm : V ∈ graphFixedRootMonomial t K σ := canonicalRep_mem_graphFixedRootMonomial t K σ hw'
    have h1 : N⁻¹ * h * N ∈ graphFixedRootTorus t K σ := by
      have := conj_mem_graphFixedRootTorus (inv_mem hNm) hh
      rwa [inv_inv] at this
    have h2 : V * h'⁻¹ * V⁻¹ ∈ graphFixedRootTorus t K σ :=
      conj_mem_graphFixedRootTorus hVm (inv_mem hh')
    have e : ((N⁻¹ * h * N) * (V * h'⁻¹ * V⁻¹)) * V = N⁻¹ * (h * W) := by
      have hr : N * V = W * h' := hrep
      calc ((N⁻¹ * h * N) * (V * h'⁻¹ * V⁻¹)) * V = N⁻¹ * h * (N * V) * h'⁻¹ := by group
        _ = N⁻¹ * h * (W * h') * h'⁻¹ := by rw [hr]
        _ = N⁻¹ * (h * W) := by group
    have hz' : ((N⁻¹ * h * N) * (V * h'⁻¹ * V⁻¹)) * V ∈ M := by
      rw [e]
      exact mul_mem (inv_mem hNA) hz
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb'
    · exact hNA
    · exact ih w' hw' rfl hlen' _ (mul_mem h1 h2) hz' b hb'

variable (hσ : Function.Surjective σ)
include hσ

theorem le_graphFixedParabolic_of_posUnipotent_le
    {M : Subgroup (ModGL t.tag K)}
    (hMC : M ≤ graphFixedRootGroup t K σ) (hU : graphFixedPosUnipotent t K σ ≤ M) :
    M ≤ graphFixedParabolic t K σ
      {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} := by
  intro g hg
  have hg' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hMC hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', hgb⟩ := mem_graphFixedRootBruhatCell.1 hgw
  obtain ⟨u₁, hu₁, h₁, hh₁, rfl⟩ : b ∈ (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) *
      (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul' hσ]
    exact hb
  obtain ⟨h₂, hh₂, u₂, hu₂, rfl⟩ : b' ∈ (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
      (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [← graphFixedRootBorel_eq_mul hσ]
    exact hb'
  have hnm : canonicalRep (coxeterSystem t.tag) K w ∈ graphFixedRootMonomial t K σ :=
    canonicalRep_mem_graphFixedRootMonomial t K σ hw
  have hh : canonicalRep (coxeterSystem t.tag) K w * h₂ * (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
      graphFixedRootTorus t K σ := conj_mem_graphFixedRootTorus hnm hh₂
  have hz : (h₁ * (canonicalRep (coxeterSystem t.tag) K w * h₂ *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹)) * canonicalRep (coxeterSystem t.tag) K w ∈ M := by
    have e : (h₁ * (canonicalRep (coxeterSystem t.tag) K w * h₂ *
        (canonicalRep (coxeterSystem t.tag) K w)⁻¹)) * canonicalRep (coxeterSystem t.tag) K w =
        u₁⁻¹ * g * u₂⁻¹ := by
      rw [← hgb]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem (hU hu₁)) hg) (inv_mem (hU hu₂))
  obtain ⟨ω, hω, hlen⟩ := exists_reduced_orbitWord hw
  have hletters := canonicalRep_orbitReflection_mem_of_reduced_of_posUnipotent hU ω w hw hω hlen _
    (by
      refine mul_mem ?_ hh
      exact hh₁) hz
  have hwJ : w ∈ foldedParabolicWeylGroup t
      {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} :=
    hω ▸ list_prod_orbitReflection_mem_foldedParabolicWeylGroup hletters
  exact graphFixedParabolicCells_subset _ ⟨w, hwJ, hgw⟩

omit hσ

end Fixed

theorem fixed_positive_root_overgroup_parabolic_containment
    (t : TwistTag) (K : Type) [Field K]
    (σ : K ≃+* K) {M : Subgroup (ModGL t.tag K)}
    (hMC : M ≤ graphFixedRootGroup t K σ.toRingHom)
    (hU : graphFixedPosUnipotent t K σ.toRingHom ≤ M) :
    M ≤ graphFixedParabolic t K σ.toRingHom
        {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} ∧
    ({a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} = Set.univ ↔
      M = graphFixedRootGroup t K σ.toRingHom) ∧
    (M ≠ graphFixedRootGroup t K σ.toRingHom → ∃ J : Set (Fin t.foldedTag.rank),
      J ≠ Set.univ ∧ M ≤ graphFixedParabolic t K σ.toRingHom J ∧
        graphFixedParabolic t K σ.toRingHom J ≠ graphFixedRootGroup t K σ.toRingHom) := by
  have hσ := σ.surjective
  have hle := le_graphFixedParabolic_of_posUnipotent_le hσ hMC hU
  have hiff : {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} = Set.univ ↔
      M = graphFixedRootGroup t K σ.toRingHom := by
    constructor
    · intro h
      refine le_antisymm hMC ?_
      rw [graphFixedRootGroup_eq_iSup_orbitRankOneGroup hσ]
      refine iSup_le fun a => (Subgroup.closure_le _).2 ?_
      have hn : canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M := by
        have : a ∈ {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} := by
          rw [h]; trivial
        exact this
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact hU (orbitX_mem_graphFixedPosUnipotent t σ.toRingHom a c)
      · have := orbitY_mem_of_posUnipotent (h := 1) hU (t.orbitReflection_mem a)
          (one_mem _) (by rwa [one_mul]) (a := a) (fun i hi => by
            rw [t.orbitReflection_inv, t.orbitReflection_smul_single hi, height_neg, height_single]
            omega) c
        exact this
    · rintro rfl
      exact Set.eq_univ_of_forall fun a => canonicalRep_orbitReflection_mem_graphFixedRootGroup a
  refine ⟨hle, hiff, fun hne => ⟨_, fun h => hne (hiff.1 h), hle, fun hP => ?_⟩⟩
  have : ∀ a : Fin t.foldedTag.rank,
      a ∈ {a | canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) ∈ M} := fun a =>
    (canonicalRep_orbitReflection_mem_graphFixedParabolic_iff hσ).1
      (hP ▸ canonicalRep_orbitReflection_mem_graphFixedRootGroup a)
  exact hne (hiff.1 (Set.eq_univ_of_forall this))

end CFSG.QuasithinUnique.Setup.X6
