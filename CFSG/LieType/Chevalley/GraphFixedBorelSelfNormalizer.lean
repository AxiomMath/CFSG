module

public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.OppositeBorel

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem mem_relWeylTwist_of_forall_length_le
    {w₀ : WeylGroup t.tag}
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    w₀ ∈ relWeylTwist t := by
  have h₀ := reversesSigns_of_forall_length_le hw₀
  have h₁ : ReversesSigns (weylTwist t w₀) := reversesSigns_of_forall_length_le fun u => by
    rw [length_weylTwist]
    exact hw₀ u
  exact (mem_relWeylTwist t).2 (h₁.eq h₀)

theorem graphFixedRootTorus_le_normalizer_graphFixedNegUnipotent :
    graphFixedRootTorus t K σ ≤
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) := by
  intro h hh
  obtain ⟨⟨hhH, hhΓ⟩, -⟩ := Subgroup.mem_inf.1 hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_negUnipotent hhH) g
  constructor
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hN.1 hgU, mul_mem (mul_mem hhΓ hgΓ) (inv_mem hhΓ)⟩
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hN.2 hgU, ?_⟩
    have e : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhΓ) hgΓ) hhΓ

theorem graphFixedRootBorel_eq_sup
    (hσ : Function.Surjective σ) :
    graphFixedRootBorel t K σ = graphFixedRootTorus t K σ ⊔ graphFixedPosUnipotent t K σ := by
  refine le_antisymm (fun b hb => ?_) (sup_le graphFixedRootTorus_le_graphFixedRootBorel
    graphFixedPosUnipotent_le_graphFixedRootBorel)
  have hb' : b ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul hσ] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  exact mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)

variable {w₀ : WeylGroup t.tag}
  (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀)
include hw₀

theorem map_conj_graphFixedPosUnipotent :
    (graphFixedPosUnipotent t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedNegUnipotent t K σ := by
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ twistedFixedGroup t K σ :=
    canonicalRep_mem_twistedFixedGroup t K σ
      ((mem_relWeylTwist t).1 (mem_relWeylTwist_of_forall_length_le hw₀))
  have hU := (canonical_weyl_root_transport t.tag K).1 w₀ {α | IsRoot t.tag α ∧ 0 < height α}
    fun α hα => hα.1
  rw [image_smul_posRoots_of_reversesSigns (reversesSigns_of_forall_length_le hw₀)] at hU
  rw [graphFixedPosUnipotent, Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective]
  change (posUnipotent t.tag K).map _ ⊓ _ = negUnipotent t.tag K ⊓ _
  rw [posUnipotent, hU, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]
  rfl

theorem map_conj_graphFixedRootTorus :
    (graphFixedRootTorus t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedRootTorus t K σ := by
  have hw := mem_relWeylTwist_of_forall_length_le hw₀
  have hn := canonicalRep_mem_graphFixedRootMonomial t K σ hw
  have hNt := graphFixedRootTorus_subgroupOf_normal t K σ
  have hHN : graphFixedRootTorus t K σ ≤ graphFixedRootMonomial t K σ :=
    inf_le_inf_right _ (graphFixedTorus_le_graphFixedMonomial t K σ)
  refine map_conj_eq_of_mem_normalizer ((Subgroup.mem_normalizer_iff).2 fun h => ⟨fun hh => ?_,
    fun hh => ?_⟩)
  · exact Subgroup.mem_subgroupOf.1 (hNt.conj_mem ⟨h, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh)
      ⟨_, hn⟩)
  · set n := canonicalRep (coxeterSystem t.tag) K w₀
    have h' : n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ ∈ graphFixedRootTorus t K σ :=
      Subgroup.mem_subgroupOf.1 (hNt.conj_mem ⟨_, hHN hh⟩ (Subgroup.mem_subgroupOf.2 hh)
        ⟨_, inv_mem hn⟩)
    rwa [show n⁻¹ * (n * h * n⁻¹) * n⁻¹⁻¹ = h by group] at h'

theorem map_conj_graphFixedRootBorel
    (hσ : Function.Surjective σ) :
    (graphFixedRootBorel t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedRootTorus t K σ ⊔ graphFixedNegUnipotent t K σ := by
  rw [graphFixedRootBorel_eq_sup hσ, Subgroup.map_sup, map_conj_graphFixedRootTorus hw₀,
    map_conj_graphFixedPosUnipotent hw₀]

omit hw₀

theorem coe_graphFixedRootTorus_sup_graphFixedNegUnipotent :
    ((graphFixedRootTorus t K σ ⊔ graphFixedNegUnipotent t K σ : Subgroup (ModGL t.tag K)) :
        Set (ModGL t.tag K)) =
      (graphFixedRootTorus t K σ : Set (ModGL t.tag K)) *
        (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _
    graphFixedRootTorus_le_normalizer_graphFixedNegUnipotent

include hw₀

theorem graphFixedRootBorel_inf_map_conj :
    graphFixedRootBorel t K σ ⊓ (graphFixedRootBorel t K σ).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedRootTorus t K σ := by
  obtain ⟨-, hmap, hinf, -⟩ := opposite_Borel_intersection t.tag K w₀ hw₀
  have hH : graphFixedRootTorus t K σ ≤ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    rw [← map_conj_graphFixedRootTorus (K := K) (σ := σ) hw₀]
    exact Subgroup.map_mono graphFixedRootTorus_le_graphFixedRootBorel
  refine le_antisymm (fun x hx => ?_) (le_inf graphFixedRootTorus_le_graphFixedRootBorel hH)
  obtain ⟨hxB, hxB'⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨⟨hxB₀, hxΓ⟩, hxC⟩ := Subgroup.mem_inf.1 hxB
  have hxB'' : x ∈ (borelGroup t.tag K).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom :=
    Subgroup.map_mono (fun b hb => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1) hxB'
  rw [hmap] at hxB''
  have hxH : x ∈ torusGroup t.tag K := by
    rw [← hinf]
    exact Subgroup.mem_inf.2 ⟨hxB₀, hxB''⟩
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hxH, hxΓ⟩, hxC⟩

omit hw₀

theorem graphFixedRootBorel_inf_graphFixedNegUnipotent :
    graphFixedRootBorel t K σ ⊓ graphFixedNegUnipotent t K σ = ⊥ := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨-, -, -, hinf⟩ := opposite_Borel_intersection t.tag K w₀ hmax
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxB, hxU⟩ := Subgroup.mem_inf.1 hx
  rw [← hinf]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxB).1).1,
    (Subgroup.mem_inf.1 hxU).1⟩

theorem eq_one_of_conj_orbitX_mem
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (h : ∀ a, canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a 1 *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ graphFixedRootBorel t K σ) : w = 1 := by
  by_contra h1
  obtain ⟨a, ha⟩ := exists_forall_height_smul_single_neg t hw h1
  have hmem := canonicalRep_conj_orbitX_mem t σ a hw 1
  obtain ⟨hS, hΓ⟩ := Subgroup.mem_inf.1 hmem
  have hU : canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a 1 *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ graphFixedNegUnipotent t K σ := by
    refine Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hS, hΓ⟩
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨IsRoot.smul (isRoot_single _ i) w, ha i hi⟩
  have h₁ : canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a 1 *
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈
        graphFixedRootBorel t K σ ⊓ graphFixedNegUnipotent t K σ := Subgroup.mem_inf.2 ⟨h a, hU⟩
  rw [graphFixedRootBorel_inf_graphFixedNegUnipotent, Subgroup.mem_bot,
    mul_inv_eq_one, mul_eq_left] at h₁
  have h₂ : orbitX t K σ a 1 = orbitX t K σ a 0 := by
    rw [orbitX_zero]
    exact Subtype.ext h₁
  exact one_ne_zero (orbitX_injective σ a h₂)

variable (hσ : Function.Surjective σ)
include hσ

theorem mem_graphFixedRootBorel_of_conj
    {g : ModGL t.tag K} (hg : g ∈ graphFixedRootGroup t K σ)
    (H : ∀ b ∈ graphFixedRootBorel t K σ, ∀ b' ∈ graphFixedRootBorel t K σ, ∀ w ∈ relWeylTwist t,
      b * canonicalRep (coxeterSystem t.tag) K w * b' = g → ∀ a,
        canonicalRep (coxeterSystem t.tag) K w * orbitX t K σ a 1 *
          (canonicalRep (coxeterSystem t.tag) K w)⁻¹ ∈ graphFixedRootBorel t K σ) :
    g ∈ graphFixedRootBorel t K σ := by
  have hg' : g ∈ (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) := hg
  rw [graphFixedRootGroup_eq_iUnion hσ] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := Set.mem_iUnion.1 hg'
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hgw
  have h1 := eq_one_of_conj_orbitX_mem hw (H b hb b' hb' w hw rfl)
  subst h1
  rw [canonicalRep_one, mul_one]
  exact mul_mem hb hb'

theorem graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent :
    graphFixedRootGroup t K σ ⊓
        Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) =
      graphFixedRootBorel t K σ := by
  have hBN : graphFixedRootBorel t K σ ≤
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer graphFixedPosUnipotent_le_graphFixedRootBorel).1
      graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal
  refine le_antisymm (fun g hg => ?_) (le_inf (graphFixedRootBorel_le t K σ) hBN)
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  refine mem_graphFixedRootBorel_of_conj hσ hgC fun b hb b' hb' w _ hgw a => ?_
  have hn : canonicalRep (coxeterSystem t.tag) K w = b⁻¹ * g * b'⁻¹ := by
    rw [← hgw]
    group
  have hnN : canonicalRep (coxeterSystem t.tag) K w ∈
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
    rw [hn]
    exact mul_mem (mul_mem (inv_mem (hBN hb)) hgN) (inv_mem (hBN hb'))
  exact graphFixedPosUnipotent_le_graphFixedRootBorel
    ((Subgroup.mem_normalizer_iff.1 hnN _).1 (orbitX_mem_graphFixedPosUnipotent t σ a 1))

theorem graphFixedRootGroup_inf_normalizer_graphFixedRootBorel :
    graphFixedRootGroup t K σ ⊓
        Subgroup.normalizer (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) =
      graphFixedRootBorel t K σ := by
  refine le_antisymm (fun g hg => ?_)
    (le_inf (graphFixedRootBorel_le t K σ) Subgroup.le_normalizer)
  obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
  refine mem_graphFixedRootBorel_of_conj hσ hgC fun b hb b' hb' w _ hgw a => ?_
  have hn : canonicalRep (coxeterSystem t.tag) K w = b⁻¹ * g * b'⁻¹ := by
    rw [← hgw]
    group
  have hnN : canonicalRep (coxeterSystem t.tag) K w ∈
      Subgroup.normalizer (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := by
    rw [hn]
    exact mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hb)) hgN)
      (inv_mem (Subgroup.le_normalizer hb'))
  exact (Subgroup.mem_normalizer_iff.1 hnN _).1 (graphFixedPosUnipotent_le_graphFixedRootBorel
    (orbitX_mem_graphFixedPosUnipotent t σ a 1))

omit hσ

theorem fixed_Borel_self_normalizers
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K)
    (w₀ : WeylGroup t.tag)
    (hw₀ : ∀ w, (coxeterSystem t.tag).length w ≤ (coxeterSystem t.tag).length w₀) :
    w₀ ∈ relWeylTwist t ∧
    canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootMonomial t K σ.toRingHom ∧
    (graphFixedRootBorel t K σ.toRingHom).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedRootTorus t K σ.toRingHom ⊔ graphFixedNegUnipotent t K σ.toRingHom ∧
    ((graphFixedRootTorus t K σ.toRingHom ⊔ graphFixedNegUnipotent t K σ.toRingHom :
        Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) =
      (graphFixedRootTorus t K σ.toRingHom : Set (ModGL t.tag K)) *
        (graphFixedNegUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) ∧
    graphFixedRootBorel t K σ.toRingHom ⊓ (graphFixedRootBorel t K σ.toRingHom).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom =
      graphFixedRootTorus t K σ.toRingHom ∧
    graphFixedRootBorel t K σ.toRingHom ⊓ graphFixedNegUnipotent t K σ.toRingHom = ⊥ ∧
    graphFixedRootGroup t K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedPosUnipotent t K σ.toRingHom : Set (ModGL t.tag K)) =
      graphFixedRootBorel t K σ.toRingHom ∧
    graphFixedRootGroup t K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedRootBorel t K σ.toRingHom : Set (ModGL t.tag K)) =
      graphFixedRootBorel t K σ.toRingHom :=
  ⟨mem_relWeylTwist_of_forall_length_le hw₀,
    canonicalRep_mem_graphFixedRootMonomial t K σ.toRingHom
      (mem_relWeylTwist_of_forall_length_le hw₀),
    map_conj_graphFixedRootBorel hw₀ σ.surjective,
    coe_graphFixedRootTorus_sup_graphFixedNegUnipotent,
    graphFixedRootBorel_inf_map_conj hw₀,
    graphFixedRootBorel_inf_graphFixedNegUnipotent,
    graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent σ.surjective,
    graphFixedRootGroup_inf_normalizer_graphFixedRootBorel σ.surjective⟩

end CFSG.LieType.Chevalley
