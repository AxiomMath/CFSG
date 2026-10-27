module

public import CFSG.LieType.Chevalley.GraphFixedRootBruhat
public import CFSG.LieType.Chevalley.GraphFixedRankOneBruhat
public import CFSG.LieType.Chevalley.GraphFixedSimpleComplement

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem exists_canonicalRep_mul_eq
    {v w : WeylGroup t.tag} (hv : v ∈ relWeylTwist t)
    (hw : w ∈ relWeylTwist t) :
    ∃ h ∈ graphFixedRootTorus t K σ,
      canonicalRep (coxeterSystem t.tag) K v * canonicalRep (coxeterSystem t.tag) K w =
        canonicalRep (coxeterSystem t.tag) K (v * w) * h := by
  have hker : (⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ (mul_mem hv hw)⟩ :
      graphFixedRootMonomial t K σ)⁻¹ *
        (⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ hv⟩ *
          ⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ hw⟩) ∈
      (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      graphFixedRootWeylHom_canonicalRep t K σ (mul_mem hv hw),
      graphFixedRootWeylHom_canonicalRep t K σ hv, graphFixedRootWeylHom_canonicalRep t K σ hw,
      inv_mul_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  refine ⟨_, hker, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

theorem exists_canonicalRep_inv_eq
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    ∃ h ∈ graphFixedRootTorus t K σ,
      (canonicalRep (coxeterSystem t.tag) K w)⁻¹ =
        canonicalRep (coxeterSystem t.tag) K w⁻¹ * h := by
  have hker : (⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ (inv_mem hw)⟩ :
      graphFixedRootMonomial t K σ)⁻¹ *
        (⟨_, canonicalRep_mem_graphFixedRootMonomial t K σ hw⟩ :
          graphFixedRootMonomial t K σ)⁻¹ ∈ (graphFixedRootWeylHom t K σ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_inv,
      graphFixedRootWeylHom_canonicalRep t K σ (inv_mem hw),
      graphFixedRootWeylHom_canonicalRep t K σ hw, inv_inv, mul_inv_cancel]
  rw [graphFixedRootWeylHom_ker, Subgroup.mem_subgroupOf] at hker
  refine ⟨_, hker, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]

theorem mul_canonicalRep_mul_mem_graphFixedRootBruhatCell
    {w : WeylGroup t.tag}
    {b b' : ModGL t.tag K} (hb : b ∈ graphFixedRootBorel t K σ)
    (hb' : b' ∈ graphFixedRootBorel t K σ) :
    b * canonicalRep (coxeterSystem t.tag) K w * b' ∈ graphFixedRootBruhatCell t K σ w :=
  mem_graphFixedRootBruhatCell.2 ⟨b, hb, b', hb', rfl⟩

theorem inv_subset_graphFixedRootBruhatCell
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    (graphFixedRootBruhatCell t K σ w)⁻¹ ⊆ graphFixedRootBruhatCell t K σ w⁻¹ := by
  intro x hx
  rw [Set.mem_inv] at hx
  obtain ⟨b, hb, b', hb', hx⟩ := mem_graphFixedRootBruhatCell.1 hx
  obtain ⟨h, hh, hinv⟩ := exists_canonicalRep_inv_eq (K := K) (σ := σ) hw
  have e : x = b'⁻¹ * canonicalRep (coxeterSystem t.tag) K w⁻¹ * (h * b⁻¹) := by
    rw [← inv_inv x, ← hx, mul_inv_rev, mul_inv_rev, hinv]
    group
  rw [e]
  exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (inv_mem hb')
    (mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh) (inv_mem hb))

theorem inv_graphFixedRootBruhatCell
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    (graphFixedRootBruhatCell t K σ w)⁻¹ = graphFixedRootBruhatCell t K σ w⁻¹ := by
  refine Set.Subset.antisymm (inv_subset_graphFixedRootBruhatCell hw) fun x hx => ?_
  have h := inv_subset_graphFixedRootBruhatCell (K := K) (σ := σ) (inv_mem hw)
  rw [inv_inv] at h
  exact Set.mem_inv.2 (h (Set.inv_mem_inv.2 hx))

theorem canonicalRep_inv_mul_mul_mem_graphFixedRootBorel
    {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α)
    (hpos : ∀ α ∈ S, 0 < height (w⁻¹ • α)) {g : ModGL t.tag K}
    (hg : g ∈ rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) :
    (canonicalRep (coxeterSystem t.tag) K w)⁻¹ * g * canonicalRep (coxeterSystem t.tag) K w ∈
      graphFixedRootBorel t K σ := by
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
  refine graphFixedPosUnipotent_le_graphFixedRootBorel (Subgroup.mem_inf.2 ⟨rootSpan_mono ?_ hy,
    hyΓ⟩)
  rintro _ ⟨α, hα, rfl⟩
  exact ⟨IsRoot.smul (hS α hα) w⁻¹, hpos α hα⟩

theorem forall_height_pos_or_forall_height_neg
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) :
    (∀ i ∈ t.orbit a, 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ))) ∨
      ∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 := by
  have h : ∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) =
      height (w • (Pi.single (t.orbitMin a) 1 : Fin t.tag.rank → ℤ)) := fun i hi =>
    height_smul_single_of_orbitIndex_eq t hw (((t.mem_orbit_iff).1 hi).trans
      ((t.mem_orbit_iff).1 (t.orbitMin_mem a)).symm)
  rcases height_smul_single_pos_or_neg w (t.orbitMin a) with hp | hn
  · exact Or.inl fun i hi => (h i hi).symm ▸ hp
  · exact Or.inr fun i hi => (h i hi).symm ▸ hn

variable (hσ : Function.Surjective σ)
include hσ

theorem exists_canonicalRep_orbitReflection_mul_eq
    (a : Fin t.foldedTag.rank) {b : ModGL t.tag K}
    (hb : b ∈ graphFixedRootBorel t K σ) :
    ∃ b' ∈ graphFixedRootBorel t K σ, ∃ c : orbitField t K σ a,
      canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b =
        b' * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a c : ModGL t.tag K) := by
  set N := canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a)
  have hb' : b ∈ (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := hb
  rw [graphFixedRootBorel_eq_mul hσ] at hb'
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  obtain ⟨v, hv, c, rfl⟩ := exists_mul_orbitX_eq hσ a hu
  have hh' : N * h * N⁻¹ ∈ graphFixedRootTorus t K σ :=
    (Subgroup.mem_normalizer_iff.1
      (canonicalRep_orbitReflection_mem_normalizer_graphFixedRootTorus (σ := σ) a) h).1 hh
  have hv' : N * v * N⁻¹ ∈ graphFixedSimpleComplement t K σ a :=
    (Subgroup.mem_normalizer_iff.1
      (canonicalRep_orbitReflection_mem_normalizer_graphFixedSimpleComplement (σ := σ) a) v).1 hv
  refine ⟨(N * h * N⁻¹) * (N * v * N⁻¹), mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh')
    (graphFixedPosUnipotent_le_graphFixedRootBorel (graphFixedSimpleComplement_le a hv')), c, ?_⟩
  group

theorem exists_of_mem_mul_graphFixedRootBruhatCell
    (a : Fin t.foldedTag.rank) {w : WeylGroup t.tag}
    {g : ModGL t.tag K}
    (hg : g ∈ graphFixedRootBruhatCell t K σ (t.orbitReflection a) *
      graphFixedRootBruhatCell t K σ w) :
    ∃ b ∈ graphFixedRootBorel t K σ, ∃ c : orbitField t K σ a, ∃ b' ∈ graphFixedRootBorel t K σ,
      b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w * b' = g := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.1 hg
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := mem_graphFixedRootBruhatCell.1 hy
  obtain ⟨b', hb', c, hc⟩ := exists_canonicalRep_orbitReflection_mul_eq hσ a (mul_mem hb₂ hb₃)
  refine ⟨b₁ * b', mul_mem hb₁ hb', c, b₄, hb₄, ?_⟩
  have e : b₁ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * b₂ *
      (b₃ * canonicalRep (coxeterSystem t.tag) K w * b₄) =
      b₁ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * (b₂ * b₃)) *
        canonicalRep (coxeterSystem t.tag) K w * b₄ := by group
  rw [e, hc]
  group

omit hσ

theorem graphFixedRootBruhatCell_mul_subset
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    graphFixedRootBruhatCell t K σ (t.orbitReflection a * w) ⊆
      graphFixedRootBruhatCell t K σ (t.orbitReflection a) * graphFixedRootBruhatCell t K σ w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
  obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ) (t.orbitReflection_mem a) hw
  refine Set.mem_mul.2 ⟨b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * 1,
    mul_canonicalRep_mul_mem_graphFixedRootBruhatCell hb (one_mem _),
    1 * canonicalRep (coxeterSystem t.tag) K w * (h⁻¹ * b'),
    mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (one_mem _)
      (mul_mem (inv_mem (graphFixedRootTorus_le_graphFixedRootBorel hh)) hb'), ?_⟩
  rw [eq_mul_inv_iff_mul_eq.2 hrep.symm]
  group

include hσ

theorem mul_graphFixedRootBruhatCell_of_pos
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t)
    (hpos : ∀ i ∈ t.orbit a, 0 < height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ))) :
    graphFixedRootBruhatCell t K σ (t.orbitReflection a) * graphFixedRootBruhatCell t K σ w =
      graphFixedRootBruhatCell t K σ (t.orbitReflection a * w) := by
  refine Set.Subset.antisymm (fun g hg => ?_) (graphFixedRootBruhatCell_mul_subset hw)
  obtain ⟨b, hb, c, b', hb', rfl⟩ := exists_of_mem_mul_graphFixedRootBruhatCell hσ a hg
  obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ) (t.orbitReflection_mem a) hw
  have hx := canonicalRep_inv_mul_mul_mem_graphFixedRootBorel (σ := σ) hw
    (S := simpleOrbitRoots t a) (fun α hα => (simpleOrbitRoots_pos a α hα).1)
    (by rintro _ ⟨i, hi, rfl⟩; exact hpos i hi) (orbitX_mem t σ a c)
  have e : b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
      (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w * b' =
      b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * w) *
        (h * ((canonicalRep (coxeterSystem t.tag) K w)⁻¹ * (orbitX t K σ a c : ModGL t.tag K) *
          canonicalRep (coxeterSystem t.tag) K w) * b') := by
    rw [eq_mul_inv_iff_mul_eq.2 hrep.symm]
    group
  rw [e]
  exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell hb
    (mul_mem (mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh) hx) hb')

theorem mul_graphFixedRootBruhatCell_of_neg
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t)
    (hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    graphFixedRootBruhatCell t K σ (t.orbitReflection a) * graphFixedRootBruhatCell t K σ w =
      graphFixedRootBruhatCell t K σ (t.orbitReflection a * w) ∪
        graphFixedRootBruhatCell t K σ w := by
  have key : ∀ u : (orbitField t K σ a)ˣ, ∃ β ∈ graphFixedRootBorel t K σ,
      ∃ β' ∈ graphFixedRootBorel t K σ,
        canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
            (orbitX t K σ a u : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w =
          β * canonicalRep (coxeterSystem t.tag) K w * β' := by
    intro u
    obtain ⟨-, -, b, hb, hbid⟩ := (fixed_simple_rank_one_Bruhat_identity t K σ).2 a u
    have hy := canonicalRep_inv_mul_mul_mem_graphFixedRootBorel (σ := σ) hw
      (S := (fun i => -(Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a))
      (by rintro _ ⟨i, -, rfl⟩; exact isRoot_neg_single _ i)
      (by rintro _ ⟨i, hi, rfl⟩; rw [smul_neg, height_neg]; linarith [hneg i hi])
      (orbitYEquiv t σ a (Multiplicative.ofAdd
        ((u⁻¹ : (orbitField t K σ a)ˣ) : orbitField t K σ a))).2
    rw [coe_orbitYEquiv] at hy
    refine ⟨b, hb, _, hy, ?_⟩
    rw [hbid]
    group
  refine Set.Subset.antisymm (fun g hg => ?_) (Set.union_subset
    (graphFixedRootBruhatCell_mul_subset hw) fun x hx => ?_)
  · obtain ⟨b, hb, c, b', hb', rfl⟩ := exists_of_mem_mul_graphFixedRootBruhatCell hσ a hg
    by_cases hc : c = 0
    · subst hc
      refine Or.inl ?_
      obtain ⟨h, hh, hrep⟩ := exists_canonicalRep_mul_eq (K := K) (σ := σ)
        (t.orbitReflection_mem a) hw
      have e : b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a 0 : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w * b' =
          b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a * w) * (h * b') := by
        rw [orbitX_zero, Subgroup.coe_one, mul_one, eq_mul_inv_iff_mul_eq.2 hrep.symm]
        group
      rw [e]
      exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell hb
        (mul_mem (graphFixedRootTorus_le_graphFixedRootBorel hh) hb')
    · refine Or.inr ?_
      obtain ⟨β, hβ, β', hβ', hββ'⟩ := key (Units.mk0 c hc)
      rw [Units.val_mk0] at hββ'
      have e : b * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w * b' =
          b * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
            (orbitX t K σ a c : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w) * b' := by
        group
      rw [e, hββ']
      have e' : b * (β * canonicalRep (coxeterSystem t.tag) K w * β') * b' =
          (b * β) * canonicalRep (coxeterSystem t.tag) K w * (β' * b') := by group
      rw [e']
      exact mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (mul_mem hb hβ) (mul_mem hβ' hb')
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_graphFixedRootBruhatCell.1 hx
    obtain ⟨β, hβ, β', hβ', hββ'⟩ := key 1
    have hx1 := orbitX_mem_graphFixedPosUnipotent t σ a
      ((1 : (orbitField t K σ a)ˣ) : orbitField t K σ a)
    refine Set.mem_mul.2 ⟨b * β⁻¹ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * 1,
      mul_canonicalRep_mul_mem_graphFixedRootBruhatCell (mul_mem hb (inv_mem hβ)) (one_mem _),
      (orbitX t K σ a ((1 : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) *
        canonicalRep (coxeterSystem t.tag) K w * (β'⁻¹ * b'),
      mul_canonicalRep_mul_mem_graphFixedRootBruhatCell
        (graphFixedPosUnipotent_le_graphFixedRootBorel hx1) (mul_mem (inv_mem hβ') hb'), ?_⟩
    have e : b * β⁻¹ * canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) * 1 *
        ((orbitX t K σ a ((1 : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) *
          canonicalRep (coxeterSystem t.tag) K w * (β'⁻¹ * b')) =
        b * β⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.orbitReflection a) *
          (orbitX t K σ a ((1 : (orbitField t K σ a)ˣ) : orbitField t K σ a) : ModGL t.tag K) *
            canonicalRep (coxeterSystem t.tag) K w) * β'⁻¹ * b' := by group
    rw [e, hββ']
    group

omit hσ

theorem forall_height_inv_smul_pos_of_orbitLength
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) (h : t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1) :
    ∀ i ∈ t.orbit a, 0 < height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) := by
  rcases forall_height_pos_or_forall_height_neg (inv_mem hw) a with hp | hn
  · exact hp
  · have := (length_orbitReflection_mul_of_neg t hw hn).1
    omega

theorem forall_height_inv_smul_neg_of_orbitLength
    {a : Fin t.foldedTag.rank} {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) (h : t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w) :
    ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 := by
  rcases forall_height_pos_or_forall_height_neg (inv_mem hw) a with hp | hn
  · have := (length_orbitReflection_mul_of_pos t hw hp).1
    omega
  · exact hn

include hσ

theorem graphFixedRootBruhatCell_mul_of_orbitLength_eq_add_one
    {a : Fin t.foldedTag.rank}
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (h : t.orbitLength (w * t.orbitReflection a) = t.orbitLength w + 1) :
    graphFixedRootBruhatCell t K σ w * graphFixedRootBruhatCell t K σ (t.orbitReflection a) =
      graphFixedRootBruhatCell t K σ (w * t.orbitReflection a) := by
  have hr := t.orbitReflection_mem a
  have hwr : w * t.orbitReflection a ∈ relWeylTwist t := mul_mem hw hr
  have h' : t.orbitLength (t.orbitReflection a * w⁻¹) = t.orbitLength w⁻¹ + 1 := by
    rw [← t.orbitReflection_inv, ← mul_inv_rev, orbitLength_inv t hwr, orbitLength_inv t hw, h]
  rw [← inv_inv (graphFixedRootBruhatCell t K σ w * _), mul_inv_rev,
    inv_graphFixedRootBruhatCell hr, inv_graphFixedRootBruhatCell hw, t.orbitReflection_inv,
    mul_graphFixedRootBruhatCell_of_pos hσ (inv_mem hw)
      (by simpa using forall_height_inv_smul_pos_of_orbitLength (inv_mem hw) h'),
    inv_graphFixedRootBruhatCell (mul_mem hr (inv_mem hw)), mul_inv_rev, inv_inv,
    t.orbitReflection_inv]

theorem graphFixedRootBruhatCell_mul_of_orbitLength_add_one_eq
    {a : Fin t.foldedTag.rank}
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (h : t.orbitLength (w * t.orbitReflection a) + 1 = t.orbitLength w) :
    graphFixedRootBruhatCell t K σ w * graphFixedRootBruhatCell t K σ (t.orbitReflection a) =
      graphFixedRootBruhatCell t K σ (w * t.orbitReflection a) ∪
        graphFixedRootBruhatCell t K σ w := by
  have hr := t.orbitReflection_mem a
  have hwr : w * t.orbitReflection a ∈ relWeylTwist t := mul_mem hw hr
  have h' : t.orbitLength (t.orbitReflection a * w⁻¹) + 1 = t.orbitLength w⁻¹ := by
    rw [← t.orbitReflection_inv, ← mul_inv_rev, orbitLength_inv t hwr, orbitLength_inv t hw, h]
  rw [← inv_inv (graphFixedRootBruhatCell t K σ w * _), mul_inv_rev,
    inv_graphFixedRootBruhatCell hr, inv_graphFixedRootBruhatCell hw, t.orbitReflection_inv,
    mul_graphFixedRootBruhatCell_of_neg hσ (inv_mem hw)
      (by simpa using forall_height_inv_smul_neg_of_orbitLength (inv_mem hw) h'),
    Set.union_inv, inv_graphFixedRootBruhatCell (mul_mem hr (inv_mem hw)),
    inv_graphFixedRootBruhatCell (inv_mem hw), mul_inv_rev, inv_inv, t.orbitReflection_inv]

omit hσ

theorem fixed_simple_Bruhat_multiplication
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ w ∈ relWeylTwist t, (graphFixedRootBruhatCell t K σ.toRingHom w)⁻¹ =
      graphFixedRootBruhatCell t K σ.toRingHom w⁻¹) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1 →
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
            graphFixedRootBruhatCell t K σ.toRingHom w =
          graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * w)) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w →
        graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) *
            graphFixedRootBruhatCell t K σ.toRingHom w =
          graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a * w) ∪
            graphFixedRootBruhatCell t K σ.toRingHom w) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (w * t.orbitReflection a) = t.orbitLength w + 1 →
        graphFixedRootBruhatCell t K σ.toRingHom w *
            graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) =
          graphFixedRootBruhatCell t K σ.toRingHom (w * t.orbitReflection a)) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      t.orbitLength (w * t.orbitReflection a) + 1 = t.orbitLength w →
        graphFixedRootBruhatCell t K σ.toRingHom w *
            graphFixedRootBruhatCell t K σ.toRingHom (t.orbitReflection a) =
          graphFixedRootBruhatCell t K σ.toRingHom (w * t.orbitReflection a) ∪
            graphFixedRootBruhatCell t K σ.toRingHom w) ∧
    ∀ w ∈ relWeylTwist t, graphFixedRootBruhatCell t K σ.toRingHom w ⊆
      (graphFixedRootGroup t K σ.toRingHom : Set (ModGL t.tag K)) :=
  ⟨fun _ hw => inv_graphFixedRootBruhatCell hw,
    fun _ hw _ h => mul_graphFixedRootBruhatCell_of_pos σ.surjective hw
      (forall_height_inv_smul_pos_of_orbitLength hw h),
    fun _ hw _ h => mul_graphFixedRootBruhatCell_of_neg σ.surjective hw
      (forall_height_inv_smul_neg_of_orbitLength hw h),
    fun _ hw _ h => graphFixedRootBruhatCell_mul_of_orbitLength_eq_add_one σ.surjective hw h,
    fun _ hw _ h => graphFixedRootBruhatCell_mul_of_orbitLength_add_one_eq σ.surjective hw h,
    fun _ hw => graphFixedRootBruhatCell_subset_graphFixedRootGroup hw⟩

end CFSG.LieType.Chevalley
