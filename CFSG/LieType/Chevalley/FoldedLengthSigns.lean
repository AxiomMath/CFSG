module

public import CFSG.LieType.Chevalley.FoldedWeylIdentification

public noncomputable section

namespace CFSG.Blueprint.Chevalley.TwistTag

open CFSG.LieType.Chevalley

variable (t : TwistTag)

@[expose] def orbitLength
    (w : WeylGroup t.tag) : ℕ :=
  sInf {n | ∃ ω : List (Fin t.foldedTag.rank), ω.length = n ∧ (ω.map t.orbitReflection).prod = w}

theorem list_prod_orbitReflection_mem
    (ω : List (Fin t.foldedTag.rank)) :
    (ω.map t.orbitReflection).prod ∈ relWeylTwist t :=
  Subgroup.list_prod_mem _ fun _ hx => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    exact t.orbitReflection_mem a

end CFSG.Blueprint.Chevalley.TwistTag

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (t : TwistTag)

theorem foldedWeylEquiv_list_prod
    (ω : List (Fin t.foldedTag.rank)) :
    foldedWeylEquiv t ⟨(ω.map t.orbitReflection).prod, t.list_prod_orbitReflection_mem ω⟩ =
      (coxeterSystem t.foldedTag).wordProd ω := by
  induction ω with
  | nil => exact map_one _
  | cons a ω ih =>
    have h : (⟨((a :: ω).map t.orbitReflection).prod, t.list_prod_orbitReflection_mem _⟩ :
        relWeylTwist t) = ⟨t.orbitReflection a, t.orbitReflection_mem a⟩ *
          ⟨(ω.map t.orbitReflection).prod, t.list_prod_orbitReflection_mem ω⟩ :=
      Subtype.ext (show ((a :: ω).map t.orbitReflection).prod =
        t.orbitReflection a * (ω.map t.orbitReflection).prod by
          rw [List.map_cons, List.prod_cons])
    rw [h, map_mul, foldedWeylEquiv_orbitReflection, ih, CoxeterSystem.wordProd_cons]

theorem orbitLength_eq
    (w : relWeylTwist t) :
    t.orbitLength w = (coxeterSystem t.foldedTag).length (foldedWeylEquiv t w) := by
  have key : ∀ ω : List (Fin t.foldedTag.rank), (ω.map t.orbitReflection).prod = w ↔
      (coxeterSystem t.foldedTag).wordProd ω = foldedWeylEquiv t w := fun ω => by
    rw [← foldedWeylEquiv_list_prod t ω, (foldedWeylEquiv t).injective.eq_iff, Subtype.ext_iff]
  obtain ⟨ω, hω, hprod⟩ := (coxeterSystem t.foldedTag).exists_isReduced (foldedWeylEquiv t w)
  have hmem : ω.length ∈ {n | ∃ ω : List (Fin t.foldedTag.rank), ω.length = n ∧
      (ω.map t.orbitReflection).prod = w} := ⟨ω, rfl, (key ω).2 hprod.symm⟩
  refine le_antisymm ?_ ?_
  · rw [hprod, hω.eq]
    exact Nat.sInf_le hmem
  · obtain ⟨ω', hω', hprod'⟩ := Nat.sInf_mem ⟨_, hmem⟩
    rw [TwistTag.orbitLength, ← hω', ← (key ω').1 hprod']
    exact (coxeterSystem t.foldedTag).length_wordProd_le ω'

theorem orbitLength_inv
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t) :
    t.orbitLength w⁻¹ = t.orbitLength w := by
  rw [show w⁻¹ = ((⟨w, hw⟩⁻¹ : relWeylTwist t) : WeylGroup t.tag) from rfl,
    orbitLength_eq, map_inv, CoxeterSystem.length_inv, ← orbitLength_eq]

theorem height_foldedWeylEquiv_smul_single_pos
    (w : relWeylTwist t) {a : Fin t.foldedTag.rank}
    (hpos : ∀ i ∈ t.orbit a, 0 < height ((w : WeylGroup t.tag) • (Pi.single i 1 :
      Fin t.tag.rank → ℤ))) :
    0 < height (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)) := by
  have hu := IsRoot.smul (isRoot_single t.foldedTag a) (foldedWeylEquiv t w)
  have hθ : t.foldMap (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)) =
      ∑ i ∈ t.orbit a, (w : WeylGroup t.tag) • (Pi.single i 1 : Fin t.tag.rank → ℤ) := by
    rw [← smul_foldMap_foldedWeylEquiv, t.foldMap_single, TwistTag.orbitSum, Finset.smul_sum]
  refine (IsRoot.height_pos_iff hu).2 fun b => ?_
  obtain ⟨j, rfl⟩ := t.exists_orbitIndex_eq b
  rw [← t.foldMap_apply_apply (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)),
    hθ, Finset.sum_apply]
  exact Finset.sum_nonneg fun i hi =>
    (IsRoot.height_pos_iff (IsRoot.smul (isRoot_single _ i) _)).1 (hpos i hi) j

theorem height_foldedWeylEquiv_smul_single_neg
    (w : relWeylTwist t) {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height ((w : WeylGroup t.tag) • (Pi.single i 1 :
      Fin t.tag.rank → ℤ)) < 0) :
    height (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)) < 0 := by
  have hu := IsRoot.smul (isRoot_single t.foldedTag a) (foldedWeylEquiv t w)
  have hθ : t.foldMap (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)) =
      ∑ i ∈ t.orbit a, (w : WeylGroup t.tag) • (Pi.single i 1 : Fin t.tag.rank → ℤ) := by
    rw [← smul_foldMap_foldedWeylEquiv, t.foldMap_single, TwistTag.orbitSum, Finset.smul_sum]
  refine (IsRoot.height_neg_iff hu).2 fun b => ?_
  obtain ⟨j, rfl⟩ := t.exists_orbitIndex_eq b
  rw [← t.foldMap_apply_apply (foldedWeylEquiv t w • (Pi.single a 1 : Fin t.foldedTag.rank → ℤ)),
    hθ, Finset.sum_apply]
  exact Finset.sum_nonpos fun i hi =>
    (IsRoot.height_neg_iff (IsRoot.smul (isRoot_single _ i) _)).1 (hneg i hi) j

theorem foldedWeylEquiv_mul_orbitReflection
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (a : Fin t.foldedTag.rank) :
    foldedWeylEquiv t ⟨w * t.orbitReflection a, mul_mem hw (t.orbitReflection_mem a)⟩ =
      foldedWeylEquiv t ⟨w, hw⟩ * simple t.foldedTag a := by
  rw [← foldedWeylEquiv_orbitReflection t a, ← map_mul]
  rfl

theorem length_mul_orbitReflection_of_pos
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {a : Fin t.foldedTag.rank}
    (hpos : ∀ i ∈ t.orbit a, 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ))) :
    t.orbitLength (w * t.orbitReflection a) = t.orbitLength w + 1 ∧
      (coxeterSystem t.tag).length (w * t.orbitReflection a) =
        (coxeterSystem t.tag).length w + (t.orbit a).card := by
  refine ⟨?_, ?_⟩
  · have h₁ := orbitLength_eq t ⟨w * t.orbitReflection a, mul_mem hw (t.orbitReflection_mem a)⟩
    have h₂ := orbitLength_eq t ⟨w, hw⟩
    rw [foldedWeylEquiv_mul_orbitReflection] at h₁
    change t.orbitLength (w * t.orbitReflection a) = _ at h₁
    change t.orbitLength w = _ at h₂
    rw [h₁, h₂]
    refine (not_isRightDescent_iff_length _ a).1 fun hd => ?_
    have h := ((smul_single_mem_negRoots_iff _ a).2 hd).2
    have := height_foldedWeylEquiv_smul_single_pos t ⟨w, hw⟩ hpos
    omega
  · rw [← t.length_orbitWord]
    exact length_mul_wordProd_of_pos (t.nodup_orbitWord a)
      (fun _ hi _ hj => t.cartan_eq_zero_of_mem_orbitWord hi hj)
      fun i hi => hpos i ((t.mem_orbitWord).1 hi)

theorem length_mul_orbitReflection_of_neg
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    t.orbitLength (w * t.orbitReflection a) + 1 = t.orbitLength w ∧
      (coxeterSystem t.tag).length (w * t.orbitReflection a) + (t.orbit a).card =
        (coxeterSystem t.tag).length w := by
  refine ⟨?_, ?_⟩
  · have h₁ := orbitLength_eq t ⟨w * t.orbitReflection a, mul_mem hw (t.orbitReflection_mem a)⟩
    have h₂ := orbitLength_eq t ⟨w, hw⟩
    rw [foldedWeylEquiv_mul_orbitReflection] at h₁
    change t.orbitLength (w * t.orbitReflection a) = _ at h₁
    change t.orbitLength w = _ at h₂
    rw [h₁, h₂]
    exact (isRightDescent_iff_length _ a).1 ((smul_single_mem_negRoots_iff _ a).1
      ⟨IsRoot.smul (isRoot_single _ a) _, height_foldedWeylEquiv_smul_single_neg t ⟨w, hw⟩ hneg⟩)
  · rw [← t.length_orbitWord]
    exact length_mul_wordProd_add_length (t.nodup_orbitWord a)
      (fun _ hi _ hj => t.cartan_eq_zero_of_mem_orbitWord hi hj)
      fun i hi => hneg i ((t.mem_orbitWord).1 hi)

theorem inv_orbitReflection_mul
    (w : WeylGroup t.tag) (a : Fin t.foldedTag.rank) :
    (t.orbitReflection a * w)⁻¹ = w⁻¹ * t.orbitReflection a := by
  rw [mul_inv_rev, t.orbitReflection_inv]

theorem length_orbitReflection_mul_of_pos
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {a : Fin t.foldedTag.rank}
    (hpos : ∀ i ∈ t.orbit a, 0 < height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ))) :
    t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1 ∧
      (coxeterSystem t.tag).length (t.orbitReflection a * w) =
        (coxeterSystem t.tag).length w + (t.orbit a).card := by
  have hmem := mul_mem (t.orbitReflection_mem a) hw
  obtain ⟨h₁, h₂⟩ := length_mul_orbitReflection_of_pos t (inv_mem hw) hpos
  rw [← inv_orbitReflection_mul, orbitLength_inv t hmem, orbitLength_inv t hw] at h₁
  rw [← inv_orbitReflection_mul, CoxeterSystem.length_inv, CoxeterSystem.length_inv] at h₂
  exact ⟨h₁, h₂⟩

theorem length_orbitReflection_mul_of_neg
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    {a : Fin t.foldedTag.rank}
    (hneg : ∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) :
    t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w ∧
      (coxeterSystem t.tag).length (t.orbitReflection a * w) + (t.orbit a).card =
        (coxeterSystem t.tag).length w := by
  have hmem := mul_mem (t.orbitReflection_mem a) hw
  obtain ⟨h₁, h₂⟩ := length_mul_orbitReflection_of_neg t (inv_mem hw) hneg
  rw [← inv_orbitReflection_mul, orbitLength_inv t hmem, orbitLength_inv t hw] at h₁
  rw [← inv_orbitReflection_mul, CoxeterSystem.length_inv, CoxeterSystem.length_inv] at h₂
  exact ⟨h₁, h₂⟩

theorem exists_forall_height_smul_single_neg
    {w : WeylGroup t.tag} (hw : w ∈ relWeylTwist t)
    (h1 : w ≠ 1) :
    ∃ a, ∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 := by
  obtain ⟨i, hi⟩ := exists_height_neg_of_ne_one h1
  exact ⟨t.orbitIndex i, fun j hj => by
    rw [height_smul_single_of_orbitIndex_eq t hw ((t.mem_orbit_iff).1 hj)]
    exact hi⟩

theorem fixed_Weyl_length_signs
    (t : TwistTag) :
    (∀ w : relWeylTwist t,
      t.orbitLength w = (coxeterSystem t.foldedTag).length (foldedWeylEquiv t w)) ∧
    (∀ w ∈ relWeylTwist t, ∀ a, ∀ i ∈ t.orbit a, ∀ j ∈ t.orbit a,
      (0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) ↔
        0 < height (w • (Pi.single j 1 : Fin t.tag.rank → ℤ)))) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      (∀ i ∈ t.orbit a, 0 < height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ))) →
        t.orbitLength (w * t.orbitReflection a) = t.orbitLength w + 1 ∧
        (coxeterSystem t.tag).length (w * t.orbitReflection a) =
          (coxeterSystem t.tag).length w + (t.orbit a).card) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      (∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) →
        t.orbitLength (w * t.orbitReflection a) + 1 = t.orbitLength w ∧
        (coxeterSystem t.tag).length (w * t.orbitReflection a) + (t.orbit a).card =
          (coxeterSystem t.tag).length w) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      (∀ i ∈ t.orbit a, 0 < height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ))) →
        t.orbitLength (t.orbitReflection a * w) = t.orbitLength w + 1 ∧
        (coxeterSystem t.tag).length (t.orbitReflection a * w) =
          (coxeterSystem t.tag).length w + (t.orbit a).card) ∧
    (∀ w ∈ relWeylTwist t, ∀ a,
      (∀ i ∈ t.orbit a, height (w⁻¹ • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0) →
        t.orbitLength (t.orbitReflection a * w) + 1 = t.orbitLength w ∧
        (coxeterSystem t.tag).length (t.orbitReflection a * w) + (t.orbit a).card =
          (coxeterSystem t.tag).length w) ∧
    (∀ w ∈ relWeylTwist t, t.orbitLength w⁻¹ = t.orbitLength w) ∧
    ∀ w ∈ relWeylTwist t, w ≠ 1 →
      ∃ a, ∀ i ∈ t.orbit a, height (w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) < 0 :=
  ⟨orbitLength_eq t,
    fun w hw a i hi j hj => by
      rw [height_smul_single_of_orbitIndex_eq t hw (((t.mem_orbit_iff).1 hi).trans
        ((t.mem_orbit_iff).1 hj).symm)],
    fun _ hw _ hpos => length_mul_orbitReflection_of_pos t hw hpos,
    fun _ hw _ hneg => length_mul_orbitReflection_of_neg t hw hneg,
    fun _ hw _ hpos => length_orbitReflection_mul_of_pos t hw hpos,
    fun _ hw _ hneg => length_orbitReflection_mul_of_neg t hw hneg,
    fun _ hw => orbitLength_inv t hw,
    fun _ hw h1 => exists_forall_height_smul_single_neg t hw h1⟩

end CFSG.LieType.Chevalley
