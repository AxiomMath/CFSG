module

public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.StandardParabolic
public import CFSG.LieType.Chevalley.BorelWeylGeneration

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag}

theorem smul_apply_of_mem_parabolicWeylGroup
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) (v : Fin τ.rank → ℤ) {i : Fin τ.rank} (hi : i ∉ J) :
    (w • v) i = v i := by
  let S : Subgroup (WeylGroup τ) :=
    { carrier := {w | ∀ v : Fin τ.rank → ℤ, ∀ i ∉ J, (w • v) i = v i}
      one_mem' := fun v i _ => by rw [one_smul]
      mul_mem' := fun {a b} ha hb v i hi => by
        rw [mul_smul, ha _ i hi, hb v i hi]
      inv_mem' := fun {a} ha v i hi => by
        have h := ha (a⁻¹ • v) i hi
        rw [smul_inv_smul] at h
        exact h.symm }
  have hle : parabolicWeylGroup τ J ≤ S := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, hj, rfl⟩ v i hi
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    change (simple τ j • v) i = v i
    rw [simple_smul, reflect, Pi.sub_apply, Pi.smul_apply, Pi.single_apply, ite_eq_right hij,
      smul_zero, sub_zero]
  exact hle hw v i hi

theorem simple_mem_parabolicWeylGroup_iff
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} :
    simple τ i ∈ parabolicWeylGroup τ J ↔ i ∈ J := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure ⟨i, h, rfl⟩⟩
  by_contra hi
  have h1 := smul_apply_of_mem_parabolicWeylGroup h (Pi.single i 1) hi
  rw [simple_smul, reflect_single_self] at h1
  simp at h1

variable {K : Type} [Field K]

theorem borelGroup_le_parabolicSubgroup
    (J : Set (Fin τ.rank)) :
    borelGroup τ K ≤ parabolicSubgroup τ K J :=
  le_sup_left

theorem weylElt_mem_parabolicSubgroup
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J) :
    weylElt τ K j 1 ∈ parabolicSubgroup τ K J :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem torusGroup_le_parabolicSubgroup
    (J : Set (Fin τ.rank)) :
    torusGroup τ K ≤ parabolicSubgroup τ K J :=
  le_trans le_sup_left (borelGroup_le_parabolicSubgroup J)

theorem canonicalRep_mem_parabolicSubgroup
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    canonicalRep (coxeterSystem τ) K w ∈ parabolicSubgroup τ K J := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [canonicalRep_simple]
    exact weylElt_mem_parabolicSubgroup hj
  | one =>
    rw [canonicalRep_one]
    exact one_mem _
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk, h⟩ := canonicalRep_mul_mem (R := K) x y
    have e : canonicalRep (coxeterSystem τ) K (x * y) =
        k⁻¹ * (canonicalRep (coxeterSystem τ) K x * canonicalRep (coxeterSystem τ) K y) := by
      rw [h, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem (torusGroup_le_parabolicSubgroup J hk)) (mul_mem hx hy)
  | inv x _ hx =>
    obtain ⟨k, hk, h⟩ := canonicalRep_mul_mem (R := K) x⁻¹ x
    rw [inv_mul_cancel, canonicalRep_one, mul_one] at h
    have e : canonicalRep (coxeterSystem τ) K x⁻¹ = k * (canonicalRep (coxeterSystem τ) K x)⁻¹ := by
      rw [← h, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (torusGroup_le_parabolicSubgroup J hk) (inv_mem hx)

theorem bruhatCell_subset_parabolicSubgroup
    {J : Set (Fin τ.rank)} {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ J) :
    bruhatCell τ K w ⊆ parabolicSubgroup τ K J := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
  exact mul_mem (mul_mem (borelGroup_le_parabolicSubgroup J hb)
    (canonicalRep_mem_parabolicSubgroup hw)) (borelGroup_le_parabolicSubgroup J hb')

variable (τ K) in
@[expose] def parabolicCells
    (J : Set (Fin τ.rank)) : Set (ModGL τ K) :=
  ⋃ w ∈ parabolicWeylGroup τ J, bruhatCell τ K w

theorem mem_parabolicCells
    {J : Set (Fin τ.rank)} {x : ModGL τ K} :
    x ∈ parabolicCells τ K J ↔ ∃ w ∈ parabolicWeylGroup τ J, x ∈ bruhatCell τ K w := by
  simp only [parabolicCells, Set.mem_iUnion, exists_prop]

theorem borel_mul_mem_parabolicCells
    {J : Set (Fin τ.rank)} {b x : ModGL τ K}
    (hb : b ∈ borelGroup τ K) (hx : x ∈ parabolicCells τ K J) : b * x ∈ parabolicCells τ K J := by
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hx
  exact mem_parabolicCells.2 ⟨w, hw, mem_bruhatCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂, by group⟩⟩

theorem weylElt_mul_mem_parabolicCells
    {J : Set (Fin τ.rank)} {j : Fin τ.rank} (hj : j ∈ J)
    {x : ModGL τ K} (hx : x ∈ parabolicCells τ K J) :
    weylElt τ K j 1 * x ∈ parabolicCells τ K J := by
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 hx
  have hsw : simple τ j * w ∈ parabolicWeylGroup τ J :=
    mul_mem (Subgroup.subset_closure ⟨j, hj, rfl⟩) hw
  have hn : weylElt τ K j 1 ∈ bruhatCell τ K (simple τ j) := by
    rw [← canonicalRep_simple (coxeterSystem τ) K j]
    exact canonicalRep_mem_bruhatCell _
  have hmem : weylElt τ K j 1 * x ∈ bruhatCell τ K (simple τ j) * bruhatCell τ K w :=
    Set.mul_mem_mul hn hx
  obtain ⟨hadd, hsub, -⟩ := simple_bruhat_multiplication τ K
  rcases (coxeterSystem τ).length_simple_mul w j with h | h
  · rw [hadd j w h] at hmem
    exact mem_parabolicCells.2 ⟨_, hsw, hmem⟩
  · have h' : (coxeterSystem τ).length (simple τ j * w) + 1 = (coxeterSystem τ).length w := h
    rw [hsub j w (by omega)] at hmem
    rcases hmem with hmem | hmem
    · exact mem_parabolicCells.2 ⟨_, hsw, hmem⟩
    · exact mem_parabolicCells.2 ⟨w, hw, hmem⟩

theorem parabolicSubgroup_subset_parabolicCells
    (J : Set (Fin τ.rank)) :
    (parabolicSubgroup τ K J : Set (ModGL τ K)) ⊆ parabolicCells τ K J := by
  let M : Subgroup (ModGL τ K) :=
    { carrier := {g | (∀ x ∈ parabolicCells τ K J, g * x ∈ parabolicCells τ K J) ∧
        ∀ x ∈ parabolicCells τ K J, g⁻¹ * x ∈ parabolicCells τ K J}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBM : borelGroup τ K ≤ M := fun b hb =>
    ⟨fun x hx => borel_mul_mem_parabolicCells hb hx,
      fun x hx => borel_mul_mem_parabolicCells (inv_mem hb) hx⟩
  have hnM : ∀ j ∈ J, weylElt τ K j 1 ∈ M := fun j hj => by
    refine ⟨fun x hx => weylElt_mul_mem_parabolicCells hj hx, fun x hx => ?_⟩
    have hsq := weylElt_one_sq (τ := τ) (R := K) j
    have e : (weylElt τ K j 1)⁻¹ = weylElt τ K j 1 * (torusElt τ K j (-1))⁻¹ := by
      rw [← hsq, sq, mul_inv_rev, mul_inv_cancel_left]
    have hd : (torusElt τ K j (-1))⁻¹ ∈ borelGroup τ K :=
      inv_mem (Subgroup.mem_sup_left (torusElt_mem_torusGroup j (-1)))
    rw [e, mul_assoc]
    exact weylElt_mul_mem_parabolicCells hj (borel_mul_mem_parabolicCells hd hx)
  have hle : parabolicSubgroup τ K J ≤ M :=
    sup_le hBM ((Subgroup.closure_le _).2 fun _ ⟨j, hj, he⟩ => he ▸ hnM j hj)
  intro g hg
  have h1 : (1 : ModGL τ K) ∈ parabolicCells τ K J :=
    mem_parabolicCells.2 ⟨1, one_mem _, one_mem_bruhatCell_one⟩
  simpa using (hle hg).1 1 h1

theorem parabolicSubgroup_eq_parabolicCells
    (J : Set (Fin τ.rank)) :
    (parabolicSubgroup τ K J : Set (ModGL τ K)) = parabolicCells τ K J := by
  refine Set.Subset.antisymm (parabolicSubgroup_subset_parabolicCells J) fun x hx => ?_
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 hx
  exact bruhatCell_subset_parabolicSubgroup hw hx

theorem weylElt_mem_parabolicSubgroup_iff
    {J : Set (Fin τ.rank)} {i : Fin τ.rank} :
    weylElt τ K i 1 ∈ parabolicSubgroup τ K J ↔ i ∈ J := by
  refine ⟨fun h => ?_, weylElt_mem_parabolicSubgroup⟩
  have h' : weylElt τ K i 1 ∈ parabolicCells τ K J := by
    rw [← parabolicSubgroup_eq_parabolicCells]
    exact h
  obtain ⟨w, hw, hx⟩ := mem_parabolicCells.1 h'
  have hn : weylElt τ K i 1 ∈ bruhatCell τ K (simple τ i) := by
    rw [← canonicalRep_simple (coxeterSystem τ) K i]
    exact canonicalRep_mem_bruhatCell _
  by_cases hwi : w = simple τ i
  · rw [hwi] at hw
    exact simple_mem_parabolicWeylGroup_iff.1 hw
  · exact absurd hn (Set.disjoint_left.1 (disjoint_bruhatCell (K := K) hwi) hx)

variable (τ K) in
theorem standard_parabolic_cells :
    (∀ J : Set (Fin τ.rank), (parabolicSubgroup τ K J : Set (ModGL τ K)) =
      ⋃ w ∈ parabolicWeylGroup τ J, bruhatCell τ K w) ∧
    (∀ w w' : WeylGroup τ, w ≠ w' → Disjoint (bruhatCell τ K w) (bruhatCell τ K w')) ∧
    (∀ (J : Set (Fin τ.rank)) (i : Fin τ.rank),
      weylElt τ K i 1 ∈ parabolicSubgroup τ K J ↔ i ∈ J) ∧
    (∀ J J' : Set (Fin τ.rank), parabolicSubgroup τ K J ≤ parabolicSubgroup τ K J' ↔ J ⊆ J') ∧
    parabolicSubgroup τ K ∅ = borelGroup τ K ∧
    parabolicSubgroup τ K Set.univ = adjointGroup τ K ∧
    ∀ [Finite K] (J : Set (Fin τ.rank)),
      Nat.card (parabolicSubgroup τ K J) = Nat.card (torusGroup τ K) *
        Nat.card K ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard *
          ∑ᶠ w : parabolicWeylGroup τ J, Nat.card K ^ (coxeterSystem τ).length w := by
  refine ⟨fun J => parabolicSubgroup_eq_parabolicCells J, fun w w' h => disjoint_bruhatCell h,
    fun J i => weylElt_mem_parabolicSubgroup_iff, fun J J' => ⟨fun h j hj => ?_, fun h => ?_⟩,
    ?_, ?_, fun J => ?_⟩
  · exact weylElt_mem_parabolicSubgroup_iff.1 (h (weylElt_mem_parabolicSubgroup hj))
  · exact sup_le_sup_left (Subgroup.closure_mono (Set.image_mono h)) _
  · simp [parabolicSubgroup]
  · rw [(borel_weyl_generation τ K).1, parabolicSubgroup, Set.image_univ]
  · classical
    have : Fintype (WeylGroup τ) := Fintype.ofFinite _
    have : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
    have e : (parabolicSubgroup τ K J : Set (ModGL τ K)) ≃
        Σ w : parabolicWeylGroup τ J, bruhatCell τ K w := by
      have hU : parabolicCells τ K J = ⋃ w : parabolicWeylGroup τ J, bruhatCell τ K w := by
        ext x
        simp only [parabolicCells, Set.mem_iUnion, exists_prop, Subtype.exists]
      rw [parabolicSubgroup_eq_parabolicCells, hU]
      exact Set.unionEqSigmaOfDisjoint fun w w' h =>
        disjoint_bruhatCell fun h' => h (Subtype.ext h')
    calc Nat.card (parabolicSubgroup τ K J) =
          Nat.card (Σ w : parabolicWeylGroup τ J, bruhatCell τ K w) := Nat.card_congr e
      _ = ∑ w : parabolicWeylGroup τ J, Nat.card (bruhatCell τ K w) := Nat.card_sigma
      _ = _ := by
        rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [card_bruhatCell, pow_add, mul_assoc]

end CFSG.LieType.Chevalley
