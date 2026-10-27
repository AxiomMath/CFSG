module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K] {A : Set (Fin τ.rank)}

theorem exists_mul_canonicalRep_eq_subsystem
    {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ A)
    (hpos : 0 < height (w⁻¹ • α)) {g : ModGL τ K} (hg : g ∈ rootSubgroup τ K α) :
    ∃ b ∈ subsystemBorel τ K A,
      g * canonicalRep (coxeterSystem τ) K w = canonicalRep (coxeterSystem τ) K w * b := by
  have ht := (canonical_weyl_root_transport τ K).2.1 w (w⁻¹ • α) (IsRoot.smul hα.1 w⁻¹)
  rw [smul_inv_smul] at ht
  rw [← ht] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  have hmem : w⁻¹ • α ∈ parabolicPosRoots τ A :=
    mem_parabolicPosRoots_of (smul_mem_parabolicRoots (inv_mem hw) hα) hpos
  refine ⟨b, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (w⁻¹ • α)
    (Subgroup.mem_iSup_of_mem hmem hb)), ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_mul_cancel_right]

theorem single_mem_parabolicPosRoots
    {i : Fin τ.rank} (hi : i ∈ A) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicPosRoots τ A :=
  mem_parabolicPosRoots_of (single_mem_parabolicRoots hi) (by rw [height_single]; exact one_pos)

theorem xUnit_mem_subsystemBorel
    {i : Fin τ.rank} (hi : i ∈ A) (c : K) :
    xUnit τ K i c ∈ subsystemBorel τ K A := by
  rw [← pinnedX_single]
  exact Subgroup.mem_sup_right (pinnedX_mem_rootSpan (single_mem_parabolicPosRoots hi) c)

theorem torusElt_mem_subsystemBorel
    {i : Fin τ.rank} (hi : i ∈ A) (t : Kˣ) :
    torusElt τ K i t ∈ subsystemBorel τ K A :=
  Subgroup.mem_sup_left (torusElt_mem_subsystemTorus hi t)

theorem image_reflect_parabolicPosRoots_diff
    {i : Fin τ.rank} (hi : i ∈ A) :
    reflect τ i '' (parabolicPosRoots τ A \ {Pi.single i 1}) =
      parabolicPosRoots τ A \ {Pi.single i 1} := by
  have hmaps : ∀ α ∈ parabolicPosRoots τ A \ {Pi.single i 1},
      reflect τ i α ∈ parabolicPosRoots τ A \ {Pi.single i 1} := by
    rintro α ⟨⟨⟨hα, hzero⟩, -, hpos⟩, hne⟩
    have hne' : α ≠ Pi.single i 1 := hne
    obtain ⟨hr, hrpos, hrne⟩ := (bijOn_reflect (τ := τ) i).mapsTo ⟨hα, hpos, hne'⟩
    refine ⟨⟨⟨hr, fun k hk => ?_⟩, hr, hrpos⟩, hrne⟩
    rw [reflect_apply_of_ne i (show k ≠ i from fun h => hk (h ▸ hi)), hzero k hk]
  refine Set.Subset.antisymm ?_ fun α hα => ⟨reflect τ i α, hmaps α hα, reflect_reflect τ i α⟩
  rintro _ ⟨α, hα, rfl⟩
  exact hmaps α hα

theorem weylElt_mul_eq_of_mem_subsystemBorel
    {i : Fin τ.rank} (hi : i ∈ A) {b : ModGL τ K}
    (hb : b ∈ subsystemBorel τ K A) :
    ∃ b' ∈ subsystemBorel τ K A, ∃ c : K,
      weylElt τ K i 1 * b = b' * (weylElt τ K i 1 * xUnit τ K i c) := by
  rw [← SetLike.mem_coe, coe_subsystemBorel] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  set S₁ := parabolicPosRoots τ A \ {Pi.single i 1}
  have hsplit : parabolicPosRoots τ A = S₁ ∪ {Pi.single i 1} := by
    rw [Set.sdiff_union_self, Set.union_eq_left.2
      (Set.singleton_subset_iff.2 (single_mem_parabolicPosRoots hi))]
  have hv' : v ∈ rootSpan τ K (S₁ ∪ {Pi.single i 1}) := by
    rw [← hsplit]
    exact hv
  obtain ⟨u, hu, x, hx, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := S₁) (S₂ := {Pi.single i 1})
    (fun α hα => hα.1.2) (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact ⟨isRoot_single τ i, by rw [height_single]; exact one_pos⟩)
    (Set.disjoint_singleton_right.2 fun h => h.2 rfl)
    (fun α hα β hβ a b ha hb hr => by
      rw [← hsplit] at hα hβ ⊢
      exact add_mem_parabolicPosRoots hα hβ ha hb hr) hv'
  rw [rootSpan, iSup_singleton] at hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  set n := weylElt τ K i 1
  have hnt : n * t * n⁻¹ ∈ subsystemTorus τ K A := weylElt_conj_mem_subsystemTorus hi ht
  have hnu : n * u * n⁻¹ ∈ parabolicLeviUnipotent τ K A := by
    have h1 : n * u * n⁻¹ ∈ (rootSpan τ K S₁).map (MulAut.conj n).toMonoidHom := ⟨u, hu, rfl⟩
    rw [map_conj_weylElt_rootSpan K i 1 fun α hα => hα.1.1.1,
      image_reflect_parabolicPosRoots_diff hi] at h1
    exact rootSpan_mono Set.sdiff_subset h1
  refine ⟨n * t * n⁻¹ * (n * u * n⁻¹), mul_mem (Subgroup.mem_sup_left hnt)
    (Subgroup.mem_sup_right hnu), c, ?_⟩
  rw [pinnedX_single]
  group

theorem weylElt_mul_mem_subsystemCell
    {i : Fin τ.rank} (hi : i ∈ A) {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) {x : ModGL τ K} (hx : x ∈ subsystemCell τ K A w) :
    weylElt τ K i 1 * x ∈ subsystemCell τ K A (simple τ i * w) ∨
      weylElt τ K i 1 * x ∈ subsystemCell τ K A w := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
  obtain ⟨b'', hb'', c, hc⟩ := weylElt_mul_eq_of_mem_subsystemBorel hi hb
  have e : weylElt τ K i 1 * (b * canonicalRep (coxeterSystem τ) K w * b') =
      b'' * (weylElt τ K i 1 * xUnit τ K i c) * canonicalRep (coxeterSystem τ) K w * b' := by
    rw [← hc]
    group
  rw [e]
  rcases (coxeterSystem τ).length_simple_mul w i with h | h
  ·
    left
    have hx' : xUnit τ K i c ∈ rootSubgroup τ K (Pi.single i 1) := by
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    obtain ⟨b₁, hb₁, h1⟩ := exists_mul_canonicalRep_eq_subsystem hw (single_mem_parabolicRoots hi)
      (height_inv_smul_single_pos h) hx'
    have hn := weylElt_mul_canonicalRep_of_length_eq (R := K) (cs := coxeterSystem τ) h
    refine mem_subsystemCell.2 ⟨b'', hb'', b₁ * b', mul_mem hb₁ hb', ?_⟩
    rw [← hn]
    calc b'' * (weylElt τ K i 1 * canonicalRep (coxeterSystem τ) K w) * (b₁ * b') =
          b'' * weylElt τ K i 1 * (canonicalRep (coxeterSystem τ) K w * b₁) * b' := by group
      _ = b'' * weylElt τ K i 1 * (xUnit τ K i c * canonicalRep (coxeterSystem τ) K w) * b' := by
          rw [h1]
      _ = b'' * (weylElt τ K i 1 * xUnit τ K i c) * canonicalRep (coxeterSystem τ) K w * b' := by
          group
  · have h' : (coxeterSystem τ).length ((coxeterSystem τ).simple i * w) =
        (coxeterSystem τ).length w - 1 := by omega
    by_cases hc0 : c = 0
    ·
      left
      have hn := weylElt_mul_canonicalRep_of_length_add_one_eq (R := K) (cs := coxeterSystem τ) h
      refine mem_subsystemCell.2 ⟨b'' * torusElt τ K i (-1),
        mul_mem hb'' (torusElt_mem_subsystemBorel hi _), b', hb', ?_⟩
      rw [hc0, xUnit_zero, mul_one, mul_assoc b'' (weylElt τ K i 1), hn, ← mul_assoc]
    ·
      right
      have hr := weylElt_one_mul_xUnit (τ := τ) (R := K) i (Units.mk0 c hc0)
      rw [Units.val_mk0] at hr
      have hy : yUnit τ K i (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) ∈
          rootSubgroup τ K (-Pi.single i 1) := by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      obtain ⟨b₂, hb₂, h2⟩ := exists_mul_canonicalRep_eq_subsystem hw
        (neg_mem_parabolicRoots (single_mem_parabolicRoots hi))
        (height_inv_smul_neg_single_pos h') hy
      refine mem_subsystemCell.2 ⟨b'' * xUnit τ K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
          torusElt τ K i (-(Units.mk0 c hc0)⁻¹),
        mul_mem (mul_mem hb'' (xUnit_mem_subsystemBorel hi _)) (torusElt_mem_subsystemBorel hi _),
        b₂ * b', mul_mem hb₂ hb', ?_⟩
      rw [hr]
      calc _ = b'' * xUnit τ K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
            torusElt τ K i (-(Units.mk0 c hc0)⁻¹) * (canonicalRep (coxeterSystem τ) K w * b₂) *
              b' := by group
        _ = b'' * xUnit τ K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
            torusElt τ K i (-(Units.mk0 c hc0)⁻¹) * (yUnit τ K i (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) *
              canonicalRep (coxeterSystem τ) K w) * b' := by rw [h2]
        _ = _ := by group

variable (τ K A) in
@[expose] def subsystemCells
    : Set (ModGL τ K) :=
  ⋃ w ∈ parabolicWeylGroup τ A, subsystemCell τ K A w

theorem mem_subsystemCells
    {x : ModGL τ K} :
    x ∈ subsystemCells τ K A ↔ ∃ w ∈ parabolicWeylGroup τ A, x ∈ subsystemCell τ K A w := by
  simp only [subsystemCells, Set.mem_iUnion, exists_prop]

theorem borel_mul_mem_subsystemCells
    {b x : ModGL τ K} (hb : b ∈ subsystemBorel τ K A)
    (hx : x ∈ subsystemCells τ K A) : b * x ∈ subsystemCells τ K A := by
  obtain ⟨w, hw, hx⟩ := mem_subsystemCells.1 hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_subsystemCell.1 hx
  exact mem_subsystemCells.2 ⟨w, hw, mem_subsystemCell.2 ⟨b * b₁, mul_mem hb hb₁, b₂, hb₂,
    by group⟩⟩

theorem weylElt_mul_mem_subsystemCells
    {i : Fin τ.rank} (hi : i ∈ A) {x : ModGL τ K}
    (hx : x ∈ subsystemCells τ K A) : weylElt τ K i 1 * x ∈ subsystemCells τ K A := by
  obtain ⟨w, hw, hx⟩ := mem_subsystemCells.1 hx
  have hsw : simple τ i * w ∈ parabolicWeylGroup τ A :=
    mul_mem (Subgroup.subset_closure ⟨i, hi, rfl⟩) hw
  rcases weylElt_mul_mem_subsystemCell hi hw hx with h | h
  · exact mem_subsystemCells.2 ⟨_, hsw, h⟩
  · exact mem_subsystemCells.2 ⟨w, hw, h⟩

theorem one_mem_subsystemCell_one
    : (1 : ModGL τ K) ∈ subsystemCell τ K A 1 :=
  mem_subsystemCell.2 ⟨1, one_mem _, 1, one_mem _, by rw [canonicalRep_one, mul_one, mul_one]⟩

theorem subsystemGroup_subset_subsystemCells :
    (subsystemGroup τ K A : Set (ModGL τ K)) ⊆ subsystemCells τ K A := by
  let M : Subgroup (ModGL τ K) :=
    { carrier := {g | (∀ x ∈ subsystemCells τ K A, g * x ∈ subsystemCells τ K A) ∧
        ∀ x ∈ subsystemCells τ K A, g⁻¹ * x ∈ subsystemCells τ K A}
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      mul_mem' := fun {a b} ha hb => ⟨fun x hx => by
          rw [mul_assoc]
          exact ha.1 _ (hb.1 x hx), fun x hx => by
          rw [mul_inv_rev, mul_assoc]
          exact hb.2 _ (ha.2 x hx)⟩
      inv_mem' := fun {a} ha => ⟨ha.2, fun x hx => by rw [inv_inv]; exact ha.1 x hx⟩ }
  have hBM : ∀ b ∈ subsystemBorel τ K A, b ∈ M := fun b hb =>
    ⟨fun x hx => borel_mul_mem_subsystemCells hb hx,
      fun x hx => borel_mul_mem_subsystemCells (inv_mem hb) hx⟩
  have hnM : ∀ i ∈ A, weylElt τ K i 1 ∈ M := fun i hi => by
    refine ⟨fun x hx => weylElt_mul_mem_subsystemCells hi hx, fun x hx => ?_⟩
    have hsq := weylElt_one_sq (τ := τ) (R := K) i
    have e : (weylElt τ K i 1)⁻¹ = weylElt τ K i 1 * (torusElt τ K i (-1))⁻¹ := by
      rw [← hsq, sq, mul_inv_rev, mul_inv_cancel_left]
    rw [e, mul_assoc]
    exact weylElt_mul_mem_subsystemCells hi
      (borel_mul_mem_subsystemCells (inv_mem (torusElt_mem_subsystemBorel hi _)) hx)
  have hle : subsystemGroup τ K A ≤ M := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · exact hBM _ (xUnit_mem_subsystemBorel hi c)
    · rw [yUnit_eq_conj]
      exact mul_mem (mul_mem (hnM i hi) (hBM _ (xUnit_mem_subsystemBorel hi _)))
        (inv_mem (hnM i hi))
  intro g hg
  have h1 : (1 : ModGL τ K) ∈ subsystemCells τ K A :=
    mem_subsystemCells.2 ⟨1, one_mem _, one_mem_subsystemCell_one⟩
  simpa using (hle hg).1 1 h1

theorem subsystemGroup_eq_subsystemCells :
    (subsystemGroup τ K A : Set (ModGL τ K)) = subsystemCells τ K A := by
  refine Set.Subset.antisymm subsystemGroup_subset_subsystemCells fun x hx => ?_
  obtain ⟨w, hw, hx⟩ := mem_subsystemCells.1 hx
  exact subsystemCell_subset_subsystemGroup hw hx

theorem disjoint_subsystemCell
    {w w' : WeylGroup τ} (h : w ≠ w') :
    Disjoint (subsystemCell τ K A w) (subsystemCell τ K A w') :=
  (disjoint_bruhatCell h).mono (subsystemCell_subset_bruhatCell w)
    (subsystemCell_subset_bruhatCell w')

theorem rootSpan_inversionSet_le_subsystemBorel
    {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) :
    rootSpan τ K (inversionSet w) ≤ subsystemBorel τ K A :=
  (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw)).trans le_sup_right

theorem subsystemCell_eq_mul
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A) :
    subsystemCell τ K A w = (subsystemBorel τ K A : Set (ModGL τ K)) *
      {canonicalRep (coxeterSystem τ) K w} * (rootSpan τ K (inversionSet w) : Set (ModGL τ K)) := by
  refine Set.Subset.antisymm (fun x hx => ?_) ?_
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
    rw [← SetLike.mem_coe, coe_subsystemBorel] at hb'
    obtain ⟨t, ht, v, hv, rfl⟩ := hb'
    set S₁ := parabolicPosRoots τ A \ inversionSet w
    have hsplit : parabolicPosRoots τ A = S₁ ∪ inversionSet w :=
      (Set.sdiff_union_of_subset (inversionSet_subset_parabolicPosRoots hw)).symm
    have hv' : v ∈ rootSpan τ K (S₁ ∪ inversionSet w) := by
      rw [← hsplit]
      exact hv
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_mul_rootSpan_eq K (S₁ := S₁)
      (S₂ := inversionSet w) (fun α hα => hα.1.2) (fun α hα => ⟨hα.1, hα.2.1⟩)
      Set.disjoint_sdiff_left
      (fun α hα β hβ a b ha hb hr => by
        rw [← hsplit] at hα hβ ⊢
        exact add_mem_parabolicPosRoots hα hβ ha hb hr) hv'
    have hnt := canonicalRep_conj_mem_subsystemTorus (K := K) hw ht
    have hnu : canonicalRep (coxeterSystem τ) K w * u₁ * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
        parabolicLeviUnipotent τ K A := by
      refine rootSpan_mono ?_ (canonicalRep_conj_mem_rootSpan (fun α hα => hα.1.1.1) hu₁)
      rintro _ ⟨α, ⟨hα, hαI⟩, rfl⟩
      refine mem_parabolicPosRoots_of (smul_mem_parabolicRoots hw hα.1) ?_
      rcases IsRoot.height_pos_or_neg (IsRoot.smul hα.1.1 w) with h | h
      · exact h
      · exact absurd ⟨hα.1.1, hα.2.2, IsRoot.smul hα.1.1 w, h⟩ hαI
    refine ⟨_, ⟨b * (canonicalRep (coxeterSystem τ) K w * t *
      (canonicalRep (coxeterSystem τ) K w)⁻¹) * (canonicalRep (coxeterSystem τ) K w * u₁ *
      (canonicalRep (coxeterSystem τ) K w)⁻¹), mul_mem (mul_mem hb (Subgroup.mem_sup_left hnt))
      (Subgroup.mem_sup_right hnu), _, rfl, rfl⟩, u₂, hu₂, ?_⟩
    simp only
    group
  · rintro _ ⟨_, ⟨b, hb, _, rfl, rfl⟩, u, hu, rfl⟩
    exact mem_subsystemCell.2 ⟨b, hb, u, rootSpan_inversionSet_le_subsystemBorel hw hu, rfl⟩

theorem bijOn_subsystemCell
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A) :
    Set.BijOn (fun p : ModGL τ K × ModGL τ K => p.1 * canonicalRep (coxeterSystem τ) K w * p.2)
      ((subsystemBorel τ K A : Set (ModGL τ K)) ×ˢ (rootSpan τ K (inversionSet w) : Set _))
      (subsystemCell τ K A w) := by
  refine ⟨fun p hp => mem_subsystemCell.2 ⟨p.1, hp.1, p.2,
    rootSpan_inversionSet_le_subsystemBorel hw hp.2, rfl⟩, fun p hp q hq h => ?_, fun x hx => ?_⟩
  · exact (bijOn_bruhatCell (K := K) w).injOn ⟨subsystemBorel_le_borelGroup hp.1, hp.2⟩
      ⟨subsystemBorel_le_borelGroup hq.1, hq.2⟩ h
  · rw [subsystemCell_eq_mul hw] at hx
    obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, u, hu, rfl⟩ := hx
    exact ⟨(b, u), ⟨hb, hu⟩, rfl⟩

end CFSG.LieType.Chevalley
