module

public import CFSG.LieType.Chevalley.ParabolicRadicalLevi

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable (τ : Tag) (K : Type) [Field K] (A : Set (Fin τ.rank))

@[expose] def subsystemGroup
    : Subgroup (ModGL τ K) :=
  Subgroup.closure {g | ∃ i ∈ A, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c}

@[expose] def subsystemTorus
    : Subgroup (ModGL τ K) :=
  Subgroup.closure {g | ∃ i ∈ A, ∃ t : Kˣ, g = torusElt τ K i t}

@[expose] def subsystemBorel
    : Subgroup (ModGL τ K) :=
  subsystemTorus τ K A ⊔ parabolicLeviUnipotent τ K A

@[expose] def subsystemCell
    (w : WeylGroup τ) : Set (ModGL τ K) :=
  (subsystemBorel τ K A : Set (ModGL τ K)) * {canonicalRep (coxeterSystem τ) K w} *
    (subsystemBorel τ K A : Set (ModGL τ K))

variable {τ K A}

theorem mem_subsystemCell
    {w : WeylGroup τ} {x : ModGL τ K} :
    x ∈ subsystemCell τ K A w ↔ ∃ b ∈ subsystemBorel τ K A, ∃ b' ∈ subsystemBorel τ K A,
      b * canonicalRep (coxeterSystem τ) K w * b' = x := by
  simp only [subsystemCell, Set.mem_mul, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩
    exact ⟨b, hb, b', hb', rfl⟩
  · rintro ⟨b, hb, b', hb', rfl⟩
    exact ⟨_, ⟨b, hb, _, rfl, rfl⟩, b', hb', rfl⟩

theorem smul_mem_parabolicRoots
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A)
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ A) : w • α ∈ parabolicRoots τ A :=
  ⟨IsRoot.smul hα.1 w, fun i hi => by rw [smul_apply_of_mem_parabolicWeylGroup hw α hi, hα.2 i hi]⟩

theorem mem_parabolicPosRoots_of {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ A)
    (hpos : 0 < height α) : α ∈ parabolicPosRoots τ A :=
  ⟨hα, hα.1, hpos⟩

theorem single_mem_parabolicRoots {i : Fin τ.rank} (hi : i ∈ A) :
    (Pi.single i 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ A :=
  ⟨isRoot_single τ i, fun k hk => by
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact hk hi⟩

theorem neg_mem_parabolicRoots
    {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ A) :
    -α ∈ parabolicRoots τ A :=
  ⟨IsRoot.neg hα.1, fun i hi => by rw [Pi.neg_apply, hα.2 i hi, neg_zero]⟩

theorem inversionSet_subset_parabolicPosRoots
    {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) : inversionSet w ⊆ parabolicPosRoots τ A := by
  rintro α ⟨hα, hpos, hwα, hneg⟩
  refine ⟨⟨hα, fun i hi => ?_⟩, hα, hpos⟩
  have h1 := (IsRoot.height_pos_iff hα).1 hpos i
  have h2 := (IsRoot.height_neg_iff hwα).1 hneg i
  rw [smul_apply_of_mem_parabolicWeylGroup hw α hi] at h2
  omega

theorem xUnit_mem_subsystemGroup
    {i : Fin τ.rank} (hi : i ∈ A) (c : K) :
    xUnit τ K i c ∈ subsystemGroup τ K A :=
  Subgroup.subset_closure ⟨i, hi, c, Or.inl rfl⟩

theorem yUnit_mem_subsystemGroup
    {i : Fin τ.rank} (hi : i ∈ A) (c : K) :
    yUnit τ K i c ∈ subsystemGroup τ K A :=
  Subgroup.subset_closure ⟨i, hi, c, Or.inr rfl⟩

theorem weylElt_eq_xUnit_mul
    (i : Fin τ.rank) (t : Kˣ) :
    weylElt τ K i t = xUnit τ K i t * yUnit τ K i (-((t⁻¹ : Kˣ) : K)) * xUnit τ K i t :=
  Units.ext rfl

theorem weylElt_mem_subsystemGroup
    {i : Fin τ.rank} (hi : i ∈ A) (t : Kˣ) :
    weylElt τ K i t ∈ subsystemGroup τ K A := by
  rw [weylElt_eq_xUnit_mul]
  exact mul_mem (mul_mem (xUnit_mem_subsystemGroup hi _) (yUnit_mem_subsystemGroup hi _))
    (xUnit_mem_subsystemGroup hi _)

theorem torusElt_mem_subsystemTorus
    {i : Fin τ.rank} (hi : i ∈ A) (t : Kˣ) :
    torusElt τ K i t ∈ subsystemTorus τ K A :=
  Subgroup.subset_closure ⟨i, hi, t, rfl⟩

theorem subsystemTorus_le_subsystemGroup
    : subsystemTorus τ K A ≤ subsystemGroup τ K A :=
  (Subgroup.closure_le _).2 fun _ ⟨_, hi, t, he⟩ =>
    he ▸ mul_mem (weylElt_mem_subsystemGroup hi t) (weylElt_mem_subsystemGroup hi (-1))

theorem subsystemTorus_le_torusGroup
    : subsystemTorus τ K A ≤ torusGroup τ K :=
  (Subgroup.closure_le _).2 fun _ ⟨i, _, t, he⟩ => he ▸ torusElt_mem_torusGroup i t

theorem canonicalRep_mem_subsystemGroup
    {w : WeylGroup τ} (hw : w ∈ parabolicWeylGroup τ A) :
    canonicalRep (coxeterSystem τ) K w ∈ subsystemGroup τ K A := by
  obtain ⟨ω, hω, rfl, hletters⟩ := (parabolic_Weyl_coordinate_stabilizer τ A).2.1 w hw
  rw [canonicalRep_wordProd hω]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  exact weylElt_mem_subsystemGroup (hletters i hi) 1

theorem parabolicLeviUnipotent_le_subsystemGroup :
    parabolicLeviUnipotent τ K A ≤ subsystemGroup τ K A := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨w, hw, j, hj, rfl⟩ := exists_mem_parabolicWeylGroup_smul _ α rfl hα
  rw [← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ j)]
  rintro _ ⟨u, hu, rfl⟩
  have huS : u ∈ subsystemGroup τ K A := by
    refine (Subgroup.closure_le _).2 ?_ hu
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_subsystemGroup hj c
  have hn := canonicalRep_mem_subsystemGroup (K := K) hw
  exact mul_mem (mul_mem hn huS) (inv_mem hn)

theorem subsystemBorel_le_subsystemGroup :
    subsystemBorel τ K A ≤ subsystemGroup τ K A :=
  sup_le subsystemTorus_le_subsystemGroup parabolicLeviUnipotent_le_subsystemGroup

theorem subsystemBorel_le_borelGroup
    : subsystemBorel τ K A ≤ borelGroup τ K :=
  sup_le (subsystemTorus_le_torusGroup.trans le_sup_left)
    ((parabolicLeviUnipotent_le_posUnipotent A).trans le_sup_right)

theorem subsystemCell_subset_subsystemGroup
    {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) : subsystemCell τ K A w ⊆ subsystemGroup τ K A := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
  exact mul_mem (mul_mem (subsystemBorel_le_subsystemGroup hb)
    (canonicalRep_mem_subsystemGroup hw)) (subsystemBorel_le_subsystemGroup hb')

theorem subsystemCell_subset_bruhatCell
    (w : WeylGroup τ) :
    subsystemCell τ K A w ⊆ bruhatCell τ K w := by
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
  exact mem_bruhatCell.2 ⟨b, subsystemBorel_le_borelGroup hb, b',
    subsystemBorel_le_borelGroup hb', rfl⟩

theorem subsystemTorus_le_normalizer :
    subsystemTorus τ K A ≤
      Subgroup.normalizer (parabolicLeviUnipotent τ K A : Set (ModGL τ K)) :=
  subsystemTorus_le_torusGroup.trans (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1)

theorem coe_subsystemBorel :
    (subsystemBorel τ K A : Set (ModGL τ K)) =
      (subsystemTorus τ K A : Set (ModGL τ K)) * (parabolicLeviUnipotent τ K A : Set _) :=
  Subgroup.coe_mul_of_left_le_normalizer_right (subsystemTorus τ K A)
    (parabolicLeviUnipotent τ K A) subsystemTorus_le_normalizer

theorem eq_of_mul_eq_subsystem
    {t t' v v' : ModGL τ K} (ht : t ∈ subsystemTorus τ K A)
    (ht' : t' ∈ subsystemTorus τ K A) (hv : v ∈ parabolicLeviUnipotent τ K A)
    (hv' : v' ∈ parabolicLeviUnipotent τ K A) (h : t * v = t' * v') : t = t' ∧ v = v' :=
  (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.1 t (subsystemTorus_le_torusGroup ht) t'
    (subsystemTorus_le_torusGroup ht') v (parabolicLeviUnipotent_le_posUnipotent A hv) v'
    (parabolicLeviUnipotent_le_posUnipotent A hv') h

theorem weylElt_conj_mem_subsystemTorus
    {i : Fin τ.rank} (hi : i ∈ A) {t : ModGL τ K}
    (ht : t ∈ subsystemTorus τ K A) :
    weylElt τ K i 1 * t * (weylElt τ K i 1)⁻¹ ∈ subsystemTorus τ K A := by
  have hle : (subsystemTorus τ K A).map (MulAut.conj (weylElt τ K i 1)).toMonoidHom ≤
      subsystemTorus τ K A := by
    rw [subsystemTorus, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨j, hj, s, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [weylElt_one_mul_torusElt_mul_inv]
    exact mul_mem (torusElt_mem_subsystemTorus hj s) (torusElt_mem_subsystemTorus hi _)
  exact hle ⟨t, ht, rfl⟩

theorem list_prod_weylElt_conj_mem_subsystemTorus :
    ∀ ω : List (Fin τ.rank), (∀ i ∈ ω, i ∈ A) → ∀ {t : ModGL τ K}, t ∈ subsystemTorus τ K A →
      (ω.map fun i => weylElt τ K i 1).prod * t * ((ω.map fun i => weylElt τ K i 1).prod)⁻¹ ∈
        subsystemTorus τ K A
  | [], _, t, ht => by simpa using ht
  | i :: ω, hω, t, ht => by
    have h1 := list_prod_weylElt_conj_mem_subsystemTorus ω
      (fun j hj => hω j (List.mem_cons_of_mem _ hj)) ht
    have h2 := weylElt_conj_mem_subsystemTorus (K := K) (hω i List.mem_cons_self) h1
    rw [List.map_cons, List.prod_cons, mul_inv_rev]
    simpa [mul_assoc] using h2

theorem canonicalRep_conj_mem_subsystemTorus
    {w : WeylGroup τ}
    (hw : w ∈ parabolicWeylGroup τ A) {t : ModGL τ K} (ht : t ∈ subsystemTorus τ K A) :
    canonicalRep (coxeterSystem τ) K w * t * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      subsystemTorus τ K A := by
  obtain ⟨ω, hω, rfl, hletters⟩ := (parabolic_Weyl_coordinate_stabilizer τ A).2.1 w hw
  rw [canonicalRep_wordProd hω]
  exact list_prod_weylElt_conj_mem_subsystemTorus ω hletters ht

end CFSG.LieType.Chevalley
