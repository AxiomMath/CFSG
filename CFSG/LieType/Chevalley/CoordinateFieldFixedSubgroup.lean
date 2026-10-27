module

public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.LieType.Chevalley.BruhatDecomposition
public import CFSG.LieType.Chevalley.BruhatCellFactorization
public import CFSG.LieType.Chevalley.PositiveRootCollection
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

variable (σ : K ≃+* K)

abbrev fixSubfield : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_fixSubfield {c : K} : c ∈ fixSubfield σ ↔ σ c = c := Iff.rfl

variable (τ) in
@[expose] def fixedFieldImage :
    Subgroup (ModGL τ K) :=
  (adjointGroup τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)

variable (τ) in
@[expose] def entrywiseFixedGroup : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _)

variable (τ) in
@[expose] def entrywiseFixedTorus
    : Subgroup (ModGL τ K) :=
  torusGroup τ K ⊓ entrywiseFixedGroup τ σ

variable {σ}

theorem mem_entrywiseFixedGroup {g : ModGL τ K} :
    g ∈ entrywiseFixedGroup τ σ ↔
      g ∈ adjointGroup τ K ∧ Units.map (entrywiseHom σ.toRingHom) g = g :=
  Iff.rfl

theorem entrywiseFixedTorus_le
    : entrywiseFixedTorus τ σ ≤ entrywiseFixedGroup τ σ :=
  inf_le_right

variable (σ) in
theorem entrywise_torusElt
    (i : Fin τ.rank) (t : Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (torusElt τ K i t) =
      torusElt τ K i (Units.map σ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
  refine Units.ext ?_
  rw [Units.coe_map]
  change entrywise σ.toRingHom (rootDiag _) = rootDiag _
  rw [entrywise_rootDiag]
  congr 1
  funext j
  rw [map_zpow]

theorem entrywise_mem_torusGroup
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    Units.map (entrywiseHom σ.toRingHom) h ∈ torusGroup τ K := by
  have hle : torusGroup τ K ≤
      (torusGroup τ K).comap (Units.map (entrywiseHom σ.toRingHom)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, entrywise_torusElt]
    exact Subgroup.subset_closure
      (Set.mem_range_self (f := fun p : Fin τ.rank × Kˣ => torusElt τ K p.1 p.2)
        (i, Units.map σ.toRingHom.toMonoidHom t))
  exact hle hh

theorem entrywise_mem_rootSpan
    {S : Set (Fin τ.rank → ℤ)} {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K S) : Units.map (entrywiseHom σ.toRingHom) g ∈ rootSpan τ K S := by
  have hmap : (rootSpan τ K S).map (Units.map (entrywiseHom σ.toRingHom)) = rootSpan τ K S := by
    rw [rootSpan, Subgroup.map_iSup]
    refine iSup_congr fun α => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun _ => map_entrywise_rootSubgroup σ α
  rw [← hmap]
  exact Subgroup.mem_map_of_mem _ hg

theorem entrywise_mem_borelGroup
    {b : ModGL τ K} (hb : b ∈ borelGroup τ K) :
    Units.map (entrywiseHom σ.toRingHom) b ∈ borelGroup τ K := by
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  rw [map_mul]
  exact mul_mem (Subgroup.mem_sup_left (entrywise_mem_torusGroup hh))
    (Subgroup.mem_sup_right (entrywise_mem_rootSpan hu))

variable (σ) in
theorem entrywise_weylElt_one
    (i : Fin τ.rank) :
    Units.map (entrywiseHom σ.toRingHom) (weylElt τ K i 1) = weylElt τ K i 1 := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [RingEquiv.toRingHom_eq_coe, map_one, map_neg]

variable (σ) in
theorem entrywise_canonicalRep
    (w : WeylGroup τ) :
    Units.map (entrywiseHom σ.toRingHom) (canonicalRep (coxeterSystem τ) K w) =
      canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => entrywise_weylElt_one σ i)

theorem fixSubfield_subtype_apply (c : fixSubfield σ) : (fixSubfield σ).subtype c = c := rfl

theorem xUnit_mem_fixedFieldImage
    (i : Fin τ.rank) {c : K} (hc : σ c = c) :
    xUnit τ K i c ∈ fixedFieldImage τ σ :=
  ⟨xUnit τ (fixSubfield σ) i ⟨c, hc⟩, xUnit_mem_adjointGroup i _,
    baseChangeGL_xUnit _ i _⟩

theorem yUnit_mem_fixedFieldImage
    (i : Fin τ.rank) {c : K} (hc : σ c = c) :
    yUnit τ K i c ∈ fixedFieldImage τ σ :=
  ⟨yUnit τ (fixSubfield σ) i ⟨c, hc⟩, yUnit_mem_adjointGroup i _,
    baseChangeGL_yUnit _ i _⟩

theorem pinnedX_mem_fixedFieldImage
    (α : Fin τ.rank → ℤ) {c : K} (hc : σ c = c) :
    pinnedX τ K α c ∈ fixedFieldImage τ σ :=
  ⟨pinnedX τ (fixSubfield σ) α ⟨c, hc⟩, pinnedX_mem_adjointGroup α _,
    baseChangeGL_pinnedX _ α _⟩

theorem weylElt_one_mem_fixedFieldImage
    (i : Fin τ.rank) :
    weylElt τ K i 1 ∈ fixedFieldImage τ σ := by
  rw [weylElt_eq_xUnit_mul, inv_one, Units.val_one]
  refine mul_mem (mul_mem (xUnit_mem_fixedFieldImage i (map_one σ))
    (yUnit_mem_fixedFieldImage i ?_)) (xUnit_mem_fixedFieldImage i (map_one σ))
  rw [map_neg, map_one]

theorem canonicalRep_mem_fixedFieldImage
    (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) K w ∈ fixedFieldImage τ σ := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  exact weylElt_one_mem_fixedFieldImage i

theorem fixedFieldImage_eq_closure :
    fixedFieldImage τ σ = Subgroup.closure
    {g | ∃ (i : Fin τ.rank) (c : K), σ c = c ∧ (g = xUnit τ K i c ∨ g = yUnit τ K i c)} := by
  rw [fixedFieldImage, map_baseChangeGL_adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨i, c, h⟩
    exact ⟨i, c, c.2, h⟩
  · rintro ⟨i, c, hc, h⟩
    exact ⟨i, ⟨c, hc⟩, h⟩

theorem fixedFieldImage_le
    : fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ := by
  rw [fixedFieldImage_eq_closure, Subgroup.closure_le]
  rintro _ ⟨i, c, hc, rfl | rfl⟩
  · refine ⟨xUnit_mem_adjointGroup i c, ?_⟩
    change Units.map (entrywiseHom σ.toRingHom) (xUnit τ K i c) = xUnit τ K i c
    rw [units_map_entrywiseHom_xUnit]
    exact congrArg _ hc
  · refine ⟨yUnit_mem_adjointGroup i c, ?_⟩
    change Units.map (entrywiseHom σ.toRingHom) (yUnit τ K i c) = yUnit τ K i c
    rw [units_map_entrywiseHom_yUnit]
    exact congrArg _ hc

theorem mem_fixedFieldImage_of_fixed
    {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S) (hfix : Units.map (entrywiseHom σ.toRingHom) u = u) :
    u ∈ fixedFieldImage τ σ := by
  have : Finite S := hS.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  set α : Fin n → Fin τ.rank → ℤ := fun k => (e.symm k : Fin τ.rank → ℤ)
  have hα : Function.Injective α := fun k k' h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range α = S := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact (e.symm k).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [α]⟩
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : Units.map (entrywiseHom σ.toRingHom)
      ((List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) =
        (List.ofFn fun k => pinnedX τ K (α k) (σ (c k))).prod := by
    rw [map_list_prod, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    refine Units.ext ?_
    rw [Function.comp_apply, Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom (α k) (c k)
  rw [hmap] at hfix
  have hc : (fun k => σ (c k)) = c := hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  exact pinnedX_mem_fixedFieldImage (α k) (congrFun hc k)

theorem mem_mul_of_mem_entrywiseFixedGroup
    {g : ModGL τ K} (hg : g ∈ entrywiseFixedGroup τ σ) :
    g ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ K)) * (fixedFieldImage τ σ : Set (ModGL τ K)) := by
  obtain ⟨hgC, hgF⟩ := mem_entrywiseFixedGroup.1 hg
  have hgC' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hgC
  rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hgC'
  obtain ⟨w, hw⟩ := hgC'
  have hbij := (bruhat_cell_factorization τ K).1 w
  obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := hbij.2.2 hw
  simp only at hbv
  have hσg : Units.map (entrywiseHom σ.toRingHom) b * canonicalRep (coxeterSystem τ) K w *
      Units.map (entrywiseHom σ.toRingHom) v = b * canonicalRep (coxeterSystem τ) K w * v := by
    calc Units.map (entrywiseHom σ.toRingHom) b * canonicalRep (coxeterSystem τ) K w *
          Units.map (entrywiseHom σ.toRingHom) v =
        Units.map (entrywiseHom σ.toRingHom) b *
          Units.map (entrywiseHom σ.toRingHom) (canonicalRep (coxeterSystem τ) K w) *
            Units.map (entrywiseHom σ.toRingHom) v := by rw [entrywise_canonicalRep]
      _ = Units.map (entrywiseHom σ.toRingHom) (b * canonicalRep (coxeterSystem τ) K w * v) := by
          rw [map_mul, map_mul]
      _ = b * canonicalRep (coxeterSystem τ) K w * v := by rw [hbv, hgF]
  have hfix : (Units.map (entrywiseHom σ.toRingHom) b, Units.map (entrywiseHom σ.toRingHom) v) =
      (b, v) :=
    hbij.2.1 (x₁ := (Units.map (entrywiseHom σ.toRingHom) b,
      Units.map (entrywiseHom σ.toRingHom) v)) (x₂ := (b, v))
      ⟨entrywise_mem_borelGroup hb, entrywise_mem_rootSpan hv⟩ ⟨hb, hv⟩ hσg
  simp only [Prod.mk.injEq] at hfix
  obtain ⟨hbF, hvF⟩ := hfix
  have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
    rw [← (triangular_borel_structure.{0, 0} τ K).2.2.2.2.1]
    exact hb
  obtain ⟨h, hh, u, hu, rfl⟩ := hb'
  rw [map_mul] at hbF
  obtain ⟨hhF, huF⟩ := (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.1 _
    (entrywise_mem_torusGroup hh) h hh _ (entrywise_mem_rootSpan hu) u hu hbF
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have huJ : u ∈ fixedFieldImage τ σ :=
    mem_fixedFieldImage_of_fixed hposfin (fun α hα hr => (positive_root_collection τ K).2 α hα hr)
      hu huF
  have hvJ : v ∈ fixedFieldImage τ σ :=
    mem_fixedFieldImage_of_fixed (inversionSet_finite w)
      (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hv hvF
  have hhC : h ∈ adjointGroup τ K :=
    ((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
      (Subgroup.mem_sup_left hh)
  refine ⟨h, ⟨hh, hhC, hhF⟩, u * canonicalRep (coxeterSystem τ) K w * v,
    mul_mem (mul_mem huJ (canonicalRep_mem_fixedFieldImage w)) hvJ, ?_⟩
  rw [← hbv]
  simp only [mul_assoc]

theorem coe_entrywiseFixedGroup_eq_mul :
    (entrywiseFixedGroup τ σ : Set (ModGL τ K)) =
      (entrywiseFixedTorus τ σ : Set (ModGL τ K)) * (fixedFieldImage τ σ : Set (ModGL τ K)) := by
  refine Set.Subset.antisymm (fun g hg => mem_mul_of_mem_entrywiseFixedGroup hg) ?_
  rintro _ ⟨h, hh, j, hj, rfl⟩
  exact mul_mem (entrywiseFixedTorus_le hh) (fixedFieldImage_le hj)

theorem conj_mem_fixedFieldImage
    {h : ModGL τ K} (hh : h ∈ entrywiseFixedTorus τ σ)
    {x : ModGL τ K} (hx : x ∈ fixedFieldImage τ σ) : h * x * h⁻¹ ∈ fixedFieldImage τ σ := by
  obtain ⟨hT, -, hF⟩ := hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hσa : ∀ i, σ (a i : K) = a i := by
    have hF' : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) = rootDiagUnit τ a := hF
    have h0 : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit τ a) =
        rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag σ.toRingHom a)
    have h1 : rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) =
        rootDiagUnit τ a := h0.symm.trans hF'
    intro i
    exact congrArg Units.val (congrFun (rootDiagUnit_injective h1) i)
  have hle : fixedFieldImage τ σ ≤ (fixedFieldImage τ σ).comap
      (MulAut.conj (rootDiagUnit τ a)).toMonoidHom := by
    conv_lhs => rw [fixedFieldImage_eq_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation τ K a).1]
      refine xUnit_mem_fixedFieldImage i ?_
      rw [map_mul, hσa, hc]
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation τ K a).2.1]
      refine yUnit_mem_fixedFieldImage i ?_
      rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀, hσa, hc]
  exact hle hx

theorem entrywiseFixedTorus_le_normalizer :
    entrywiseFixedTorus τ σ ≤ Subgroup.normalizer (fixedFieldImage τ σ : Set (ModGL τ K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_fixedFieldImage hh hx, fun hx => ?_⟩
  have := conj_mem_fixedFieldImage (inv_mem hh) hx
  rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

theorem fixedFieldImage_normal :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer fixedFieldImage_le).2 fun g hg => ?_
  have hg' : g ∈ (entrywiseFixedTorus τ σ : Set (ModGL τ K)) *
      (fixedFieldImage τ σ : Set (ModGL τ K)) := mem_mul_of_mem_entrywiseFixedGroup hg
  obtain ⟨h, hh, j, hj, rfl⟩ := hg'
  exact mul_mem (entrywiseFixedTorus_le_normalizer hh) (Subgroup.le_normalizer hj)

instance fixedFieldImage_subgroupOf_normal :
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).Normal :=
  fixedFieldImage_normal

theorem entrywiseFixedGroup_quotient_comm
    (a b : ↥(entrywiseFixedGroup τ σ) ⧸
      (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)) :
    a * b = b * a := by
  have hcls : ∀ x : ↥(entrywiseFixedGroup τ σ), ∃ (h : ModGL τ K)
      (hh : h ∈ entrywiseFixedTorus τ σ),
      (x : ↥(entrywiseFixedGroup τ σ) ⧸ (fixedFieldImage τ σ).subgroupOf
        (entrywiseFixedGroup τ σ)) = ((⟨h, entrywiseFixedTorus_le hh⟩ :
          ↥(entrywiseFixedGroup τ σ)) : _ ⧸ _) := by
    intro x
    obtain ⟨h, hh, j, hj, hx⟩ := mem_mul_of_mem_entrywiseFixedGroup x.2
    refine ⟨h, hh, ?_⟩
    rw [eq_comm, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (h⁻¹ * (x : ModGL τ K)) ∈ fixedFieldImage τ σ
    rw [← hx, inv_mul_cancel_left]
    exact hj
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  obtain ⟨h, hh, hx⟩ := hcls x
  obtain ⟨h', hh', hy⟩ := hcls y
  rw [hx, hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  exact (triangular_borel_structure.{0, 0} τ K).1 h hh.1 h' hh'.1

theorem Chevalley_coordinate_field_fixed_normal_subgroup
    (τ : Tag) (K : Type) [Field K]
    [Finite K] (σ : K ≃+* K) :
    (∃ e : MulAut (adjointGroup τ K), ∀ g : adjointGroup τ K,
      (e g : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (g : ModGL τ K)) ∧
    Function.Injective (baseChangeGL (τ := τ) (fixSubfield σ).subtype) ∧
    (∀ (g : ModGL τ (fixSubfield σ)) (b : Label τ),
      ((baseChangeGL (fixSubfield σ).subtype g : ModGL τ K) : Module.End K (RootModule τ K))
          (Finsupp.single b 1) =
        Finsupp.mapRange (fixSubfield σ).subtype (map_zero _)
          ((g : Module.End (fixSubfield σ) (RootModule τ (fixSubfield σ))) (Finsupp.single b 1))) ∧
    fixedFieldImage τ σ ≤ entrywiseFixedGroup τ σ ∧
    (entrywiseFixedGroup τ σ : Set (ModGL τ K)) =
      (entrywiseFixedTorus τ σ : Set (ModGL τ K)) * (fixedFieldImage τ σ : Set (ModGL τ K)) ∧
    ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).Normal ∧
    ∀ a b : ↥(entrywiseFixedGroup τ σ) ⧸
        (fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ), a * b = b * a :=
  ⟨⟨mulAutRestrict (adjointGroup τ K) (exactEntrywiseAut τ σ)
      (map_exactEntrywiseAut σ (Or.inl rfl)), fun _ => rfl⟩,
    baseChangeGL_injective _, fun g b => baseChangeGL_apply_single _ g b, fixedFieldImage_le,
    coe_entrywiseFixedGroup_eq_mul, fixedFieldImage_normal, entrywiseFixedGroup_quotient_comm⟩

end CFSG.LieType.Chevalley
