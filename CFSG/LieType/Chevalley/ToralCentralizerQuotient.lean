module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def toralRootGroup
    (a : Fin τ.rank → Kˣ) : Subgroup (ModGL τ K) :=
  torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a)

@[expose] def rootCharStabilizerSubgroup
    (a : Fin τ.rank → Kˣ) : Subgroup (WeylGroup τ) where
  carrier := rootCharStabilizer a
  one_mem' v := by rw [one_smul]
  mul_mem' {w w'} hw hw' v := by rw [mul_smul, hw, hw']
  inv_mem' {w} hw v := by rw [← hw (w⁻¹ • v), smul_inv_smul]

theorem mem_rootCharStabilizerSubgroup
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ} :
    w ∈ rootCharStabilizerSubgroup a ↔ w ∈ rootCharStabilizer a :=
  Iff.rfl

@[expose] def kernelReflectionGroup
    (a : Fin τ.rank → Kˣ) : Subgroup (WeylGroup τ) :=
  Subgroup.closure {r | ∃ (w : WeylGroup τ) (i : Fin τ.rank),
    w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ rootCharKernel a ∧ r = w * simple τ i * w⁻¹}

theorem torusGroup_le_toralCentralizer
    (a : Fin τ.rank → Kˣ) :
    torusGroup τ K ≤ toralCentralizer τ K a := fun _ hh =>
  mem_toralCentralizer.2 ⟨((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
    (Subgroup.mem_sup_left hh), conj_rootDiagUnit_of_mem_torusGroup a hh⟩

theorem toralRootGroup_le
    (a : Fin τ.rank → Kˣ) :
    toralRootGroup τ K a ≤ toralCentralizer τ K a :=
  sup_le (torusGroup_le_toralCentralizer a) fun _ hu =>
    Subgroup.mem_inf.2 ⟨rootSpan_le_adjointGroup K _ hu, rootSpan_le_centralizer a le_rfl hu⟩

theorem canonicalRep_mem_toralCentralizer
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a) :
    canonicalRep (coxeterSystem τ) K w ∈ toralCentralizer τ K a :=
  mem_toralCentralizer.2 ⟨canonicalRep_mem_adjointGroup _ K w,
    (conj_canonicalRep_eq_iff a w).2 hw⟩

theorem image_rootCharKernel
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a) : (fun α => w • α) '' rootCharKernel a = rootCharKernel a := by
  have hw' : w⁻¹ ∈ rootCharStabilizer a := (rootCharStabilizerSubgroup a).inv_mem hw
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, (hw α).trans hαa⟩
  · rintro ⟨hβ, hβa⟩
    exact ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, (hw' β).trans hβa⟩, smul_inv_smul w β⟩

theorem canonicalRep_mem_normalizer_toralRootGroup
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ rootCharStabilizer a) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (toralRootGroup τ K a : Set (ModGL τ K)) := by
  have hT := map_conj_eq_of_mem_normalizer (canonicalRep_mem_normalizer (R := K) w)
  have hS := (canonical_weyl_root_transport τ K).1 w (rootCharKernel a) fun α hα => hα.1
  rw [image_rootCharKernel hw] at hS
  have hmap : (toralRootGroup τ K a).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom = toralRootGroup τ K a := by
    rw [toralRootGroup, Subgroup.map_sup, hT, hS]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h
  exact h

theorem toralCentralizer_le_normalizer
    (a : Fin τ.rank → Kˣ) :
    toralCentralizer τ K a ≤ Subgroup.normalizer (toralRootGroup τ K a : Set (ModGL τ K)) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2]
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_sup_left.trans Subgroup.le_normalizer
  · exact le_sup_right.trans Subgroup.le_normalizer
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact canonicalRep_mem_normalizer_toralRootGroup hw

instance toralRootGroup_normal
    (a : Fin τ.rank → Kˣ) :
    ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (toralRootGroup_le a)).2
    (toralCentralizer_le_normalizer a)

theorem exists_conj_simple_smul
    (w : WeylGroup τ) (i : Fin τ.rank) (v : Fin τ.rank → ℤ) :
    ∃ c : ℤ, (w * simple τ i * w⁻¹) • v = v - c • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
  refine ⟨∑ j, τ.cartan i j * (w⁻¹ • v) j, ?_⟩
  rw [mul_smul, mul_smul, simple_smul]
  change w • (w⁻¹ • v - (∑ j, τ.cartan i j * (w⁻¹ • v) j) • Pi.single i 1) = _
  rw [smul_sub, smul_inv_smul, smul_comm]

theorem kernelReflectionGroup_le
    (a : Fin τ.rank → Kˣ) :
    kernelReflectionGroup a ≤ rootCharStabilizerSubgroup a := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨w, i, ⟨-, hα⟩, rfl⟩ v
  obtain ⟨c, hc⟩ := exists_conj_simple_smul w i v
  rw [hc, rootChar_sub, rootChar_zsmul, hα, one_zpow, inv_one, mul_one]

theorem conj_mem_kernelReflectionGroup
    {a : Fin τ.rank → Kˣ} {v : WeylGroup τ}
    (hv : v ∈ rootCharStabilizer a) {x : WeylGroup τ} (hx : x ∈ kernelReflectionGroup a) :
    v * x * v⁻¹ ∈ kernelReflectionGroup a := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, i, ⟨hα, hαa⟩, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨v * w, i, ⟨?_, ?_⟩, by group⟩
    · rw [mul_smul]
      exact IsRoot.smul hα v
    · rw [mul_smul, hv, hαa]
  | one => simp
  | mul x y _ _ hx hy =>
    have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

instance kernelReflectionGroup_normal (a : Fin τ.rank → Kˣ) :
    ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (kernelReflectionGroup_le a)).2 ?_
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_kernelReflectionGroup hv, fun h => ?_⟩
  have hv' : v⁻¹ ∈ rootCharStabilizer a := (rootCharStabilizerSubgroup a).inv_mem hv
  have := conj_mem_kernelReflectionGroup hv' h
  rwa [show v⁻¹ * (v * x * v⁻¹) * v⁻¹⁻¹ = x by group] at this

theorem mem_torusGroup_of_mapsRootLines_one
    {g : ModGL τ K} (hg : g ∈ monomialSubgroup τ K)
    (h1 : MapsRootLines g 1) : g ∈ torusGroup τ K := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets hg
  have hmaps : MapsRootLines g w := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  have hw : w = 1 := hmaps.unique h1
  rw [hgk, hw, canonicalRep_one, mul_one]
  exact hk

theorem canonicalRep_conj_simple_mem
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ} {i : Fin τ.rank}
    (hα : w • (Pi.single i 1 : Fin τ.rank → ℤ) ∈ rootCharKernel a) :
    canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) ∈ toralRootGroup τ K a := by
  set n := canonicalRep (coxeterSystem τ) K w
  set α : Fin τ.rank → ℤ := w • (Pi.single i 1 : Fin τ.rank → ℤ)
  have hnegα : -α ∈ rootCharKernel a := by
    refine ⟨IsRoot.neg hα.1, ?_⟩
    rw [← zero_sub, rootChar_sub, rootChar_zero, hα.2, inv_one, mul_one]
  have hmapx := (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i)
  have hmapy := (canonical_weyl_root_transport τ K).2.1 w _ (IsRoot.neg (isRoot_single τ i))
  rw [smul_neg] at hmapy
  have hU : ∀ β ∈ rootCharKernel a, rootSubgroup τ K β ≤ toralRootGroup τ K a := fun β hβ =>
    (le_iSup₂_of_le (f := fun γ (_ : γ ∈ rootCharKernel a) => rootSubgroup τ K γ) β hβ
      le_rfl).trans le_sup_right
  have hx : ∀ c : K, n * xUnit τ K i c * n⁻¹ ∈ toralRootGroup τ K a := fun c => by
    refine hU α hα ?_
    rw [← hmapx]
    exact ⟨_, xUnit_mem_rootSubgroup i c, rfl⟩
  have hy : ∀ c : K, n * yUnit τ K i c * n⁻¹ ∈ toralRootGroup τ K a := fun c => by
    refine hU (-α) hnegα ?_
    rw [← hmapy]
    exact ⟨_, yUnit_mem_rootSubgroup i c, rfl⟩
  have hm : n * weylElt τ K i 1 * n⁻¹ ∈ toralRootGroup τ K a := by
    rw [weylElt_eq_xUnit_mul]
    have e : n * (xUnit τ K i ((1 : Kˣ) : K) * yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) *
        xUnit τ K i ((1 : Kˣ) : K)) * n⁻¹ = (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) *
          (n * yUnit τ K i (-(((1 : Kˣ)⁻¹ : Kˣ) : K)) * n⁻¹) *
            (n * xUnit τ K i ((1 : Kˣ) : K) * n⁻¹) := by group
    rw [e]
    exact mul_mem (mul_mem (hx _) (hy _)) (hx _)
  have hN : (canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹) ∈ monomialSubgroup τ K :=
    mul_mem (inv_mem (canonicalRep_mem_monomialSubgroup K _))
      (mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup K w) (weylElt_mem_monomialSubgroup i))
        (inv_mem (canonicalRep_mem_monomialSubgroup K w)))
  have hmaps : MapsRootLines ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
      (n * weylElt τ K i 1 * n⁻¹)) 1 := by
    have := (mapsRootLines_canonicalRep (R := K) (w * simple τ i * w⁻¹)).inv.mul
      (((mapsRootLines_canonicalRep (R := K) w).mul (mapsRootLines_weylElt i)).mul
        (mapsRootLines_canonicalRep (R := K) w).inv)
    rwa [inv_mul_cancel] at this
  have hT := mem_torusGroup_of_mapsRootLines_one hN hmaps
  have e : canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹) =
      (n * weylElt τ K i 1 * n⁻¹) *
        ((canonicalRep (coxeterSystem τ) K (w * simple τ i * w⁻¹))⁻¹ *
          (n * weylElt τ K i 1 * n⁻¹))⁻¹ := by group
  rw [e]
  exact mul_mem hm (inv_mem (le_sup_left (a := torusGroup τ K) hT))

variable (K) in
@[expose] def weylToralQuotientHom
    (a : Fin τ.rank → Kˣ) :
    rootCharStabilizerSubgroup a →*
      toralCentralizer τ K a ⧸ (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a) where
  toFun w := QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w,
    canonicalRep_mem_toralCentralizer w.2⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext (by simp [canonicalRep_one])
  map_mul' w v := by
    obtain ⟨k, hk, hkv⟩ := canonicalRep_mul_mem (R := K) (w : WeylGroup τ) (v : WeylGroup τ)
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hkv]
    have hT := (Subgroup.mem_normalizer_iff.1 (inv_mem (canonicalRep_mem_normalizer (R := K)
      ((w : WeylGroup τ) * (v : WeylGroup τ)))) k).1 hk
    rw [inv_inv] at hT
    rw [← mul_assoc]
    exact le_sup_left (a := torusGroup τ K) hT

theorem weylToralQuotientHom_apply
    (a : Fin τ.rank → Kˣ) (w : rootCharStabilizerSubgroup a) :
    weylToralQuotientHom K a w = QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w,
      canonicalRep_mem_toralCentralizer w.2⟩ :=
  rfl

theorem kernelReflectionGroup_le_ker
    (a : Fin τ.rank → Kˣ) :
    (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) ≤
      (weylToralQuotientHom K a).ker := by
  rintro ⟨x, hxa⟩ hx
  rw [Subgroup.mem_subgroupOf] at hx
  change x ∈ kernelReflectionGroup a at hx
  revert hxa
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    intro hxa
    obtain ⟨w, i, hα, rfl⟩ := hx
    rw [MonoidHom.mem_ker, weylToralQuotientHom_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact canonicalRep_conj_simple_mem hα
  | one => intro hxa; exact one_mem _
  | mul x y hx hy ihx ihy =>
    intro hxa
    have h := mul_mem (ihx (kernelReflectionGroup_le a hx)) (ihy (kernelReflectionGroup_le a hy))
    exact h
  | inv x hx ihx =>
    intro hxa
    exact inv_mem (ihx (kernelReflectionGroup_le a hx))

theorem Chevalley_toral_centralizer_root_generated_quotient
    (τ : Tag) (K : Type) [Field K]
    (a : Fin τ.rank → Kˣ) :
    toralRootGroup τ K a ≤ toralCentralizer τ K a ∧
    ((toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)).Normal ∧
    kernelReflectionGroup a ≤ rootCharStabilizerSubgroup a ∧
    ((kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)).Normal ∧
    ∃ φ : rootCharStabilizerSubgroup a ⧸
        (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a) →*
          toralCentralizer τ K a ⧸ (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a),
      Function.Surjective φ ∧
      ∀ w : rootCharStabilizerSubgroup a, φ (QuotientGroup.mk w) =
        QuotientGroup.mk ⟨canonicalRep (coxeterSystem τ) K w,
          canonicalRep_mem_toralCentralizer w.2⟩ := by
  refine ⟨toralRootGroup_le a, inferInstance, kernelReflectionGroup_le a, inferInstance,
    QuotientGroup.lift _ (weylToralQuotientHom K a) (kernelReflectionGroup_le_ker a), ?_,
    fun w => rfl⟩
  intro q
  obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K a).1 g hg
  have hM : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ rootCharKernel a →
      rootSpan τ K S ≤ toralRootGroup τ K a := fun hS =>
    (rootSpan_mono hS).trans le_sup_right
  have huM : h * u ∈ toralRootGroup τ K a :=
    mul_mem (le_sup_left (a := torusGroup τ K) hh) (hM Set.inter_subset_left hu)
  have hvM : v ∈ toralRootGroup τ K a := hM Set.inter_subset_left hv
  refine ⟨QuotientGroup.mk ⟨w, hw⟩, ?_⟩
  change weylToralQuotientHom K a ⟨w, hw⟩ = _
  rw [weylToralQuotientHom_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  set n := canonicalRep (coxeterSystem τ) K w
  have e : n⁻¹ * (h * u * n * v) = (n⁻¹ * (h * u) * n) * v := by group
  rw [e]
  refine mul_mem ?_ hvM
  have hn := inv_mem (canonicalRep_mem_normalizer_toralRootGroup (K := K) hw)
  have := (Subgroup.mem_normalizer_iff.1 hn (h * u)).1 huM
  simpa using this

end CFSG.LieType.Chevalley
