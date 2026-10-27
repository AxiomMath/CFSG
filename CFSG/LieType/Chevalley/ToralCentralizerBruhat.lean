module

public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.WeylNormalizerQuotient
public import CFSG.LieType.Chevalley.SimpleWeylComplement

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

variable (τ K) in
@[expose] def toralCentralizer (a : Fin τ.rank → Kˣ) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ Subgroup.centralizer {rootDiagUnit τ a}

@[expose] def rootCharKernel (a : Fin τ.rank → Kˣ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ rootChar a α = 1}

@[expose] def rootCharStabilizer
    (a : Fin τ.rank → Kˣ) : Set (WeylGroup τ) :=
  {w | ∀ v : Fin τ.rank → ℤ, rootChar a (w • v) = rootChar a v}

theorem conj_eq_iff_mem_centralizer {a : Fin τ.rank → Kˣ} {g : ModGL τ K} :
    rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g ↔
      g ∈ Subgroup.centralizer {rootDiagUnit τ a} := by
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

theorem mem_toralCentralizer {a : Fin τ.rank → Kˣ} {g : ModGL τ K} :
    g ∈ toralCentralizer τ K a ↔
      g ∈ adjointGroup τ K ∧ rootDiagUnit τ a * g * (rootDiagUnit τ a)⁻¹ = g := by
  rw [toralCentralizer, Subgroup.mem_inf, conj_eq_iff_mem_centralizer]

theorem rootChar_inv_apply (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem rootChar_sum {ι : Type*} (a : Fin τ.rank → Kˣ) (s : Finset ι)
    (f : ι → Fin τ.rank → ℤ) : rootChar a (∑ i ∈ s, f i) = ∏ i ∈ s, rootChar a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, rootChar_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, rootChar_add, ih]

theorem rootChar_zsmul (a : Fin τ.rank → Kˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar a (n • v) = rootChar a v ^ n := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

theorem rootChar_smul_eq_of_forall_isRoot
    {a : Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (h : ∀ α, IsRoot τ α → rootChar a (w • α) = rootChar a α) (v : Fin τ.rank → ℤ) :
    rootChar a (w • v) = rootChar a v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin τ.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hw : w • v = ∑ i, v i • (w • (Pi.single i 1 : Fin τ.rank → ℤ)) := by
    conv_lhs => rw [hv]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm w (v i) _
  rw [hw, rootChar_sum]
  conv_rhs => rw [hv, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [rootChar_zsmul, rootChar_zsmul, h _ (.basis i)]

theorem rootDiagUnit_mul_comm_of_mem_torusGroup
    (a : Fin τ.rank → Kˣ) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : rootDiagUnit τ a * h = h * rootDiagUnit τ a := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem conj_rootDiagUnit_of_mem_torusGroup
    (a : Fin τ.rank → Kˣ) {h : ModGL τ K}
    (hh : h ∈ torusGroup τ K) : rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ = h := by
  rw [rootDiagUnit_mul_comm_of_mem_torusGroup a hh, mul_inv_cancel_right]

theorem rootDiagUnit_conj_weylElt_one
    (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootDiagUnit τ a * weylElt τ K i 1 * (rootDiagUnit τ a)⁻¹ =
      torusElt τ K i (a i) * weylElt τ K i 1 := by
  obtain ⟨hx, hy, -⟩ := root_diagonal_conjugation τ K a
  rw [← weylElt_eq_torusElt_mul_weylElt_one, weylElt_eq_xUnit_mul, weylElt_eq_xUnit_mul]
  have e : ∀ x y z : ModGL τ K, rootDiagUnit τ a * (x * y * z) * (rootDiagUnit τ a)⁻¹ =
      (rootDiagUnit τ a * x * (rootDiagUnit τ a)⁻¹) * (rootDiagUnit τ a * y *
        (rootDiagUnit τ a)⁻¹) * (rootDiagUnit τ a * z * (rootDiagUnit τ a)⁻¹) := fun x y z => by
    group
  rw [e, hx, hy]
  simp

theorem exists_conj_list_prod_weylElt
    (a : Fin τ.rank → Kˣ) (ω : List (Fin τ.rank)) :
    ∃ t ∈ torusGroup τ K, rootDiagUnit τ a * (ω.map fun i => weylElt τ K i 1).prod *
      (rootDiagUnit τ a)⁻¹ = t * (ω.map fun i => weylElt τ K i 1).prod := by
  induction ω with
  | nil => exact ⟨1, one_mem _, by simp⟩
  | cons i ω ih =>
    obtain ⟨t, ht, h⟩ := ih
    have hni := weylElt_mem_normalizer_torus τ K i 1
    refine ⟨torusElt τ K i (a i) * (weylElt τ K i 1 * t * (weylElt τ K i 1)⁻¹),
      mul_mem (torusElt_mem_torusGroup i _) ((Subgroup.mem_normalizer_iff.1 hni t).1 ht), ?_⟩
    rw [List.map_cons, List.prod_cons]
    calc rootDiagUnit τ a * (weylElt τ K i 1 * (ω.map fun i => weylElt τ K i 1).prod) *
          (rootDiagUnit τ a)⁻¹ =
        (rootDiagUnit τ a * weylElt τ K i 1 * (rootDiagUnit τ a)⁻¹) *
          (rootDiagUnit τ a * (ω.map fun i => weylElt τ K i 1).prod * (rootDiagUnit τ a)⁻¹) := by
          group
      _ = torusElt τ K i (a i) * weylElt τ K i 1 *
          (t * (ω.map fun i => weylElt τ K i 1).prod) := by
          rw [rootDiagUnit_conj_weylElt_one, h]
      _ = _ := by group

theorem exists_conj_canonicalRep
    (a : Fin τ.rank → Kˣ) (w : WeylGroup τ) :
    ∃ t ∈ torusGroup τ K, rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w *
      (rootDiagUnit τ a)⁻¹ = t * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact exists_conj_list_prod_weylElt a ω

theorem rootVec_ne_zero
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) : rootVec τ K β ≠ 0 := by
  rw [rootVec_eq_single hβ]
  exact Finsupp.single_ne_zero.2 one_ne_zero

theorem eq_of_smul_rootVec_eq_smul
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {c c' : K}
    (h : c • rootVec τ K β = c' • rootVec τ K β) : c = c' := by
  have h1 := congrArg (fun v : RootModule τ K => v (Sum.inr ⟨β, hβ⟩)) h
  simpa [rootVec_eq_single hβ] using h1

theorem rootDiagUnit_inv_rootVec
    (a : Fin τ.rank → Kˣ) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (((rootDiagUnit τ a)⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α) =
      (((rootChar a α)⁻¹ : Kˣ) : K) • rootVec τ K α := by
  change rootDiag a⁻¹ (rootVec τ K α) = _
  rw [rootDiag_rootVec _ hα, rootChar_inv_apply]

theorem conj_canonicalRep_rootVec
    (a : Fin τ.rank → Kˣ) (w : WeylGroup τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {c : Kˣ}
    (hc : (canonicalRep (coxeterSystem τ) K w : Module.End K (RootModule τ K)) (rootVec τ K α) =
      (c : K) • rootVec τ K (w • α)) :
    ((rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w * (rootDiagUnit τ a)⁻¹ : ModGL τ K) :
        Module.End K (RootModule τ K)) (rootVec τ K α) =
      ((((rootChar a α)⁻¹ * rootChar a (w • α)) : Kˣ) : K) • ((c : K) • rootVec τ K (w • α)) := by
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    rootDiagUnit_inv_rootVec a hα, map_smul, hc, map_smul, map_smul]
  rw [show ((rootDiagUnit τ a : ModGL τ K) : Module.End K (RootModule τ K)) = rootDiag a from rfl,
    rootDiag_rootVec _ (IsRoot.smul hα w)]
  simp only [smul_smul, Units.val_mul]
  congr 1
  ring

theorem conj_canonicalRep_eq_iff
    (a : Fin τ.rank → Kˣ) (w : WeylGroup τ) :
    rootDiagUnit τ a * canonicalRep (coxeterSystem τ) K w * (rootDiagUnit τ a)⁻¹ =
      canonicalRep (coxeterSystem τ) K w ↔ w ∈ rootCharStabilizer a := by
  have hmaps := mapsRootLines_canonicalRep (R := K) w
  constructor
  · intro h
    refine rootChar_smul_eq_of_forall_isRoot fun α hα => ?_
    obtain ⟨c, hc⟩ := hmaps α hα
    have h1 := conj_canonicalRep_rootVec a w hα hc
    rw [h, hc, smul_smul] at h1
    have h2 := eq_of_smul_rootVec_eq_smul (IsRoot.smul hα w) h1
    have h3 : ((((rootChar a α)⁻¹ * rootChar a (w • α)) : Kˣ) : K) = 1 :=
      mul_right_cancel₀ c.ne_zero (by rw [← h2, one_mul])
    have h4 : (rootChar a α)⁻¹ * rootChar a (w • α) = 1 := Units.ext h3
    rw [inv_mul_eq_one] at h4
    exact h4.symm
  · intro hw
    obtain ⟨t, ht, heq⟩ := exists_conj_canonicalRep a w
    suffices t = 1 by rw [heq, this, one_mul]
    refine Units.ext (rootModule_end_ext (fun j => ?_) fun β hβ => ?_)
    · rw [((triangular_borel_structure.{0, 0} τ K).2.1 t ht).1 j]
      rfl
    ·
      have hα : IsRoot τ (w⁻¹ • β) := IsRoot.smul hβ w⁻¹
      obtain ⟨c, hc⟩ := hmaps (w⁻¹ • β) hα
      have h1 := conj_canonicalRep_rootVec a w hα hc
      have hw' : ∀ v, rootChar a (w • v) = rootChar a v := hw
      rw [hw', inv_mul_cancel, Units.val_one, one_smul, heq, Units.val_mul,
        Module.End.mul_apply, hc, map_smul, smul_inv_smul] at h1
      have h2 : (c : K) • ((t : Module.End K (RootModule τ K)) (rootVec τ K β)) =
          (c : K) • rootVec τ K β := h1
      have h3 := congrArg (fun v => ((c⁻¹ : Kˣ) : K) • v) h2
      simp only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h3
      rw [h3]
      rfl

theorem rootSpan_le_centralizer
    (a : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : S ⊆ rootCharKernel a) :
    rootSpan τ K S ≤ Subgroup.centralizer {rootDiagUnit τ a} := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, ← conj_eq_iff_mem_centralizer, rootDiagUnit_conj_pinnedX a (hS hα).1,
    (hS hα).2, Units.val_one, one_mul]

theorem mem_rootSpan_inter_of_conj_eq
    (a : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (hfix : rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ = u) :
    u ∈ rootSpan τ K (rootCharKernel a ∩ S) := by
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
  have hαS : ∀ k, α k ∈ S := fun k => (e.symm k).2
  have hbij := hcoll α hα hrange
  obtain ⟨c, -, rfl⟩ := hbij.2.2 hu
  have hmap : rootDiagUnit τ a * (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod *
      (rootDiagUnit τ a)⁻¹ =
        (List.ofFn fun k => pinnedX τ K (α k) ((rootChar a (α k) : K) * c k)).prod := by
    have h := map_list_prod (MulAut.conj (rootDiagUnit τ a)).toMonoidHom
      (List.ofFn fun k => pinnedX τ K (α k) (c k))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_ofFn] at h
    rw [h]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    exact rootDiagUnit_conj_pinnedX a (hSroot _ (hαS k)) (c k)
  rw [hmap] at hfix
  have hc : (fun k => (rootChar a (α k) : K) * c k) = c :=
    hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) hfix
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hk : rootChar a (α k) = 1
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ rootCharKernel a ∩ S) => rootSubgroup τ K β) (α k)
      ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩ le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
  · have hck : c k = 0 := by
      have h1 : (rootChar a (α k) : K) * c k = c k := congrFun hc k
      have h2 : ((rootChar a (α k) : K) - 1) * c k = 0 := by
        linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact absurd (Units.ext (sub_eq_zero.1 h3)) hk
      · exact h3
    simp only [hck, pinnedX_zero]
    exact one_mem _

theorem Chevalley_toral_centralizer_Bruhat_factors
    (τ : Tag) (K : Type) [Field K]
    (a : Fin τ.rank → Kˣ) :
    (∀ g ∈ toralCentralizer τ K a, ∃ w ∈ rootCharStabilizer a, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ rootSpan τ K (rootCharKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ v ∈ rootSpan τ K (rootCharKernel a ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v) ∧
    (∀ (w w' : WeylGroup τ) (h h' u u' v v' : ModGL τ K), h ∈ torusGroup τ K →
      h' ∈ torusGroup τ K → u ∈ posUnipotent τ K → u' ∈ posUnipotent τ K →
      v ∈ rootSpan τ K (inversionSet w) → v' ∈ rootSpan τ K (inversionSet w') →
      h * u * canonicalRep (coxeterSystem τ) K w * v =
        h' * u' * canonicalRep (coxeterSystem τ) K w' * v' →
      w = w' ∧ h = h' ∧ u = u' ∧ v = v') ∧
    (∀ w ∈ rootCharStabilizer a, ∀ h ∈ torusGroup τ K,
      ∀ u ∈ rootSpan τ K (rootCharKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∀ v ∈ rootSpan τ K (rootCharKernel a ∩ inversionSet w),
        h * u * canonicalRep (coxeterSystem τ) K w * v ∈ toralCentralizer τ K a) ∧
    toralCentralizer τ K a = torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) ⊔
      Subgroup.closure ((fun w => canonicalRep (coxeterSystem τ) K w) '' rootCharStabilizer a) := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup τ K ≤ adjointGroup τ K := le_sup_left.trans hBC
  have hUC : posUnipotent τ K ≤ adjointGroup τ K := le_sup_right.trans hBC
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hIU : ∀ w : WeylGroup τ, rootSpan τ K (inversionSet w) ≤ posUnipotent τ K := fun w =>
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin τ.rank → ℤ |
      IsRoot τ β ∧ 0 < height β}) => rootSubgroup τ K β) α ⟨hα.1, hα.2.1⟩ le_rfl
  have hKC : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ rootCharKernel a →
      rootSpan τ K S ≤ Subgroup.centralizer {rootDiagUnit τ a} := fun hS =>
    rootSpan_le_centralizer a hS
  have hfactor : ∀ g ∈ adjointGroup τ K, ∃ w : WeylGroup τ, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ posUnipotent τ K, ∃ v ∈ rootSpan τ K (inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
    intro g hg
    have hg' : g ∈ (adjointGroup τ K : Set (ModGL τ K)) := hg
    rw [(bruhat_decomposition τ K).1, Set.mem_iUnion] at hg'
    obtain ⟨w, hw⟩ := hg'
    obtain ⟨⟨b, v⟩, ⟨hb, hv⟩, hbv⟩ := ((bruhat_cell_factorization τ K).1 w).2.2 hw
    have hb' : b ∈ (torusGroup τ K : Set (ModGL τ K)) * (posUnipotent τ K : Set (ModGL τ K)) := by
      rw [← hTB.2.2.2.2.1]
      exact hb
    obtain ⟨h, hh, u, hu, rfl⟩ := hb'
    exact ⟨w, h, hh, u, hu, v, hv, hbv.symm⟩
  have huniq : ∀ (w w' : WeylGroup τ) (h h' u u' v v' : ModGL τ K), h ∈ torusGroup τ K →
      h' ∈ torusGroup τ K → u ∈ posUnipotent τ K → u' ∈ posUnipotent τ K →
      v ∈ rootSpan τ K (inversionSet w) → v' ∈ rootSpan τ K (inversionSet w') →
      h * u * canonicalRep (coxeterSystem τ) K w * v =
        h' * u' * canonicalRep (coxeterSystem τ) K w' * v' →
      w = w' ∧ h = h' ∧ u = u' ∧ v = v' := by
    intro w w' h h' u u' v v' hh hh' hu hu' hv hv' heq
    have hb : h * u ∈ borelGroup τ K :=
      mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right hu)
    have hb' : h' * u' ∈ borelGroup τ K :=
      mul_mem (Subgroup.mem_sup_left hh') (Subgroup.mem_sup_right hu')
    have hc := ((bruhat_cell_factorization τ K).1 w).1 (x := (h * u, v)) ⟨hb, hv⟩
    have hc' := ((bruhat_cell_factorization τ K).1 w').1 (x := (h' * u', v')) ⟨hb', hv'⟩
    simp only at hc hc'
    have hww : w = w' := by
      by_contra hne
      have hdis := (bruhat_decomposition τ K).2.1 w w' hne
      rw [heq] at hc
      exact Set.disjoint_left.1 hdis hc hc'
    subst hww
    have hinj := ((bruhat_cell_factorization τ K).1 w).2.1 (x₁ := (h * u, v))
      (x₂ := (h' * u', v')) ⟨hb, hv⟩ ⟨hb', hv'⟩ heq
    simp only [Prod.mk.injEq] at hinj
    obtain ⟨hhu, hvv⟩ := hinj
    obtain ⟨h1, h2⟩ := hTB.2.2.2.2.2.2.1 h hh h' hh' u hu u' hu' hhu
    exact ⟨rfl, h1, h2, hvv⟩
  have hprod : ∀ w ∈ rootCharStabilizer a, ∀ h ∈ torusGroup τ K,
      ∀ u ∈ rootSpan τ K (rootCharKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∀ v ∈ rootSpan τ K (rootCharKernel a ∩ inversionSet w),
        h * u * canonicalRep (coxeterSystem τ) K w * v ∈ toralCentralizer τ K a := by
    intro w hw h hh u hu v hv
    have huU : u ∈ posUnipotent τ K :=
      (rootSpan_mono (Set.inter_subset_right)) hu
    have hvU : v ∈ posUnipotent τ K :=
      hIU w ((rootSpan_mono (Set.inter_subset_right)) hv)
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (mul_mem (hTC hh) (hUC huU))
      (canonicalRep_mem_adjointGroup _ K w)) (hUC hvU), ?_⟩
    refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
    · exact conj_eq_iff_mem_centralizer.1 (conj_rootDiagUnit_of_mem_torusGroup a hh)
    · exact hKC Set.inter_subset_left hu
    · exact conj_eq_iff_mem_centralizer.1 ((conj_canonicalRep_eq_iff a w).2 hw)
    · exact hKC Set.inter_subset_left hv
  have hX : ∀ g ∈ toralCentralizer τ K a, ∃ w ∈ rootCharStabilizer a, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ rootSpan τ K (rootCharKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ v ∈ rootSpan τ K (rootCharKernel a ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
    intro g hg
    obtain ⟨hgC, hgfix⟩ := mem_toralCentralizer.1 hg
    obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := hfactor g hgC
    set d := rootDiagUnit τ a with hd
    obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep a w
    have hdu : d * u * d⁻¹ ∈ posUnipotent τ K := by
      have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 a).2.1
      rw [← this]
      exact ⟨u, hu, rfl⟩
    have hdv : d * v * d⁻¹ ∈ rootSpan τ K (inversionSet w) := by
      have : (rootSpan τ K (inversionSet w)).map (MulAut.conj d).toMonoidHom =
          rootSpan τ K (inversionSet w) :=
        map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a hα.1
      rw [← this]
      exact ⟨v, hv, rfl⟩
    have hu' : t⁻¹ * (d * u * d⁻¹) * t ∈ posUnipotent τ K := by
      have hN := hTB.2.2.1 (inv_mem ht)
      have := (Subgroup.mem_normalizer_iff.1 hN (d * u * d⁻¹)).1 hdu
      simpa using this
    have heq : h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem τ) K w *
        (d * v * d⁻¹) = h * u * canonicalRep (coxeterSystem τ) K w * v := by
      calc h * t * (t⁻¹ * (d * u * d⁻¹) * t) * canonicalRep (coxeterSystem τ) K w *
            (d * v * d⁻¹) =
          (d * h * d⁻¹) * (d * u * d⁻¹) * (t * canonicalRep (coxeterSystem τ) K w) *
            (d * v * d⁻¹) := by
            rw [conj_rootDiagUnit_of_mem_torusGroup a hh]
            group
        _ = (d * h * d⁻¹) * (d * u * d⁻¹) * (d * canonicalRep (coxeterSystem τ) K w * d⁻¹) *
            (d * v * d⁻¹) := by rw [hnt]
        _ = d * (h * u * canonicalRep (coxeterSystem τ) K w * v) * d⁻¹ := by group
        _ = h * u * canonicalRep (coxeterSystem τ) K w * v := hgfix
    obtain ⟨-, h1, h2, h3⟩ := huniq w w (h * t) h _ u _ v (mul_mem hh ht) hh hu' hu hdv hv heq
    have ht1 : t = 1 := by
      have := h1
      rwa [mul_eq_left] at this
    subst ht1
    have hufix : d * u * d⁻¹ = u := by simpa using h2
    have hw : w ∈ rootCharStabilizer a := by
      rw [← conj_canonicalRep_eq_iff, ← hd, hnt, one_mul]
    refine ⟨w, hw, h, hh, u, ?_, v, ?_, rfl⟩
    · have := mem_rootSpan_inter_of_conj_eq a hposfin (fun β hβ => hβ.1)
        (fun α hα hr => (positive_root_collection τ K).2 α hα hr) hu hufix
      exact this
    · exact mem_rootSpan_inter_of_conj_eq a (inversionSet_finite w) (fun β hβ => hβ.1)
        (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hv h3
  refine ⟨hX, huniq, hprod, le_antisymm ?_ ?_⟩
  · intro g hg
    obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := hX g hg
    have hKS : ∀ {S : Set (Fin τ.rank → ℤ)}, S ⊆ rootCharKernel a →
        rootSpan τ K S ≤ torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a) ⊔
          Subgroup.closure ((fun w => canonicalRep (coxeterSystem τ) K w) ''
            rootCharStabilizer a) := fun hS =>
      (rootSpan_mono hS).trans (le_sup_right.trans le_sup_left)
    refine mul_mem (mul_mem (mul_mem ?_ (hKS Set.inter_subset_left hu)) ?_)
      (hKS Set.inter_subset_left hv)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hh)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨w, hw, rfl⟩)
  · refine sup_le (sup_le ?_ ?_) ?_
    · intro h hh
      simpa [canonicalRep_one] using
        hprod 1 (fun v => by rw [one_smul]) h hh 1 (one_mem _) 1 (one_mem _)
    · intro u hu
      exact Subgroup.mem_inf.2 ⟨rootSpan_le_adjointGroup K _ hu, hKC le_rfl hu⟩
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨w, hw, rfl⟩
      simpa using hprod w hw 1 (one_mem _) 1 (one_mem _) 1 (one_mem _)

end CFSG.LieType.Chevalley
