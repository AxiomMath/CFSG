module

public import CFSG.LieType.AlgebraicGroups.ToralRootCover

public noncomputable section

namespace CFSG.HardMathSupport.Timmesfeld.Torality

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped Pointwise

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K] {ι : Type}

variable (τ K) in
@[expose] def familyCentralizer (a : ι → Fin τ.rank → Kˣ) : Subgroup (ModGL τ K) :=
  adjointGroup τ K ⊓ ⨅ i, Subgroup.centralizer {rootDiagUnit τ (a i)}

@[expose] def familyKernel (a : ι → Fin τ.rank → Kˣ) : Set (Fin τ.rank → ℤ) :=
  {α | IsRoot τ α ∧ ∀ i, rootChar (a i) α = 1}

@[expose] def familyStabilizer (a : ι → Fin τ.rank → Kˣ) : Set (WeylGroup τ) :=
  {w | ∀ i, w ∈ rootCharStabilizer (a i)}

@[expose] def familyGroup
    (a : ι → Fin τ.rank → Kˣ) : Subgroup (ModGL τ K) :=
  torusGroup τ K ⊔ rootSpan τ K (familyKernel a)

theorem mem_familyCentralizer {a : ι → Fin τ.rank → Kˣ} {g : ModGL τ K} :
    g ∈ familyCentralizer τ K a ↔
      g ∈ adjointGroup τ K ∧ ∀ i, rootDiagUnit τ (a i) * g * (rootDiagUnit τ (a i))⁻¹ = g := by
  rw [familyCentralizer, Subgroup.mem_inf, Subgroup.mem_iInf]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [conj_eq_iff_mem_centralizer]

@[expose] def familyChar (a : ι → Fin τ.rank → Kˣ) :
    Multiplicative (Fin τ.rank → ℤ) →* (ι → Kˣ) :=
  MonoidHom.pi fun i => rootCharHom (a i)

theorem kernelRoots_familyChar (a : ι → Fin τ.rank → Kˣ) :
    kernelRoots (familyChar a) = familyKernel a := by
  ext α
  change IsRoot τ α ∧ familyChar a (Multiplicative.ofAdd α) = 1 ↔ _
  refine and_congr_right fun _ => ?_
  rw [funext_iff]
  exact forall_congr' fun i => Iff.rfl

theorem familyStabilizer_inv {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer a) : w⁻¹ ∈ familyStabilizer a := fun i =>
  (rootCharStabilizerSubgroup (a i)).inv_mem (hw i)

theorem image_familyKernel {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer a) : (fun α => w • α) '' familyKernel a = familyKernel a := by
  have hw' := familyStabilizer_inv hw
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hαa⟩, rfl⟩
    exact ⟨IsRoot.smul hα w, fun i => (hw i α).trans (hαa i)⟩
  · rintro ⟨hβ, hβa⟩
    exact ⟨w⁻¹ • β, ⟨IsRoot.smul hβ w⁻¹, fun i => (hw' i β).trans (hβa i)⟩, smul_inv_smul w β⟩

section Main


theorem canonicalRep_mem_normalizer_of_image {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : (fun α => w • α) '' familyKernel a = familyKernel a) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (familyGroup (K := K) a : Set (ModGL τ K)) := by
  have hT := map_conj_eq_of_mem_normalizer (canonicalRep_mem_normalizer (R := K) w)
  have hS := (canonical_weyl_root_transport τ K).1 w (familyKernel a) fun α hα => hα.1
  rw [hw] at hS
  have hmap : (familyGroup (K := K) a).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom = familyGroup a := by
    rw [familyGroup, Subgroup.map_sup, hT, hS]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hmap
  rw [Subgroup.coe_map] at h
  exact h

theorem canonicalRep_mem_normalizer_familyGroup {a : ι → Fin τ.rank → Kˣ} {w : WeylGroup τ}
    (hw : w ∈ familyStabilizer a) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (familyGroup (K := K) a : Set (ModGL τ K)) :=
  canonicalRep_mem_normalizer_of_image (image_familyKernel hw)

theorem familyGroup_le_familyCentralizer (a : ι → Fin τ.rank → Kˣ) :
    familyGroup (K := K) a ≤ familyCentralizer τ K a :=
  sup_le (fun _ hh => mem_familyCentralizer.2
      ⟨((triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.2.2 K).1
        (Subgroup.mem_sup_left hh), fun i => conj_rootDiagUnit_of_mem_torusGroup (a i) hh⟩)
    fun _ hu => mem_familyCentralizer.2
      ⟨rootSpan_le_adjointGroup K _ hu, fun i => conj_eq_iff_mem_centralizer.2
        (rootSpan_le_centralizer (a i) (S := familyKernel a) (fun _ hα => ⟨hα.1, hα.2 i⟩) hu)⟩

end Main

section Coordinates


theorem coords_eq_zero_of_conj_eq_family (a : ι → Fin τ.rank → Kˣ) {m : ℕ}
    (α : Fin m → Fin τ.rank → ℤ) (hαroot : ∀ k, IsRoot τ (α k))
    (hinj : ∀ c c' : Fin m → K, (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod =
      (List.ofFn fun k => pinnedX τ K (α k) (c' k)).prod → c = c')
    {c : Fin m → K}
    (hfix : ∀ i, rootDiagUnit τ (a i) * (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod *
      (rootDiagUnit τ (a i))⁻¹ = (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod) :
    ∀ k, ¬ (∀ i, rootChar (a i) (α k) = 1) → c k = 0 := by
  intro k hk
  obtain ⟨i, hi⟩ := not_forall.1 hk
  have hmap : rootDiagUnit τ (a i) * (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod *
      (rootDiagUnit τ (a i))⁻¹ =
        (List.ofFn fun k => pinnedX τ K (α k) ((rootChar (a i) (α k) : K) * c k)).prod := by
    have h := map_list_prod (MulAut.conj (rootDiagUnit τ (a i))).toMonoidHom
      (List.ofFn fun k => pinnedX τ K (α k) (c k))
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, List.map_ofFn] at h
    rw [h]
    refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
    exact rootDiagUnit_conj_pinnedX (a i) (hαroot k) (c k)
  have hc : (fun k => (rootChar (a i) (α k) : K) * c k) = c :=
    hinj _ _ (by rw [← hmap]; exact hfix i)
  have h1 : (rootChar (a i) (α k) : K) * c k = c k := congrFun hc k
  have h2 : ((rootChar (a i) (α k) : K) - 1) * c k = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (Units.ext (sub_eq_zero.1 h3)) hi
  · exact h3

theorem mem_rootSpan_inter_of_conj_eq_family (a : ι → Fin τ.rank → Kˣ)
    {S : Set (Fin τ.rank → ℤ)}
    (hS : S.Finite) (hSroot : ∀ α ∈ S, IsRoot τ α)
    (hcoll : ∀ {m : ℕ} (α : Fin m → Fin τ.rank → ℤ), Function.Injective α → Set.range α = S →
      Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX τ K (α k) (c k)).prod)
        Set.univ (rootSpan τ K S))
    {u : ModGL τ K} (hu : u ∈ rootSpan τ K S)
    (hfix : ∀ i, rootDiagUnit τ (a i) * u * (rootDiagUnit τ (a i))⁻¹ = u) :
    u ∈ rootSpan τ K (familyKernel a ∩ S) := by
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
  have hz := coords_eq_zero_of_conj_eq_family a α (fun k => hSroot _ (hαS k))
    (fun c c' h => hbij.2.1 (Set.mem_univ _) (Set.mem_univ _) h) hfix
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  by_cases hk : ∀ i, rootChar (a i) (α k) = 1
  · exact le_iSup₂_of_le (f := fun β (_ : β ∈ familyKernel a ∩ S) => rootSubgroup τ K β) (α k)
      ⟨⟨hSroot _ (hαS k), hk⟩, hαS k⟩ le_rfl (Subgroup.subset_closure ⟨c k, rfl⟩)
  · show pinnedX τ K (α k) (c k) ∈ _
    rw [hz k hk, pinnedX_zero]
    exact one_mem _

end Coordinates

section Factors


theorem familyCentralizer_factors (τ : Tag) (K : Type) [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) :
    ∀ g ∈ familyCentralizer τ K a, ∃ w ∈ familyStabilizer a, ∃ h ∈ torusGroup τ K,
      ∃ u ∈ rootSpan τ K (familyKernel a ∩ {α | IsRoot τ α ∧ 0 < height α}),
      ∃ v ∈ rootSpan τ K (familyKernel a ∩ inversionSet w),
        g = h * u * canonicalRep (coxeterSystem τ) K w * v := by
  have hTB := triangular_borel_structure.{0, 0} τ K
  have hBC : borelGroup τ K ≤ adjointGroup τ K := (hTB.2.2.2.2.2.2.2.2.2.2.2 K).1
  have hTC : torusGroup τ K ≤ adjointGroup τ K := le_sup_left.trans hBC
  have hUC : posUnipotent τ K ≤ adjointGroup τ K := le_sup_right.trans hBC
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  have hIU : ∀ w : WeylGroup τ, rootSpan τ K (inversionSet w) ≤ posUnipotent τ K := fun w =>
    iSup₂_le fun α hα => le_iSup₂_of_le (f := fun β (_ : β ∈ {β : Fin τ.rank → ℤ |
      IsRoot τ β ∧ 0 < height β}) => rootSubgroup τ K β) α ⟨hα.1, hα.2.1⟩ le_rfl
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
  have hposfin : {β : Fin τ.rank → ℤ | IsRoot τ β ∧ 0 < height β}.Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hβ.1
  intro g hg
  obtain ⟨hgC, hgfix⟩ := mem_familyCentralizer.1 hg
  obtain ⟨w, h, hh, u, hu, v, hv, rfl⟩ := hfactor g hgC
  have key : ∀ i, w ∈ rootCharStabilizer (a i) ∧
      rootDiagUnit τ (a i) * u * (rootDiagUnit τ (a i))⁻¹ = u ∧
      rootDiagUnit τ (a i) * v * (rootDiagUnit τ (a i))⁻¹ = v := by
    intro i
    set d := rootDiagUnit τ (a i) with hd
    obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep (a i) w
    have hdu : d * u * d⁻¹ ∈ posUnipotent τ K := by
      have := ((chevalley_root_character_and_field_conjugation τ K).2.2.2.1 (a i)).2.1
      rw [← this]
      exact ⟨u, hu, rfl⟩
    have hdv : d * v * d⁻¹ ∈ rootSpan τ K (inversionSet w) := by
      have : (rootSpan τ K (inversionSet w)).map (MulAut.conj d).toMonoidHom =
          rootSpan τ K (inversionSet w) :=
        map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup (a i) hα.1
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
            rw [conj_rootDiagUnit_of_mem_torusGroup (a i) hh]
            group
        _ = (d * h * d⁻¹) * (d * u * d⁻¹) * (d * canonicalRep (coxeterSystem τ) K w * d⁻¹) *
            (d * v * d⁻¹) := by rw [hnt]
        _ = d * (h * u * canonicalRep (coxeterSystem τ) K w * v) * d⁻¹ := by group
        _ = h * u * canonicalRep (coxeterSystem τ) K w * v := hgfix i
    obtain ⟨-, h1, h2, h3⟩ := huniq w w (h * t) h _ u _ v (mul_mem hh ht) hh hu' hu hdv hv heq
    have ht1 : t = 1 := by
      have := h1
      rwa [mul_eq_left] at this
    subst ht1
    have hufix : d * u * d⁻¹ = u := by simpa using h2
    have hw : w ∈ rootCharStabilizer (a i) := by
      rw [← conj_canonicalRep_eq_iff, ← hd, hnt, one_mul]
    exact ⟨hw, hufix, h3⟩
  refine ⟨w, fun i => (key i).1, h, hh, u, ?_, v, ?_, rfl⟩
  · exact mem_rootSpan_inter_of_conj_eq_family a hposfin (fun β hβ => hβ.1)
      (fun α hα hr => (positive_root_collection τ K).2 α hα hr) hu fun i => (key i).2.1
  · exact mem_rootSpan_inter_of_conj_eq_family a (inversionSet_finite w) (fun β hβ => hβ.1)
      (fun α hα hr => (bruhat_cell_factorization τ K).2.1 w α hα hr) hv fun i => (key i).2.2

theorem familyCentralizer_le_mul (τ : Tag) (K : Type) [Field K] {ι : Type}
    (a : ι → Fin τ.rank → Kˣ) {g : ModGL τ K} (hg : g ∈ familyCentralizer τ K a) :
    ∃ w ∈ familyStabilizer a, ∃ m ∈ familyGroup (K := K) a,
      g = m * canonicalRep (coxeterSystem τ) K w := by
  obtain ⟨w, hw, h, hh, u, hu, v, hv, rfl⟩ := familyCentralizer_factors τ K a g hg
  have hnorm := canonicalRep_mem_normalizer_familyGroup (K := K) hw
  have huM : u ∈ familyGroup (K := K) a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hu)
  have hvM : v ∈ familyGroup (K := K) a :=
    Subgroup.mem_sup_right (rootSpan_mono Set.inter_subset_left hv)
  have hn' : canonicalRep (coxeterSystem τ) K w * v * (canonicalRep (coxeterSystem τ) K w)⁻¹ ∈
      familyGroup (K := K) a :=
    (Subgroup.mem_normalizer_iff.1 hnorm v).1 hvM
  refine ⟨w, hw, h * u * (canonicalRep (coxeterSystem τ) K w * v *
    (canonicalRep (coxeterSystem τ) K w)⁻¹), mul_mem (mul_mem (Subgroup.mem_sup_left hh) huM) hn', ?_⟩
  group

end Factors

end CFSG.HardMathSupport.Timmesfeld.Torality
