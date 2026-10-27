module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylRootTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type} [CommRing R]

@[expose] def MapsRootLines
    (g : (Module.End R (RootModule τ R))ˣ) (w : WeylGroup τ) : Prop :=
  ∀ α, IsRoot τ α → ∃ c : Rˣ,
    (g : Module.End R (RootModule τ R)) (rootVec τ R α) = (c : R) • rootVec τ R (w • α)

theorem MapsRootLines.mul
    {g g' : (Module.End R (RootModule τ R))ˣ} {w w' : WeylGroup τ}
    (hg : MapsRootLines g w) (hg' : MapsRootLines g' w') : MapsRootLines (g * g') (w * w') := by
  intro α hα
  obtain ⟨c', h'⟩ := hg' α hα
  obtain ⟨c, h⟩ := hg (w' • α) (IsRoot.smul hα w')
  refine ⟨c' * c, ?_⟩
  rw [Units.val_mul, Module.End.mul_apply, h', map_smul, h, smul_smul, mul_smul w w' α,
    Units.val_mul]

theorem MapsRootLines.inv
    {g : (Module.End R (RootModule τ R))ˣ} {w : WeylGroup τ}
    (hg : MapsRootLines g w) : MapsRootLines g⁻¹ w⁻¹ := by
  intro β hβ
  obtain ⟨c, h⟩ := hg (w⁻¹ • β) (IsRoot.smul hβ w⁻¹)
  rw [smul_inv_smul] at h
  refine ⟨c⁻¹, ?_⟩
  have h2 := congrArg (fun v => ((g⁻¹ : (Module.End R (RootModule τ R))ˣ) :
    Module.End R (RootModule τ R)) v) h
  simp only [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply, map_smul] at h2
  rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem eq_of_smul_rootVec_eq
    [Nontrivial R] {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) {c c' : Rˣ}
    (h : (c : R) • rootVec τ R β = (c' : R) • rootVec τ R γ) : β = γ := by
  by_contra hne
  have h1 := congrArg (fun v : RootModule τ R => v (Sum.inr ⟨β, hβ⟩)) h
  simp only [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot hγ, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at h1
  have hne' : (Sum.inr ⟨γ, hγ⟩ : Label τ) ≠ Sum.inr ⟨β, hβ⟩ := fun h => hne (by
    injection h with h
    exact (congrArg Subtype.val h).symm)
  rw [Finsupp.single_apply, ite_eq_right hne', mul_zero] at h1
  exact c.ne_zero h1

theorem MapsRootLines.unique
    [Nontrivial R] {g : (Module.End R (RootModule τ R))ˣ}
    {w w' : WeylGroup τ} (hg : MapsRootLines g w) (hg' : MapsRootLines g w') : w = w' :=
  ext_single fun i => by
    obtain ⟨c, h⟩ := hg _ (isRoot_single τ i)
    obtain ⟨c', h'⟩ := hg' _ (isRoot_single τ i)
    exact eq_of_smul_rootVec_eq (IsRoot.smul (isRoot_single τ i) w)
      (IsRoot.smul (isRoot_single τ i) w') (h.symm.trans h')

theorem mapsRootLines_one
    : MapsRootLines (1 : (Module.End R (RootModule τ R))ˣ) 1 :=
  fun α _ => ⟨1, by simp⟩

theorem mapsRootLines_of_mem_torusGroup
    {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ torusGroup τ R) : MapsRootLines g 1 := fun α hα => by
  obtain ⟨c, hc⟩ := (torusGroup_le_diagonalGroup hg).2 α hα
  exact ⟨c, by rw [hc, one_smul]⟩

theorem mapsRootLines_weylElt
    (i : Fin τ.rank) :
    MapsRootLines (weylElt τ R i 1) (simple τ i) := fun α hα => by
  refine ⟨(-1) ^ stringDown τ i α * (1 ^ (-∑ j, τ.cartan i j * α j) : Rˣ), ?_⟩
  rw [weylElt_rootVec i 1 hα, simple_smul]
  congr 1

theorem mapsRootLines_list_prod
    (ω : List (Fin τ.rank)) :
    MapsRootLines (ω.map fun i => weylElt τ R i 1).prod ((coxeterSystem τ).wordProd ω) := by
  induction ω with
  | nil => exact mapsRootLines_one
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons, (coxeterSystem τ).wordProd_cons]
    exact (mapsRootLines_weylElt i).mul ih

theorem mapsRootLines_canonicalRep
    (w : WeylGroup τ) :
    MapsRootLines (canonicalRep (coxeterSystem τ) R w) w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem τ).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact mapsRootLines_list_prod ω

theorem canonicalRep_mem_normalizer
    (w : WeylGroup τ) :
    canonicalRep (coxeterSystem τ) R w ∈
      Subgroup.normalizer (torusGroup τ R : Set (Module.End R (RootModule τ R))ˣ) :=
  (canonical_weyl_root_transport τ R).2.2 w

theorem canonicalRep_mul_mem
    (w w' : WeylGroup τ) :
    ∃ k ∈ torusGroup τ R, canonicalRep (coxeterSystem τ) R w * canonicalRep (coxeterSystem τ) R w' =
      k * canonicalRep (coxeterSystem τ) R (w * w') := by
  induction w using (coxeterSystem τ).simple_induction_left with
  | one => exact ⟨1, Subgroup.one_mem _, by rw [canonicalRep_one, one_mul, one_mul, one_mul]⟩
  | mul_simple_left u i ih =>
    obtain ⟨k₂, hk₂, h₂⟩ := ih
    have hstep : ∀ v : WeylGroup τ, ∃ k ∈ torusGroup τ R,
        weylElt τ R i 1 * canonicalRep (coxeterSystem τ) R v =
          k * canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).simple i * v) := fun v => by
      rw [weylElt_mul_canonicalRep]
      split_ifs
      · exact ⟨1, Subgroup.one_mem _, (one_mul _).symm⟩
      · exact ⟨_, torusElt_mem_torusGroup i (-1), rfl⟩
    obtain ⟨k₁, hk₁, h₁⟩ := hstep u
    obtain ⟨k₃, hk₃, h₃⟩ := hstep (u * w')
    have hni := weylElt_mem_normalizer_torus τ R i 1
    have hconj : weylElt τ R i 1 * k₂ * (weylElt τ R i 1)⁻¹ ∈ torusGroup τ R :=
      (Subgroup.mem_normalizer_iff.1 hni k₂).1 hk₂
    refine ⟨k₁⁻¹ * (weylElt τ R i 1 * k₂ * (weylElt τ R i 1)⁻¹) * k₃,
      mul_mem (mul_mem (inv_mem hk₁) hconj) hk₃, ?_⟩
    have e₁ : canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).simple i * u) =
        k₁⁻¹ * (weylElt τ R i 1 * canonicalRep (coxeterSystem τ) R u) := by
      rw [h₁, inv_mul_cancel_left]
    calc canonicalRep (coxeterSystem τ) R ((coxeterSystem τ).simple i * u) *
          canonicalRep (coxeterSystem τ) R w' =
        k₁⁻¹ * weylElt τ R i 1 *
          (canonicalRep (coxeterSystem τ) R u * canonicalRep (coxeterSystem τ) R w') := by
          rw [e₁]
          group
      _ = k₁⁻¹ * (weylElt τ R i 1 * k₂ * (weylElt τ R i 1)⁻¹) *
          (weylElt τ R i 1 * canonicalRep (coxeterSystem τ) R (u * w')) := by
          rw [h₂]
          group
      _ = _ := by
          rw [h₃, mul_assoc ((coxeterSystem τ).simple i) u w']
          group

@[expose] def torusWeylCosets
    (τ : Tag) (R : Type) [CommRing R] :
    Subgroup (Module.End R (RootModule τ R))ˣ where
  carrier := {g | ∃ w : WeylGroup τ, ∃ k ∈ torusGroup τ R,
    g = k * canonicalRep (coxeterSystem τ) R w}
  one_mem' := ⟨1, 1, Subgroup.one_mem _, by rw [canonicalRep_one, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨w, k, hk, rfl⟩ ⟨w', k', hk', rfl⟩
    obtain ⟨k'', hk'', h⟩ := canonicalRep_mul_mem (R := R) w w'
    have hc : canonicalRep (coxeterSystem τ) R w * k' *
        (canonicalRep (coxeterSystem τ) R w)⁻¹ ∈ torusGroup τ R :=
      (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer w) k').1 hk'
    refine ⟨w * w', k * (canonicalRep (coxeterSystem τ) R w * k' *
      (canonicalRep (coxeterSystem τ) R w)⁻¹) * k'', mul_mem (mul_mem hk hc) hk'', ?_⟩
    calc k * canonicalRep (coxeterSystem τ) R w * (k' * canonicalRep (coxeterSystem τ) R w') =
        k * (canonicalRep (coxeterSystem τ) R w * k' * (canonicalRep (coxeterSystem τ) R w)⁻¹) *
          (canonicalRep (coxeterSystem τ) R w * canonicalRep (coxeterSystem τ) R w') := by group
      _ = _ := by
          rw [h]
          group
  inv_mem' := by
    rintro _ ⟨w, k, hk, rfl⟩
    obtain ⟨k₀, hk₀, h₀⟩ := canonicalRep_mul_mem (R := R) w⁻¹ w
    rw [inv_mul_cancel, canonicalRep_one, mul_one] at h₀
    have hn := inv_mem (canonicalRep_mem_normalizer (R := R) w)
    have hc : (canonicalRep (coxeterSystem τ) R w)⁻¹ * k⁻¹ *
        (canonicalRep (coxeterSystem τ) R w)⁻¹⁻¹ ∈ torusGroup τ R :=
      (Subgroup.mem_normalizer_iff.1 hn k⁻¹).1 (inv_mem hk)
    refine ⟨w⁻¹, (canonicalRep (coxeterSystem τ) R w)⁻¹ * k⁻¹ *
      (canonicalRep (coxeterSystem τ) R w)⁻¹⁻¹ * k₀⁻¹, mul_mem hc (inv_mem hk₀), ?_⟩
    have e : (canonicalRep (coxeterSystem τ) R w)⁻¹ =
        k₀⁻¹ * canonicalRep (coxeterSystem τ) R w⁻¹ := by
      rw [eq_inv_mul_iff_mul_eq, ← h₀, mul_assoc, mul_inv_cancel, mul_one]
    rw [mul_inv_rev, mul_assoc _ k₀⁻¹, ← e, inv_inv]
    group

theorem monomialSubgroup_le_torusWeylCosets
    : monomialSubgroup τ R ≤ torusWeylCosets τ R := by
  refine sup_le (fun k hk => ⟨1, k, hk, by rw [canonicalRep_one, mul_one]⟩)
    ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨i, rfl⟩
  exact ⟨simple τ i, 1, Subgroup.one_mem _, by rw [canonicalRep_simple, one_mul]⟩

theorem exists_mapsRootLines_of_mem
    {g : (Module.End R (RootModule τ R))ˣ}
    (hg : g ∈ monomialSubgroup τ R) : ∃ w, MapsRootLines g w := by
  obtain ⟨w, k, hk, rfl⟩ := monomialSubgroup_le_torusWeylCosets hg
  exact ⟨w, by simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)⟩

instance torusGroup_subgroupOf_monomialSubgroup_normal
    (τ : Tag) (R : Type) [CommRing R] :
    ((torusGroup τ R).subgroupOf (monomialSubgroup τ R)).Normal :=
  ((triangular_borel_structure.{0, 0} τ R).2.2.2.2.2.2.2.2.2.2).1

variable (τ R) in
@[expose] def weylQuotientHom
    [Nontrivial R] : monomialSubgroup τ R →* WeylGroup τ where
  toFun g := (exists_mapsRootLines_of_mem g.2).choose
  map_one' := ((exists_mapsRootLines_of_mem (one_mem (monomialSubgroup τ R))).choose_spec).unique
    mapsRootLines_one
  map_mul' g g' := ((exists_mapsRootLines_of_mem (g * g').2).choose_spec).unique
    ((exists_mapsRootLines_of_mem g.2).choose_spec.mul
      (exists_mapsRootLines_of_mem g'.2).choose_spec)

theorem mapsRootLines_weylQuotientHom
    [Nontrivial R] (g : monomialSubgroup τ R) :
    MapsRootLines (g : (Module.End R (RootModule τ R))ˣ) (weylQuotientHom τ R g) :=
  (exists_mapsRootLines_of_mem g.2).choose_spec

theorem weylQuotientHom_eq
    [Nontrivial R] {g : monomialSubgroup τ R} {w : WeylGroup τ}
    (h : MapsRootLines (g : (Module.End R (RootModule τ R))ˣ) w) : weylQuotientHom τ R g = w :=
  (mapsRootLines_weylQuotientHom g).unique h

theorem torusElt_mem_monomialSubgroup
    (i : Fin τ.rank) (t : Rˣ) :
    torusElt τ R i t ∈ monomialSubgroup τ R :=
  Subgroup.mem_sup_left (torusElt_mem_torusGroup i t)

theorem weylElt_mem_monomialSubgroup
    (i : Fin τ.rank) :
    weylElt τ R i 1 ∈ monomialSubgroup τ R :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨i, rfl⟩)

theorem Weyl_normalizer_quotient
    (τ : Tag) (R : Type) [CommRing R] [Nontrivial R] :
    (∀ g ∈ monomialSubgroup τ R, ∃! w : WeylGroup τ, MapsRootLines g w) ∧
    (∃ ρ : monomialSubgroup τ R →* WeylGroup τ, Function.Surjective ρ ∧
      (∀ g : monomialSubgroup τ R, MapsRootLines (g : (Module.End R (RootModule τ R))ˣ) (ρ g)) ∧
      (∀ i t, ρ ⟨torusElt τ R i t, torusElt_mem_monomialSubgroup i t⟩ = 1) ∧
      (∀ i, ρ ⟨weylElt τ R i 1, weylElt_mem_monomialSubgroup i⟩ = simple τ i) ∧
      ρ.ker = (torusGroup τ R).subgroupOf (monomialSubgroup τ R)) ∧
    ∃! ψ : WeylGroup τ ≃*
        monomialSubgroup τ R ⧸ (torusGroup τ R).subgroupOf (monomialSubgroup τ R),
      ∀ i, ψ (simple τ i) = QuotientGroup.mk ⟨weylElt τ R i 1, weylElt_mem_monomialSubgroup i⟩ := by
  set ρ := weylQuotientHom τ R
  have hd : ∀ i t, ρ ⟨torusElt τ R i t, torusElt_mem_monomialSubgroup i t⟩ = 1 := fun i t =>
    weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (torusElt_mem_torusGroup i t))
  have hn : ∀ i, ρ ⟨weylElt τ R i 1, weylElt_mem_monomialSubgroup i⟩ = simple τ i := fun i =>
    weylQuotientHom_eq (mapsRootLines_weylElt i)
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← (coxeterSystem τ).subgroup_closure_range_simple,
      Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨_, hn i⟩
  have hker : ρ.ker = (torusGroup τ R).subgroupOf (monomialSubgroup τ R) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets g.2
      have hmaps : MapsRootLines (g : (Module.End R (RootModule τ R))ˣ) w := by
        rw [hgk]
        simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
      have hw : w = 1 := (weylQuotientHom_eq hmaps).symm.trans hg
      rw [hgk, hw, canonicalRep_one, mul_one]
      exact hk
    · exact fun hg => weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hg)
  set e : (monomialSubgroup τ R ⧸ (torusGroup τ R).subgroupOf (monomialSubgroup τ R)) ≃*
      WeylGroup τ :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hsurj)
  have he : ∀ g, e (QuotientGroup.mk g) = ρ g := fun g => rfl
  refine ⟨fun g hg => ?_, ⟨ρ, hsurj, mapsRootLines_weylQuotientHom, hd, hn, hker⟩,
    ⟨e.symm, fun i => (MulEquiv.symm_apply_eq e).2 (by rw [he, hn]), fun ψ hψ => ?_⟩⟩
  · obtain ⟨w, hw⟩ := exists_mapsRootLines_of_mem hg
    exact ⟨w, hw, fun w' hw' => hw'.unique hw⟩
  · have h1 : ψ.toMonoidHom = e.symm.toMonoidHom :=
      (coxeterSystem τ).ext_simple fun i => by
        change ψ (simple τ i) = e.symm (simple τ i)
        rw [hψ, MulEquiv.eq_symm_apply, he, hn]
    exact MulEquiv.ext fun w => congrArg (fun f => f w) h1

end CFSG.LieType.Chevalley
