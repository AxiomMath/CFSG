module

public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.WeylRootTransport

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem height_permLattice_pos_iff
    (α : Fin t.tag.rank → ℤ) :
    0 < height (permLattice t.perm α) ↔ 0 < height α := by
  rw [height_permLattice]

theorem height_permLattice_neg_iff
    (α : Fin t.tag.rank → ℤ) :
    height (permLattice t.perm α) < 0 ↔ height α < 0 := by
  rw [height_permLattice]

theorem image_permLattice_posRoots :
    permLattice t.perm '' {α | IsRoot t.tag α ∧ 0 < height α} =
      {α | IsRoot t.tag α ∧ 0 < height α} := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hpos⟩, rfl⟩
    exact ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice]⟩
  · rintro ⟨hβ, hpos⟩
    exact ⟨permLattice t.perm.symm β, ⟨hβ.permLattice (cartan_perm_symm t.cartan_perm),
      by rwa [height_permLattice]⟩, permLattice_permLattice_symm _ _⟩

theorem image_permLattice_negRoots :
    permLattice t.perm '' {α | IsRoot t.tag α ∧ height α < 0} =
      {α | IsRoot t.tag α ∧ height α < 0} := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hneg⟩, rfl⟩
    exact ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice]⟩
  · rintro ⟨hβ, hneg⟩
    exact ⟨permLattice t.perm.symm β, ⟨hβ.permLattice (cartan_perm_symm t.cartan_perm),
      by rwa [height_permLattice]⟩, permLattice_permLattice_symm _ _⟩

theorem twistHom_canonicalRep
    (w : WeylGroup t.tag) :
    twistHom t K σ (canonicalRep (coxeterSystem t.tag) K w) =
      canonicalRep (coxeterSystem t.tag) K (weylTwist t w) :=
  congrArg Subtype.val (twistC_nrep t K σ w)

theorem canonicalRep_mem_twistedFixedGroup
    {w : WeylGroup t.tag} (hw : weylTwist t w = w) :
    canonicalRep (coxeterSystem t.tag) K w ∈ twistedFixedGroup t K σ :=
  (coe_mem_twistedFixedGroup_iff t K σ (nrep t.tag K w)).2 (by rw [twistC_nrep, hw])

theorem map_map_conj {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) (L : Subgroup G) :
    (L.map (MulAut.conj g).toMonoidHom).map f = (L.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

variable {σ} (hσ : Function.Surjective σ)
include hσ

theorem map_twistHom_rootSubgroup_single
    (i : Fin t.tag.rank) :
    (rootSubgroup t.tag K (Pi.single i 1)).map (twistHom t K σ) =
      rootSubgroup t.tag K (Pi.single (t.perm i) 1) := by
  rw [rootSubgroup, rootSubgroup, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨σ c, by simp [pinnedX_single, twistHom_xUnit]⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨c, rfl⟩ := hσ d
    exact ⟨c, by simp [pinnedX_single, twistHom_xUnit]⟩

theorem map_twistHom_rootSubgroup
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    (rootSubgroup t.tag K α).map (twistHom t K σ) =
      rootSubgroup t.tag K (permLattice t.perm α) := by
  obtain ⟨w, i, rfl⟩ := isRoot_iff_exists_smul_single.1 hα
  rw [← (canonical_weyl_root_transport t.tag K).2.1 w _ (isRoot_single _ i), map_map_conj,
    map_twistHom_rootSubgroup_single t K hσ, twistHom_canonicalRep,
    (canonical_weyl_root_transport t.tag K).2.1 _ _ (isRoot_single _ _), ← permLattice_single,
    weylTwist_smul_permLattice]

theorem map_twistHom_rootSpan
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α) :
    (rootSpan t.tag K S).map (twistHom t K σ) = rootSpan t.tag K (permLattice t.perm '' S) := by
  simp only [rootSpan, Subgroup.map_iSup, iSup_image]
  exact iSup_congr fun α => iSup_congr fun hα => map_twistHom_rootSubgroup t K hσ (hS α hα)

theorem map_twistHom_posUnipotent :
    (posUnipotent t.tag K).map (twistHom t K σ) = posUnipotent t.tag K := by
  rw [posUnipotent, map_twistHom_rootSpan t K hσ fun α hα => hα.1, image_permLattice_posRoots]

theorem map_twistHom_negUnipotent :
    (negUnipotent t.tag K).map (twistHom t K σ) = negUnipotent t.tag K := by
  rw [negUnipotent, map_twistHom_rootSpan t K hσ fun α hα => hα.1, image_permLattice_negRoots]

theorem map_twistHom_torusGroup :
    (torusGroup t.tag K).map (twistHom t K σ) = torusGroup t.tag K := by
  rw [torusGroup, MonoidHom.map_closure, ← Set.range_comp]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨i, u⟩, rfl⟩
    exact ⟨(t.perm i, Units.map σ.toMonoidHom u), (twistHom_torusElt t K σ i u).symm⟩
  · rintro ⟨⟨j, u⟩, rfl⟩
    obtain ⟨c, hc⟩ := hσ u
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact u.ne_zero hc.symm
    refine ⟨(t.perm.symm j, Units.mk0 c hc0), ?_⟩
    change twistHom t K σ (torusElt t.tag K (t.perm.symm j) (Units.mk0 c hc0)) = _
    rw [twistHom_torusElt, Equiv.apply_symm_apply]
    congr 1
    exact Units.ext (by simpa using hc)

theorem map_twistHom_monomialSubgroup :
    (monomialSubgroup t.tag K).map (twistHom t K σ) = monomialSubgroup t.tag K := by
  rw [monomialSubgroup, Subgroup.map_sup, map_twistHom_torusGroup t K hσ, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 2
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨t.perm i, (twistHom_weylElt_one t K σ i).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨t.perm.symm j, by
      change twistHom t K σ (weylElt t.tag K (t.perm.symm j) 1) = _
      rw [twistHom_weylElt_one, Equiv.apply_symm_apply]⟩

theorem map_twistHom_borelGroup :
    (borelGroup t.tag K).map (twistHom t K σ) = borelGroup t.tag K := by
  rw [borelGroup, Subgroup.map_sup, map_twistHom_torusGroup t K hσ,
    map_twistHom_posUnipotent t K hσ]

omit hσ

theorem diagram_field_Bruhat_equivariance
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    (∀ w : WeylGroup t.tag,
      (coxeterSystem t.tag).length (weylTwist t w) = (coxeterSystem t.tag).length w) ∧
    (∀ α : Fin t.tag.rank → ℤ, (0 < height (permLattice t.perm α) ↔ 0 < height α) ∧
      (height (permLattice t.perm α) < 0 ↔ height α < 0)) ∧
    (∀ α, IsRoot t.tag α → (rootSubgroup t.tag K α).map (twistHom t K σ.toRingHom) =
      rootSubgroup t.tag K (permLattice t.perm α)) ∧
    (torusGroup t.tag K).map (twistHom t K σ.toRingHom) = torusGroup t.tag K ∧
    (monomialSubgroup t.tag K).map (twistHom t K σ.toRingHom) = monomialSubgroup t.tag K ∧
    (borelGroup t.tag K).map (twistHom t K σ.toRingHom) = borelGroup t.tag K ∧
    (posUnipotent t.tag K).map (twistHom t K σ.toRingHom) = posUnipotent t.tag K ∧
    (negUnipotent t.tag K).map (twistHom t K σ.toRingHom) = negUnipotent t.tag K ∧
    (∀ w : WeylGroup t.tag, twistHom t K σ.toRingHom (canonicalRep (coxeterSystem t.tag) K w) =
      canonicalRep (coxeterSystem t.tag) K (weylTwist t w)) ∧
    ∀ w : WeylGroup t.tag, weylTwist t w = w →
      canonicalRep (coxeterSystem t.tag) K w ∈ twistedFixedGroup t K σ.toRingHom :=
  ⟨length_weylTwist t,
    fun α => ⟨height_permLattice_pos_iff t α, height_permLattice_neg_iff t α⟩,
    fun _ hα => map_twistHom_rootSubgroup t K σ.surjective hα,
    map_twistHom_torusGroup t K σ.surjective,
    map_twistHom_monomialSubgroup t K σ.surjective,
    map_twistHom_borelGroup t K σ.surjective,
    map_twistHom_posUnipotent t K σ.surjective,
    map_twistHom_negUnipotent t K σ.surjective,
    twistHom_canonicalRep t K σ.toRingHom,
    fun _ hw => canonicalRep_mem_twistedFixedGroup t K σ.toRingHom hw⟩

end CFSG.LieType.Chevalley
