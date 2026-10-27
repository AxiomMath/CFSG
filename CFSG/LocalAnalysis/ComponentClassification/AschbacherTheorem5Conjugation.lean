module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages

public section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

@[expose] noncomputable def onD {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) : MulAut D :=
  (D.equivMapOfInjective (MulAut.conj h.val).toMonoidHom (MulAut.conj h.val).injective).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp h.property))

theorem onD_apply {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) (d : D) :
    (onD D h d).val = h.val * d.val * h.val⁻¹ := rfl

theorem onD_equivariant {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) :
    D.subtype.comp (onD D h).toMonoidHom =
      (MulAut.conj h.val).toMonoidHom.comp D.subtype := by
  ext d
  exact onD_apply D h d

@[expose] noncomputable def onQuotient {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) : MulAut (D ⧸ aschbacherThm5OddCore D) :=
  QuotientGroup.congr (aschbacherThm5OddCore D) (aschbacherThm5OddCore D)
    (onD D h) (Subgroup.characteristic_iff_map_eq.mp (oddCore_characteristic D) (onD D h))

theorem onQuotient_mk {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) (d : D) :
    onQuotient D h (QuotientGroup.mk' (aschbacherThm5OddCore D) d) =
      QuotientGroup.mk' (aschbacherThm5OddCore D) (onD D h d) :=
  QuotientGroup.congr_mk' _ _ _ _ d

theorem onQuotient_symm_mk {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) (d : D) :
    (onQuotient D h).symm (QuotientGroup.mk' (aschbacherThm5OddCore D) d) =
      QuotientGroup.mk' (aschbacherThm5OddCore D) ((onD D h).symm d) := by
  have heq := onQuotient_mk D h ((onD D h).symm d)
  rw [(onD D h).apply_symm_apply] at heq
  exact (congrArg (onQuotient D h).symm heq).symm.trans
    ((onQuotient D h).symm_apply_apply _)

theorem core_conjugate_eq {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G)) :
    (aschbacherThm5Core D).map (MulAut.conj h.val).toMonoidHom = aschbacherThm5Core D := by
  have hcore := Subgroup.characteristic_iff_map_eq.mp (oddCore_characteristic D) (onD D h)
  change ((aschbacherThm5OddCore D).map D.subtype).map _ = _
  rw [Subgroup.map_map, ← onD_equivariant, ← Subgroup.map_map, hcore]
  rfl

theorem preimage_conjugate {G : Type*} [Group G] (D : Subgroup G)
    (h : Subgroup.normalizer (D : Set G))
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    (aschbacherThm5Preimage D Abar).map (MulAut.conj h.val).toMonoidHom =
      aschbacherThm5Preimage D (Abar.map (onQuotient D h).toMonoidHom) := by
  have hpreimage : (Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map
      (onD D h).toMonoidHom = (Abar.map (onQuotient D h).toMonoidHom).comap
        (QuotientGroup.mk' (aschbacherThm5OddCore D)) := by
    ext d
    rw [Subgroup.mem_map_equiv]
    change QuotientGroup.mk' (aschbacherThm5OddCore D) ((onD D h).symm d) ∈ Abar ↔
      QuotientGroup.mk' (aschbacherThm5OddCore D) d ∈ Abar.map (onQuotient D h).toMonoidHom
    rw [Subgroup.mem_map_equiv, onQuotient_symm_mk]
  change ((Abar.comap (QuotientGroup.mk' (aschbacherThm5OddCore D))).map D.subtype).map _ = _
  rw [Subgroup.map_map, ← onD_equivariant, ← Subgroup.map_map, hpreimage]
  rfl

theorem permutation_of_canonical_hypothesis {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hdistinct : Function.Injective Abar)
    (hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j)) (h : Subgroup.normalizer (D : Set G)) :
    ∃ permutation : Equiv.Perm (Fin r), ∀ i,
      (Abar i).map (onQuotient D h).toMonoidHom = Abar (permutation i) := by
  classical
  let image := fun i => Classical.choose (hperm h.val h.property i)
  have himage : ∀ i, (Abar i).map (onQuotient D h).toMonoidHom = Abar (image i) := by
    intro i
    apply preimage_injective D
    rw [← preimage_conjugate]
    exact Classical.choose_spec (hperm h.val h.property i)
  have hinjective : Function.Injective image := by
    intro i j hij
    apply hdistinct
    exact Subgroup.map_injective (f := (onQuotient D h).toMonoidHom)
      (onQuotient D h).injective
      ((himage i).trans ((congrArg Abar hij).trans (himage j).symm))
  exact ⟨Equiv.ofBijective image ⟨hinjective, Finite.surjective_of_injective hinjective⟩, himage⟩

end CFSG.ComponentClassification.AschbacherTheorem5
