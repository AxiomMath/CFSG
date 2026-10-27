module

public import CFSG.LieType.Chevalley.BorelStructure
public import CFSG.LieType.Chevalley.WeylRootTransport
public import CFSG.LieType.Chevalley.LongestElement

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley
open scoped Pointwise

variable {τ : Tag}

theorem negUnipotent_le_comap_conj_torusElt
    {R : Type*} [CommRing R] (i : Fin τ.rank)
    (t : Rˣ) :
    negUnipotent τ R ≤ (negUnipotent τ R).comap (MulAut.conj (torusElt τ R i t)).toMonoidHom := by
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [root_torus_conjugation i hα.1 t c]
  exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨_, rfl⟩))

theorem torusElt_mem_normalizer_negUnipotent
    {R : Type*} [CommRing R] (i : Fin τ.rank)
    (t : Rˣ) : torusElt τ R i t ∈ Subgroup.normalizer (SetLike.coe (negUnipotent τ R)) := by
  rw [Subgroup.mem_normalizer_iff]
  refine fun h => ⟨fun hh => negUnipotent_le_comap_conj_torusElt i t hh, fun hh => ?_⟩
  have h1 := negUnipotent_le_comap_conj_torusElt i t⁻¹ hh
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  have hinv : torusElt τ R i t⁻¹ = (torusElt τ R i t)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← torusElt_mul, inv_mul_cancel, torusElt_one]
  rw [hinv] at h1
  convert h1 using 1
  group

theorem torusGroup_le_normalizer_negUnipotent
    {R : Type*} [CommRing R] :
    torusGroup τ R ≤ Subgroup.normalizer (SetLike.coe (negUnipotent τ R)) :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_normalizer_negUnipotent i t)

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  refine SetLike.coe_injective ?_
  rw [Subgroup.coe_map]
  exact Subgroup.mem_normalizer_iff_conj_image_eq.1 hg

theorem eq_one_of_isUpperTriangular_of_isLowerUnitriangular
    {R : Type*} [CommRing R]
    {A : Module.End R (RootModule τ R)} (hu : IsUpperTriangular τ R A)
    (hl : IsLowerUnitriangular A) : A = 1 := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  by_cases hab : a = b
  · subst hab
    rw [hl.1 a, Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, ite_eq_right_iff.2 fun h => absurd h (Ne.symm hab)]
    rcases Label.precedes_or_precedes hab with h | h
    · exact hl.2 a b h
    · exact hu a b h

theorem opposite_Borel_intersection
    (τ : Tag) (R : Type) [CommRing R] (w₀ : WeylGroup τ)
    (hw₀ : ∀ w, (coxeterSystem τ).length w ≤ (coxeterSystem τ).length w₀) :
    (SetLike.coe (torusGroup τ R) * SetLike.coe (negUnipotent τ R) :
        Set (Module.End R (RootModule τ R))ˣ) =
      SetLike.coe (torusGroup τ R ⊔ negUnipotent τ R) ∧
    (borelGroup τ R).map
        (MulAut.conj (canonicalRep (coxeterSystem τ) R w₀)).toMonoidHom =
      torusGroup τ R ⊔ negUnipotent τ R ∧
    borelGroup τ R ⊓ (torusGroup τ R ⊔ negUnipotent τ R) = torusGroup τ R ∧
    borelGroup τ R ⊓ negUnipotent τ R = ⊥ := by
  have hN := torusGroup_le_normalizer_negUnipotent (τ := τ) (R := R)
  have hprod : (SetLike.coe (torusGroup τ R) * SetLike.coe (negUnipotent τ R) :
      Set (Module.End R (RootModule τ R))ˣ) = SetLike.coe (torusGroup τ R ⊔ negUnipotent τ R) :=
    (Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN).symm
  obtain ⟨w₁, -, huniq, himage, -⟩ := weyl_longest_element τ
  have hw : w₀ = w₁ := huniq w₀ hw₀
  subst hw
  obtain ⟨hS, -, hnorm⟩ := canonical_weyl_root_transport τ R
  have hU : (posUnipotent τ R).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) R w₀)).toMonoidHom = negUnipotent τ R := by
    rw [posUnipotent, hS w₀ _ fun α hα => hα.1, himage]
    rfl
  have hmap : (borelGroup τ R).map
      (MulAut.conj (canonicalRep (coxeterSystem τ) R w₀)).toMonoidHom =
      torusGroup τ R ⊔ negUnipotent τ R := by
    rw [borelGroup, Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hnorm w₀), hU]
  have hupper := ((triangular_borel_structure.{0, 0} τ R).2.2.2.2.2.2.2.2.2).1
  have hinf : borelGroup τ R ⊓ negUnipotent τ R = ⊥ := by
    refine eq_bot_iff.2 fun g hg => Subgroup.mem_bot.2 (Units.ext ?_)
    obtain ⟨hgB, hgU⟩ := Subgroup.mem_inf.1 hg
    exact eq_one_of_isUpperTriangular_of_isLowerUnitriangular (hupper g hgB)
      (isLowerUnitriangular_of_mem (negUnipotent_le_posFiltration τ R hgU))
  refine ⟨hprod, hmap, le_antisymm (fun x hx => ?_) (le_inf le_sup_left le_sup_left), hinf⟩
  obtain ⟨hxB, hxB'⟩ := Subgroup.mem_inf.1 hx
  have hx' : x ∈ (SetLike.coe (torusGroup τ R) * SetLike.coe (negUnipotent τ R) :
      Set (Module.End R (RootModule τ R))ˣ) := by
    rw [hprod]
    exact hxB'
  obtain ⟨h, hh, v, hv, rfl⟩ := hx'
  have hvB : v ∈ borelGroup τ R := by
    have := mul_mem (inv_mem ((le_sup_left : torusGroup τ R ≤ borelGroup τ R) hh)) hxB
    rwa [inv_mul_cancel_left] at this
  have hv1 : v ∈ borelGroup τ R ⊓ negUnipotent τ R := Subgroup.mem_inf.2 ⟨hvB, hv⟩
  rw [hinf, Subgroup.mem_bot] at hv1
  show h * v ∈ torusGroup τ R
  rw [hv1, mul_one]
  exact hh

end CFSG.LieType.Chevalley
