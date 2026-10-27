module

public import CFSG.LocalAnalysis.ComponentInitial.UnitarySixFieldTwoCover

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace UnitarySixFieldTwo

open Matrix CFSG.ClassicalGroups.UnitaryFlag MatrixExtension

variable {F : Type} [Field F]

@[expose] def sixScalars (h : UnitaryFieldData 2 1 F) : Subgroup (hypSU h 3 0) where
  carrier := {g | ∃ c : Fˣ, (g : GL (HypIndex 3 0) F) = GeneralLinearGroup.scalar _ c}
  mul_mem' := by
    rintro g g' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c * c', by rw [Subgroup.coe_mul, hc, hc', map_mul]⟩
  one_mem' := ⟨1, by rw [map_one]; rfl⟩
  inv_mem' := by
    rintro g ⟨c, hc⟩
    exact ⟨c⁻¹, by rw [Subgroup.coe_inv, hc, map_inv]⟩

theorem sixScalars_eq (h : UnitaryFieldData 2 1 F) : sixScalars h = hypScalars h 3 0 := by
  ext g
  constructor
  · rintro ⟨c, hc⟩
    have h3 : (c : F) ^ 3 = 1 := four_pow_three (card_eq_four h) c.ne_zero
    refine ⟨c, ?_, ?_, hc⟩
    · rw [UnitaryFieldData.norm, UnitaryFourCover.bar_apply_two, ← pow_succ']
      exact h3
    · refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one, show 2 * 3 + 0 = 3 * 2 from rfl, pow_mul, h3,
        one_pow]
  · rintro ⟨c, -, -, hc⟩
    exact ⟨c, hc⟩

instance sixScalars_normal (h : UnitaryFieldData 2 1 F) : (sixScalars h).Normal :=
  sixScalars_eq h ▸ normOneScalars_normal h _ _

@[expose] def hermRadical (h : UnitaryFieldData 2 1 F) : Subgroup (hypSU h 3 0) where
  carrier := {g | ∃ B : Matrix (Fin 3) (Fin 3) F, (B.map h.bar)ᵀ = B ∧
    ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) = nMat B}
  mul_mem' := by
    rintro g g' ⟨B, hB, hg⟩ ⟨B', hB', hg'⟩
    refine ⟨B + B', ?_, ?_⟩
    · rw [Matrix.map_add _ (map_add h.bar), transpose_add, hB, hB']
    · change ((g : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) *
        ((g' : GL (HypIndex 3 0) F) : Matrix (HypIndex 3 0) (HypIndex 3 0) F) = _
      rw [hg, hg', nMat_mul]
  one_mem' := ⟨0, by rw [Matrix.map_zero _ (map_zero h.bar), transpose_zero],
    by rw [nMat_zero]; rfl⟩
  inv_mem' := by
    rintro g ⟨B, hB, hg⟩
    refine ⟨-B, by rw [Matrix.map_neg _ (map_neg h.bar), transpose_neg, hB], ?_⟩
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hg, nMat_mul, add_neg_cancel, nMat_zero])

end UnitarySixFieldTwo

open UnitarySixFieldTwo CFSG.ClassicalGroups.UnitaryFlag MatrixExtension

theorem unitary_six_field_two_full_cover_Hermitian_radical_preimage_elementary {F : Type}
    [Field F] (h : UnitaryFieldData 2 1 F) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* hypSU h 3 0 ⧸ sixScalars h) (hη : Function.Surjective η)
    (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker) :
    CFSG.IsElementaryAbelian 2 η.ker ∧
      CFSG.IsElementaryAbelian 2
        (((hermRadical h).map (QuotientGroup.mk' (sixScalars h))).comap η) ∧
      (∀ x ∈ ((hermRadical h).map (QuotientGroup.mk' (sixScalars h))).comap η, x ^ 2 = 1) ∧
      η.ker ≤ ((hermRadical h).map (QuotientGroup.mk' (sixScalars h))).comap η := by
  have := h.charP
  set e : hypSU h 3 0 ⧸ sixScalars h ≃* hypPSU h 3 0 :=
    QuotientGroup.quotientMulEquivOfEq (sixScalars_eq h) with he
  set θ : E →* hypPSU h 3 0 := e.toMonoidHom.comp η with hθdef
  have hker : θ.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hθ : Function.Surjective θ := e.surjective.comp hη
  have hθC : θ.ker ≤ Subgroup.center E := hker ▸ hC
  have hsqC : ∀ c ∈ η.ker, c ^ 2 = 1 := by
    have := kernel_sq_eq_one_of_isPGroup θ hθ hθC (hker ▸ h2)
    rwa [hker] at this
  set M := ((hermRadical h).map (QuotientGroup.mk' (sixScalars h))).comap η with hM
  have hlift : ∀ x ∈ M, ∃ B : Matrix (Fin 3) (Fin 3) F, IsLift θ (nMat B) x := by
    intro x hx
    obtain ⟨g, ⟨B, -, hgB⟩, hgx⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hx)
    refine ⟨B, g, hgB, ?_⟩
    change e (η x) = hypProj h 3 0 g
    rw [← hgx, QuotientGroup.mk'_apply, he, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hMsq : ∀ x ∈ M, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨B, hxB⟩ := hlift x hx
    obtain ⟨c, hc, hxc⟩ := exists_sq_eq_of_isLift_nMat hθ hθC hxB
    rw [hxc]
    exact hsqC c (by rw [← hker]; exact hc)
  refine ⟨{ is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hC v.2) u)⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
              Subtype.ext (by simpa using hsqC x x.2) },
    { is_comm := ⟨fun u v => Subtype.ext ?_⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hMsq x x.2) }, hMsq, fun c hc => ?_⟩
  · obtain ⟨B, hu⟩ := hlift u u.2
    obtain ⟨B', hv⟩ := hlift v v.2
    exact (commute_of_isLift_nMat hθ hθC hu hv).eq
  · rw [hM, Subgroup.mem_comap, MonoidHom.mem_ker.mp hc]
    exact Subgroup.one_mem _

end CFSG.LocalAnalysis.ComponentInitial
