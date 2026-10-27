module

public import CFSG.GroupTheory.ABGDGroups.LinearDecomposition
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pGammaL2PSLRange
  pGammaL2PGLRange mem_pGammaL2PSLRange_iff pgl2FieldAut HasDihedralSylowTwo)
open CFSG.Semidihedral.FixedFieldCentralizer (pglInclusion pgl_fixed_iff F0)

section Squares

variable {F : Type} [Field F] [Finite F]

theorem isSquare_of_isSquare_coe_fixedSubfield (hF2 : ringChar F ≠ 2) (A : Subgroup (F ≃+* F))
    (hA : Odd (Nat.card A)) {a : F0 F A} (ha : a ≠ 0) (hsq : IsSquare (a : F)) : IsSquare a := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (F0 F A) := Fintype.ofFinite _
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF2
  have h2₀ : ringChar (F0 F A) ≠ 2 := by
    intro h
    apply h2
    have h' : ((ringChar (F0 F A) : ℕ) : F0 F A) = 0 := ringChar.Nat.cast_ringChar
    rw [h] at h'
    have h'' := congrArg (F0 F A).subtype h'
    rwa [map_natCast, map_zero] at h''
  set q₀ := Fintype.card (F0 F A) with hq₀def
  set d := Nat.card A
  have hq : Fintype.card F = q₀ ^ d := by
    rw [← Nat.card_eq_fintype_card, hq₀def, ← Nat.card_eq_fintype_card]
    exact CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow F A
  have hq₀odd : Odd q₀ := Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two h2₀)
  have ha' : (a : F) ≠ 0 := fun h => ha (Subtype.ext h)
  rw [FiniteField.isSquare_iff hF2 ha'] at hsq
  rw [FiniteField.isSquare_iff h2₀ ha]
  set b := a ^ (q₀ / 2)
  have hb : b * b = 1 := by
    rw [← pow_add, show q₀ / 2 + q₀ / 2 = q₀ - 1 by obtain ⟨k, hk⟩ := hq₀odd; omega]
    exact FiniteField.pow_card_sub_one_eq_one a ha
  set S := ∑ i ∈ Finset.range d, q₀ ^ i
  have hq₀1 : 1 ≤ q₀ := by obtain ⟨k, hk⟩ := hq₀odd; omega
  have hS : S * (q₀ - 1) = q₀ ^ d - 1 := geom_sum_mul_of_one_le hq₀1 d
  have hSodd : Odd S := by
    apply (Finset.odd_sum_iff_odd_card_odd fun i => q₀ ^ i).mpr
    simpa only [hq₀odd.pow, Finset.filter_true, Finset.card_range] using hA
  have hqS : Fintype.card F / 2 = q₀ / 2 * S := by
    rw [hq]
    obtain ⟨k, hk⟩ := hq₀odd
    have hk' : q₀ - 1 = 2 * k := by omega
    rw [hk'] at hS
    have h1 : q₀ ^ d = 2 * (k * S) + 1 := by
      have hpos : 1 ≤ q₀ ^ d := Nat.one_le_pow _ _ hq₀1
      have : q₀ ^ d - 1 = 2 * (k * S) := by rw [← hS]; ring
      omega
    rw [h1, show q₀ / 2 = k by omega]
    omega
  rw [hqS, pow_mul, show (a : F) ^ (q₀ / 2) = (b : F) by simp [b]] at hsq
  rcases mul_self_eq_one_iff.mp hb with hb1 | hb1
  · exact hb1
  · exfalso
    rw [hb1] at hsq
    simp only [OneMemClass.coe_one, NegMemClass.coe_neg] at hsq
    rw [hSodd.neg_one_pow] at hsq
    apply h2
    linear_combination -hsq

theorem pglInclusion_mem_range_toPGL_iff (hF2 : ringChar F ≠ 2) (A : Subgroup (F ≃+* F))
    (hA : Odd (Nat.card A)) (g₀ : PGL2 (F0 F A)) :
    pglInclusion F A g₀ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      g₀ ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F0 F A)).range := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g₀
  rw [pglInclusion, Matrix.ProjGenLinGroup.map_mk,
    CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare,
    CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare,
    Matrix.GeneralLinearGroup.map_det, Units.coe_map]
  constructor
  · intro h
    exact isSquare_of_isSquare_coe_fixedSubfield hF2 A hA B.det.ne_zero h
  · rintro ⟨c, hc⟩
    exact ⟨(c : F), by simp [hc]⟩

end Squares

namespace IsLinearDecomposition

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

private theorem ringChar_ne_two (hF : IsOddPrimePower (Nat.card F)) : ringChar F ≠ 2 := by
  intro h
  obtain ⟨p, f, hp, hpodd, hf, hq⟩ := hF
  have : Fintype F := Fintype.ofFinite F
  have h2 : 2 ∣ Fintype.card F := by
    have := (prime_dvd_char_iff_dvd_card (R := F) (p := 2)).mp (by rw [h])
    exact this
  rw [← Nat.card_eq_fintype_card, hq] at h2
  have : Odd (p ^ f) := hpodd.pow
  exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h2)

private theorem map_eq_map_inr (hd : IsLinearDecomposition ι L E S) {E₀ : Subgroup H}
    (hE₀ : E₀ ≤ E) :
    E₀.map ι = ((E₀.map ι).comap (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F)).map
      SemidirectProduct.inr :=
  (Subgroup.map_comap_eq_self ((Subgroup.map_mono hE₀).trans hd.map_le_fieldRange)).symm

omit [Finite F] in
private theorem inr_conj_inl (σ : F ≃+* F) (g : PGL2 F) :
    (SemidirectProduct.inr σ : PGammaL2 F) * SemidirectProduct.inl g *
      (SemidirectProduct.inr σ)⁻¹ = SemidirectProduct.inl (pgl2FieldAut F σ g) := by
  rw [← map_inv, SemidirectProduct.inl_aut]

theorem centralizer_fieldSubgroup_mulEquiv (hd : IsLinearDecomposition ι L E S)
    {E₀ : Subgroup H} (hE₀ : E₀ ≤ E) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F = Nat.card F₀ ^ Nat.card E₀ ∧
      Nonempty (↥(linearCore ι ⊓ Subgroup.centralizer (E₀ : Set H)) ≃* PSL2 F₀) := by
  classical
  have hF := hd.isOddPrimePower_card
  have hF2 := ringChar_ne_two hF
  set A := (E₀.map ι).comap (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F) with hAdef
  have hEA := hd.map_eq_map_inr hE₀
  have hAcard : Nat.card A = Nat.card E₀ := by
    rw [← Subgroup.card_map_of_injective (f := (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F))
      SemidirectProduct.inr_injective, ← hEA, Subgroup.card_map_of_injective hd.injective]
  have hAodd : Odd (Nat.card A) := by
    rw [hAcard]
    exact hd.odd_card.of_dvd_nat (Subgroup.card_dvd_of_le hE₀)
  refine ⟨F0 F A, inferInstance, inferInstance, ?_, ⟨?_⟩⟩
  · rw [← hAcard]
    exact CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow F A
  set toPGL₀ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F0 F A)
  set J₀ := toPGL₀.range
  set f₀ : PGL2 (F0 F A) →* PGammaL2 F :=
    (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).comp (pglInclusion F A)
  have hf₀ : Function.Injective f₀ := SemidirectProduct.inl_injective.comp
    (CFSG.Semidihedral.FixedFieldCentralizer.pgl_map_injective _)
  have hmap : (linearCore ι ⊓ Subgroup.centralizer (E₀ : Set H)).map ι = J₀.map f₀ := by
    ext x
    constructor
    · rintro ⟨h, ⟨hL, hC⟩, rfl⟩
      obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff F _).mp (show ι h ∈ pGammaL2PSLRange F from hL)
      set g := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F) y
      have hfix : ∀ σ : A, pgl2FieldAut F σ g = g := by
        rintro ⟨σ, hσ⟩
        obtain ⟨e, he, hσe⟩ := hσ
        have hcomm := Subgroup.mem_centralizer_iff.mp hC e he
        apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
        rw [← inr_conj_inl, ← hσe, hy, ← map_inv, ← map_mul, ← map_mul, hcomm,
          mul_inv_cancel_right]
      obtain ⟨g₀, hg₀⟩ := (pgl_fixed_iff F A g).mp hfix
      have hg₀J : g₀ ∈ J₀ := (pglInclusion_mem_range_toPGL_iff hF2 A hAodd g₀).mp
        (hg₀ ▸ ⟨y, rfl⟩)
      exact ⟨g₀, hg₀J, by simp only [f₀, MonoidHom.comp_apply, hg₀, hy]⟩
    · rintro ⟨g₀, hg₀J, rfl⟩
      have hJ : pglInclusion F A g₀ ∈
          (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
        (pglInclusion_mem_range_toPGL_iff hF2 A hAodd g₀).mpr hg₀J
      obtain ⟨y, hy⟩ := hJ
      have hPSL : f₀ g₀ ∈ pGammaL2PSLRange F := ⟨y, by simp only [f₀, MonoidHom.comp_apply, hy]⟩
      obtain ⟨h, hh⟩ := hd.pGammaL2PSLRange_le_range hPSL
      refine ⟨h, ⟨show ι h ∈ pGammaL2PSLRange F by rw [hh]; exact hPSL,
        Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩, hh⟩
      have heA : ι e ∈ A.map SemidirectProduct.inr := hEA ▸ ⟨e, he, rfl⟩
      obtain ⟨σ, hσ, hσe⟩ := heA
      apply hd.injective
      rw [map_mul, map_mul, hh, ← hσe]
      exact inr_mul_inl_comm hσ ⟨g₀, rfl⟩
  exact ((Subgroup.equivMapOfInjective _ ι hd.injective).trans (MulEquiv.subgroupCongr hmap)).trans
    ((Subgroup.equivMapOfInjective J₀ f₀ hf₀).symm.trans
      (MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).symm)

end IsLinearDecomposition

end CFSG.ABGDGroups
