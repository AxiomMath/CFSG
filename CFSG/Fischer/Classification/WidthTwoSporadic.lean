module

public import CFSG.Fischer.Classification.WidthTwoPSU
public import CFSG.Fischer.OpenTranslation

public noncomputable section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Open CFSG.OddTranspositions

variable {X : Type} [Group X] {E : Set X}

theorem width_two_false_of_localImages {e : X} (hP : Pair X E)
    (h : ¬ WidthLe (LocalImages E e) 2) : ¬ WidthLe E 2 := by
  classical
  intro hW
  rw [widthLe_two_iff] at h
  push Not at h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hcxy, hcxz, hcyz⟩ := h
  have hx' : x ∈ Set.range (starImage E e) := by
    rw [range_starImage]
    exact hx
  obtain ⟨fx, rfl⟩ := hx'
  have hy' : y ∈ Set.range (starImage E e) := by
    rw [range_starImage]
    exact hy
  obtain ⟨fy, rfl⟩ := hy'
  have hz' : z ∈ Set.range (starImage E e) := by
    rw [range_starImage]
    exact hz
  obtain ⟨fz, rfl⟩ := hz'
  have hne_fx_fy : (fx : X) ≠ fy := by
    intro hEq
    exact hxy (congrArg (starImage E e) (Subtype.ext hEq))
  have hne_fx_fz : (fx : X) ≠ fz := by
    intro hEq
    exact hxz (congrArg (starImage E e) (Subtype.ext hEq))
  have hne_fy_fz : (fy : X) ≠ fz := by
    intro hEq
    exact hyz (congrArg (starImage E e) (Subtype.ext hEq))
  have hc_fx_fy : Commute (fx : X) fy :=
    (Pair.starImage_commute_iff hP fx fy).1 hcxy
  have hc_fx_fz : Commute (fx : X) fz :=
    (Pair.starImage_commute_iff hP fx fz).1 hcxz
  have hc_fy_fz : Commute (fy : X) fz :=
    (Pair.starImage_commute_iff hP fy fz).1 hcyz
  rw [widthLe_two_iff] at hW
  exact hW (fx : X) fx.2.1 (fy : X) fy.2.1 (fz : X) fz.2.1
    hne_fx_fy hne_fx_fz hne_fy_fz ⟨hc_fx_fy, hc_fx_fz, hc_fy_fz⟩

theorem width_two_false_of_F22 (h : F22 X E) : ¬ WidthLe E 2 := by
  classical
  obtain ⟨hP, e, -, H, hH, iso, himg⟩ := h
  obtain ⟨iso1, himg1⟩ := exists_psu_equiv hH
  let ψ : LocalQuotient E e ≃* PSU (1 : Matrix (Fin 6) (Fin 6) K) := iso.trans iso1.symm
  have hψ : ψ '' LocalImages E e = Transvections (1 : Matrix (Fin 6) (Fin 6) K) := by
    show (iso.trans iso1.symm) '' LocalImages E e = Transvections 1
    rw [MulEquiv.coe_trans, Set.image_comp, himg, ← himg1]
    exact image_symm_image iso1 (Transvections (1 : Matrix (Fin 6) (Fin 6) K))
  let φ : LocalQuotient E e ≃* fischerEUPSU := ψ.trans psuOpenEquiv
  have hφ : φ '' LocalImages E e = fischerEUTransvections := by
    show (ψ.trans psuOpenEquiv) '' LocalImages E e = fischerEUTransvections
    rw [MulEquiv.coe_trans, Set.image_comp, hψ]
    exact psuOpenEquiv_image
  have hmodel : fischerCentralQuotientModel (LocalImages E e) (Unitary.SUm 6) (Unitary.TU 6) := by
    refine ⟨φ, ?_⟩
    intro g
    have hmem : g ∈ LocalImages E e ↔ φ g ∈ fischerEUTransvections := by
      constructor
      · intro hg
        rw [← hφ]
        exact ⟨g, hg, rfl⟩
      · intro hg
        rw [← hφ] at hg
        obtain ⟨d, hd, hdg⟩ := hg
        rwa [φ.injective hdg] at hd
    rw [hmem]
    constructor
    · rintro ⟨A, v, hv0, hvv, hact, hq⟩
      refine ⟨A, ?_, hq⟩
      exact ⟨v, ⟨hv0, hvv⟩, hact⟩
    · rintro ⟨A, hA, hq⟩
      obtain ⟨v, ⟨hv0, hvv⟩, hact⟩ := hA
      exact ⟨A, v, hv0, hvv, hact, hq⟩
  exact width_two_false_of_localImages hP
    (CFSG.Fischer.Classification.Unitary.width_two_false_of_psu_case (m := 6) (by norm_num) hmodel)

theorem width_two_false_of_F23 (h : F23 X E) : ¬ WidthLe E 2 := by
  obtain ⟨hP, e, -, hF22⟩ := h
  exact width_two_false_of_localImages hP (width_two_false_of_F22 hF22)

theorem width_two_false_of_F24 (h : F24 X E) : ¬ WidthLe E 2 := by
  obtain ⟨hP, e, -, hF23⟩ := h
  exact width_two_false_of_localImages hP (width_two_false_of_F23 hF23)

theorem width_two_false_of_hasType {k : Fin 3} (h : HasType k X E) : ¬ WidthLe E 2 := by
  fin_cases k
  · exact width_two_false_of_F22 h
  · exact width_two_false_of_F23 h
  · exact width_two_false_of_F24 h

end CFSG.Fischer.Classification
