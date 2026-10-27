module

public import CFSG.GH74.GLS.Stage4.T2F1LocFA
public import CFSG.GH74.GLS.Stage4.T2Coord
public import CFSG.GH74.GLS.Stage4.RestX2Q1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.GH74.GLS.Stage4.T2SL2B
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2NonsplitTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2SplitTorus

public section

namespace CFSG.GH74.GLS.Stage4.Rest.F1Loc

open CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest Subgroup

section Generic

variable {G : Type} [Group G]

theorem conj_mem_sup {X X' : Subgroup G} {f : G} (hfX : ∀ x ∈ X, f * x * f⁻¹ ∈ X)
    (hfX' : ∀ x ∈ X', f * x * f⁻¹ ∈ X') : ∀ x ∈ X ⊔ X', f * x * f⁻¹ ∈ X ⊔ X' := by
  have : X ⊔ X' ≤ (X ⊔ X').comap (MulAut.conj f).toMonoidHom :=
    sup_le (fun x hx => Subgroup.mem_sup_left (hfX x hx))
      (fun x hx => Subgroup.mem_sup_right (hfX' x hx))
  intro x hx
  exact this hx

theorem exists_fieldAut_of_coord {F : Type} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (φ : SL2 F →* G) (hφ : Function.Injective φ)
    {X X' H : Subgroup G} {f : G}
    (hX : X = (uSub F).map φ)
    (hHK : H ⊓ (X ⊔ X') = (tSub F).map φ)
    (hfX : ∀ x ∈ X, f * x * f⁻¹ ∈ X) (hfX' : ∀ x ∈ X', f * x * f⁻¹ ∈ X')
    (hfH : ∀ x ∈ H, f * x * f⁻¹ ∈ H) (hfw : f * φ (sl2W F) = φ (sl2W F) * f) :
    ∃ σ : F ≃+* F, ∀ M : SL2 F,
      f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M) := by
  have hfK : ∀ x ∈ X ⊔ X', f * x * f⁻¹ ∈ X ⊔ X' := conj_mem_sup hfX hfX'
  refine exists_fieldAut h2 φ hφ f ?_ ?_ hfw
  · intro c
    have hmem : φ (sl2U c) ∈ X := by
      rw [hX]; exact ⟨sl2U c, sl2U_mem_uSub c, rfl⟩
    have := hfX _ hmem
    rw [hX] at this
    obtain ⟨x, hx, hxe⟩ := this
    obtain ⟨c', rfl⟩ := mem_uSub.1 hx
    exact ⟨c', hxe.symm⟩
  · intro s
    have hmem : φ (sl2D s) ∈ H ⊓ (X ⊔ X') := by
      rw [hHK]; exact ⟨sl2D s, sl2D_mem_tSub s, rfl⟩
    have h1 : f * φ (sl2D s) * f⁻¹ ∈ H ⊓ (X ⊔ X') := ⟨hfH _ hmem.1, hfK _ hmem.2⟩
    rw [hHK] at h1
    obtain ⟨x, hx, hxe⟩ := h1
    obtain ⟨s', rfl⟩ := mem_tSub.1 hx
    exact ⟨s', hxe.symm⟩

theorem map_sl2D {F F' : Type} [Field F] [Field F'] (σ : F →+* F') (s : Fˣ) :
    Matrix.SpecialLinearGroup.map σ (sl2D s) = sl2D (Units.map (σ : F →* F') s) := by
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

variable {F : Type} [Field F] (φ : SL2 F →* G) (f : G) (σ : F ≃+* F)

theorem centralizes_of_eq_one
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (h1 : σ = 1) (M : SL2 F) : f * φ M * f⁻¹ = φ M := by
  rw [hσ, h1]
  congr 1

theorem eq_one_of_centralizes_torus (hφ : Function.Injective φ)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M))
    (hc : ∀ s : Fˣ, f * φ (sl2D s) * f⁻¹ = φ (sl2D s)) : σ = 1 := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · have h := hφ ((hσ (sl2D (Units.mk0 x hx))).symm.trans (hc (Units.mk0 x hx)))
    have := congrArg (fun A : SL2 F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simpa [map_sl2D, Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem range_comp_slFixIncl (hφ : Function.Injective φ)
    (hσ : ∀ M : SL2 F, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F →+* F) M)) :
    (φ.comp (slFixIncl σ)).range = φ.range ⊓ Subgroup.centralizer ({f} : Set G) := by
  ext x
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨⟨slFixIncl σ A, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (centralizes_iff φ hφ f σ hσ (slFixIncl σ A)).2
      ((mem_range_slFixIncl σ _).1 ⟨A, rfl⟩)
    show φ (slFixIncl σ A) * f = f * φ (slFixIncl σ A)
    calc φ (slFixIncl σ A) * f = (f * φ (slFixIncl σ A) * f⁻¹) * f := by rw [h]
      _ = f * φ (slFixIncl σ A) := by group
  · rintro ⟨⟨M, rfl⟩, hc⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : f * φ M * f⁻¹ = φ M := by
      calc f * φ M * f⁻¹ = (φ M * f) * f⁻¹ := by rw [← hc]
        _ = φ M := by group
    have := (centralizes_iff φ hφ f σ hσ M).1 hc'
    obtain ⟨A, rfl⟩ := (mem_range_slFixIncl σ M).2 this
    exact ⟨A, rfl⟩

end Generic

section Recoord

variable {G : Type} [Group G] {F F' : Type} [Field F] [Field F']

def recoordHom (ι : F' ≃+* F) (φ : SL2 F →* G) : SL2 F' →* G :=
  φ.comp (Matrix.SpecialLinearGroup.map (ι : F' →+* F))

theorem map_surj_aux (ι : F' ≃+* F) :
    Function.Surjective (Matrix.SpecialLinearGroup.map (n := Fin 2) (ι : F' →+* F)) := by
  intro M
  refine ⟨Matrix.SpecialLinearGroup.map (ι.symm : F →+* F') M, ?_⟩
  apply Subtype.ext
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem map_inj_aux (ι : F' ≃+* F) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) (ι : F' →+* F)) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun X : SL2 F => (X : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa [Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem recoordHom_injective (ι : F' ≃+* F) {φ : SL2 F →* G} (hφ : Function.Injective φ) :
    Function.Injective (recoordHom ι φ) := hφ.comp (map_inj_aux ι)

theorem recoordHom_range (ι : F' ≃+* F) (φ : SL2 F →* G) :
    (recoordHom ι φ).range = φ.range := by
  unfold recoordHom
  rw [MonoidHom.range_comp, (MonoidHom.range_eq_top.2 (map_surj_aux ι)), Subgroup.map_top]

theorem recoordHom_uSub (ι : F' ≃+* F) (φ : SL2 F →* G) :
    (uSub F').map (recoordHom ι φ) = (uSub F).map φ := by
  unfold recoordHom
  rw [← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_uSub.1 hy
    rw [map_sl2U]
    exact sl2U_mem_uSub _
  · intro hx
    obtain ⟨c, rfl⟩ := mem_uSub.1 hx
    exact ⟨sl2U (ι.symm c), sl2U_mem_uSub _, by simp [map_sl2U]⟩

theorem recoordHom_lSub (ι : F' ≃+* F) (φ : SL2 F →* G) :
    (lSub F').map (recoordHom ι φ) = (lSub F).map φ := by
  unfold recoordHom
  rw [← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_lSub.1 hy
    rw [map_sl2L]
    exact sl2L_mem_lSub _
  · intro hx
    obtain ⟨c, rfl⟩ := mem_lSub.1 hx
    exact ⟨sl2L (ι.symm c), sl2L_mem_lSub _, by simp [map_sl2L]⟩

theorem recoordHom_tSub (ι : F' ≃+* F) (φ : SL2 F →* G) :
    (tSub F').map (recoordHom ι φ) = (tSub F).map φ := by
  unfold recoordHom
  rw [← Subgroup.map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := mem_tSub.1 hy
    rw [map_sl2D]
    exact sl2D_mem_tSub _
  · intro hx
    obtain ⟨s, rfl⟩ := mem_tSub.1 hx
    refine ⟨sl2D (Units.map (ι.symm : F →* F') s), sl2D_mem_tSub _, ?_⟩
    rw [map_sl2D]
    congr 1
    ext
    simp

theorem recoordHom_w (ι : F' ≃+* F) (φ : SL2 F →* G) :
    recoordHom ι φ (sl2W F') = φ (sl2W F) := by
  unfold recoordHom
  show φ (Matrix.SpecialLinearGroup.map (ι : F' →+* F) (sl2W F')) = _
  congr 1
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem recoordHom_negOne (ι : F' ≃+* F) (φ : SL2 F →* G) :
    recoordHom ι φ (negOne F') = φ (negOne F) := by
  unfold recoordHom
  show φ (Matrix.SpecialLinearGroup.map (ι : F' →+* F) (negOne F')) = _
  congr 1
  apply sl2_ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.map_apply_coe]

end Recoord

section CoordN

variable {G : Type} [Group G]

theorem exists_coord_over {N : T2N1 G} (hC : Ch6Coord N) {F₁ : Type} [Field F₁] [Finite F₁]
    (hF₁ : Nat.card F₁ = N.q₁) :
    ∃ φ : SL2 F₁ →* G, Function.Injective φ ∧ φ.range = N.K₁ ∧ φ (negOne F₁) = N.z ∧
      N.X₁ = (uSub F₁).map φ ∧ N.X₁' = (lSub F₁).map φ ∧ N.w₁ = φ (sl2W F₁) ∧
      N.H ⊓ N.K₁ = (tSub F₁).map φ := by
  obtain ⟨F, iF, fF, φ, hcard, hinj, hrange, hz, hX, hX', hw, hHK⟩ := hC.coord₁
  have : Fintype F₁ := Fintype.ofFinite F₁
  have : Fintype F := Fintype.ofFinite F
  obtain ι : F₁ ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF₁, hcard])
  refine ⟨recoordHom ι φ, recoordHom_injective ι hinj, by rw [recoordHom_range, hrange],
    by rw [recoordHom_negOne, hz], by rw [recoordHom_uSub, hX], by rw [recoordHom_lSub, hX'],
    by rw [recoordHom_w, hw], by rw [recoordHom_tSub, hHK]⟩

theorem coord_fieldAut {N : T2N3 G} {u : G} (hSec : Ch6Sec5 N u)
    (hC : Ch6Coord N.toT2N2.toT2N1) {F₁ : Type} [Field F₁] [Finite F₁] (hF₁ : Nat.card F₁ = N.q₁)
    {f : G} (hf : f ∈ N.F) (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∃ (φ : SL2 F₁ →* G) (σ : F₁ ≃+* F₁),
      Function.Injective φ ∧ φ.range = N.K₁ ∧ φ (negOne F₁) = N.z ∧
      N.X₁ = (uSub F₁).map φ ∧ N.X₁' = (lSub F₁).map φ ∧ N.w₁ = φ (sl2W F₁) ∧
      N.H ⊓ N.K₁ = (tSub F₁).map φ ∧
      ∀ M : SL2 F₁, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F₁ →+* F₁) M) := by
  obtain ⟨φ, hinj, hrange, hz, hX, hX', hw, hHK⟩ := exists_coord_over hC hF₁
  have hLoc := hSec.loc
  have hF5 := hSec.F5
  have hodd : Odd (Nat.card F₁) := by rw [hF₁]; exact hLoc.q₁_odd
  have h2 : (2 : F₁) ≠ 0 := CFSG.GorensteinWalter.two_ne_zero_of_odd_card F₁ hodd
  have hK : N.K₁ = N.X₁ ⊔ N.X₁' := hLoc.K₁_eq
  have hfH : ∀ x ∈ N.H, f * x * f⁻¹ ∈ N.H := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hF5.F_normH hf) x).1 hx
  have hfw : f * φ (sl2W F₁) = φ (sl2W F₁) * f := by
    rw [← hw]; exact hfS _ hLoc.w₁_memS
  obtain ⟨σ, hσ⟩ := exists_fieldAut_of_coord h2 φ hinj hX (by rw [← hK]; exact hHK)
    (hF5.F_normX₁ f hf) (hF5.F_normX₁' f hf) hfH hfw
  exact ⟨φ, σ, hinj, hrange, hz, hX, hX', hw, hHK, hσ⟩

theorem coord_fieldAut₂ {N : T2N3 G} {u : G} (hSec : Ch6Sec5 N u) (hq : N.q₁ = N.q₂)
    (hC : Ch6Coord N.toT2N2.toT2N1) {F₂ : Type} [Field F₂] [Finite F₂] (hF₂ : Nat.card F₂ = N.q₂)
    {f : G} (hf : f ∈ N.F) (hfS : ∀ s ∈ N.S, f * s = s * f) :
    ∃ (φ : SL2 F₂ →* G) (σ : F₂ ≃+* F₂),
      Function.Injective φ ∧ φ.range = N.K₂ ∧ φ (negOne F₂) = N.z ∧
      N.X₂ = (uSub F₂).map φ ∧ N.X₂' = (lSub F₂).map φ ∧ N.w₂ = φ (sl2W F₂) ∧
      N.H ⊓ N.K₂ = (tSub F₂).map φ ∧
      ∀ M : SL2 F₂, f * φ M * f⁻¹ = φ (Matrix.SpecialLinearGroup.map (σ : F₂ →+* F₂) M) :=
  coord_fieldAut (N := N.swap) (hSec.swap hq) (hC.swap) hF₂ hf hfS

end CoordN

end CFSG.GH74.GLS.Stage4.Rest.F1Loc
