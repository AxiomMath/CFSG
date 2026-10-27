module

public import CFSG.LieType.Multipliers.L34Check
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LieType.Multipliers.L34

open Matrix Subgroup CFSG.Fischer CFSG.CosetTable

abbrev M3 : Type := Matrix (Fin 3) (Fin 3) F4

abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) F4

abbrev PSL3 : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4

namespace Mat3

def toMatrix (x : Mat3) : M3 :=
  !![x.e00, x.e01, x.e02; x.e10, x.e11, x.e12; x.e20, x.e21, x.e22]

theorem toMatrix_mul (x y : Mat3) : (x.mul y).toMatrix = x.toMatrix * y.toMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul, toMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem toMatrix_ofFun (f : Fin 3 → Fin 3 → F4) : (ofFun f).toMatrix = Matrix.of f := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem toMatrix_scalar (c : F4) : (scalar c).toMatrix = Matrix.scalar (Fin 3) c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalar, toMatrix]

theorem toMatrix_one : one.toMatrix = 1 := by
  rw [one, toMatrix_scalar, map_one]

theorem toMatrix_injective : Function.Injective toMatrix := by
  intro x y h
  have h' := fun i j => congrFun (congrFun h i) j
  obtain ⟨⟩ := x
  obtain ⟨⟩ := y
  simp only [mk.injEq]
  exact ⟨h' 0 0, h' 0 1, h' 0 2, h' 1 0, h' 1 1, h' 1 2, h' 2 0, h' 2 1, h' 2 2⟩

theorem eq_scalar_of_isScalar {x : Mat3} (h : x.isScalar = true) :
    x.toMatrix = Matrix.scalar (Fin 3) x.e00 := by
  have hx : x = scalar x.e00 := of_decide_eq_true h
  rw [← toMatrix_scalar, ← hx]

end Mat3

theorem toMatrix_transMat {i j : Fin 3} (h : i ≠ j) (c : F4) :
    (transMat i j c).toMatrix = transvection i j c := by
  rw [transMat, Mat3.toMatrix_ofFun]
  ext k l
  simp only [Matrix.of_apply, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  exact trans_entry i j k l c h

theorem toMatrix_diagMat (d₀ d₁ d₂ : F4) :
    (diagMat d₀ d₁ d₂).toMatrix = diagonal ![d₀, d₁, d₂] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagMat, Mat3.toMatrix]

theorem val_mul (A B : SL3) : ((A * B : SL3) : M3) = (A : M3) * (B : M3) := rfl

theorem det_toMatrix (x : Mat3) : x.toMatrix.det = x.det := by
  rw [Matrix.det_fin_three]
  rfl

theorem det_aMat
    : aMat.toMatrix.det = 1 := by rw [det_toMatrix]; exact det_gens.1

theorem det_aInvMat
    : aInvMat.toMatrix.det = 1 := by rw [det_toMatrix]; exact det_gens.2.1

theorem det_bMat
    : bMat.toMatrix.det = 1 := by rw [det_toMatrix]; exact det_gens.2.2.1

theorem det_bInvMat
    : bInvMat.toMatrix.det = 1 := by rw [det_toMatrix]; exact det_gens.2.2.2

def aSL : SL3 := ⟨aMat.toMatrix, det_aMat⟩

def bSL : SL3 := ⟨bMat.toMatrix, det_bMat⟩

def genSL : Fin 2 → SL3 := ![aSL, bSL]

theorem aSL_inv : ((aSL⁻¹ : SL3) : M3) = aInvMat.toMatrix := by
  have h : aSL * ⟨aInvMat.toMatrix, det_aInvMat⟩ = 1 := Subtype.ext <| by
    change aMat.toMatrix * aInvMat.toMatrix = 1
    rw [← Mat3.toMatrix_mul, ← Mat3.toMatrix_one]
    congr 1
  rw [inv_eq_of_mul_eq_one_right h]

theorem bSL_inv : ((bSL⁻¹ : SL3) : M3) = bInvMat.toMatrix := by
  have h : bSL * ⟨bInvMat.toMatrix, det_bInvMat⟩ = 1 := Subtype.ext <| by
    change bMat.toMatrix * bInvMat.toMatrix = 1
    rw [← Mat3.toMatrix_mul, ← Mat3.toMatrix_one]
    congr 1
  rw [inv_eq_of_mul_eq_one_right h]

private theorem coe_letter (l : Fin 2 × Bool) :
    ((cond l.2 (genSL l.1) (genSL l.1)⁻¹ : SL3) : M3) = (letterMat l).toMatrix := by
  obtain ⟨i, s⟩ := l
  fin_cases i <;> cases s
  · exact aSL_inv
  · rfl
  · exact bSL_inv
  · rfl

theorem coe_lift_genSL (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift genSL (FreeGroup.mk w) : SL3) : M3) = (wordMat w).toMatrix := by
  rw [FreeGroup.lift_mk]
  induction w with
  | nil => exact Mat3.toMatrix_one.symm
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, val_mul, ih, coe_letter,
      ← Mat3.toMatrix_mul]
    rfl

theorem lift_genSL_eq_one
    {w : List (Fin 2 × Bool)} (h : wordMat w = Mat3.one) :
    FreeGroup.lift genSL (FreeGroup.mk w) = 1 :=
  Subtype.ext <| by rw [coe_lift_genSL, h, Mat3.toMatrix_one]; rfl

theorem lift_genSL_mem_center
    {w : List (Fin 2 × Bool)} (h : (wordMat w).isScalar = true) :
    FreeGroup.lift genSL (FreeGroup.mk w) ∈ center SL3 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  have hs := Mat3.eq_scalar_of_isScalar h
  rw [← coe_lift_genSL] at hs
  refine ⟨(wordMat w).e00, ?_, hs.symm⟩
  have hdet := (FreeGroup.lift genSL (FreeGroup.mk w)).prop
  rw [hs, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ] at hdet
  exact hdet

private theorem exists_mem_of_wordMat
    (H : Subgroup SL3) (hH : closure (Set.range genSL) ≤ H)
    (w : List (Fin 2 × Bool)) : ∃ h ∈ H, (h : M3) = (wordMat w).toMatrix := by
  refine ⟨_, hH ?_, coe_lift_genSL w⟩
  rw [← FreeGroup.range_lift_eq_closure]
  exact ⟨_, rfl⟩

private theorem exists_mem_prod
    (H : Subgroup SL3) (hH : closure (Set.range genSL) ≤ H)
    (L : List (TransvectionStruct (Fin 3) F4)) :
    ∃ h ∈ H, (h : M3) = (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => exact ⟨1, H.one_mem, rfl⟩
  | cons t L ih =>
    obtain ⟨h, hh, he⟩ := ih
    obtain ⟨g, hg, ge⟩ := exists_mem_of_wordMat H hH (transWord t.i t.j t.c)
    refine ⟨g * h, H.mul_mem hg hh, ?_⟩
    rw [val_mul, ge, he, List.map_cons, List.prod_cons,
      transCheck t.i t.j t.c t.hij, toMatrix_transMat t.hij]
    rfl

theorem closure_genSL : closure (Set.range genSL) = ⊤ := by
  set H := closure (Set.range genSL)
  rw [eq_top_iff]
  intro A _
  obtain ⟨L, L', D, hA⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (A : M3)
  obtain ⟨h₁, hh₁, he₁⟩ := exists_mem_prod H le_rfl L
  obtain ⟨h₂, hh₂, he₂⟩ := exists_mem_prod H le_rfl L'
  set g : SL3 := h₁⁻¹ * A * h₂⁻¹
  have hg : (g : M3) = diagonal D := by
    have e₁ : ((h₁⁻¹ : SL3) : M3) * h₁ = 1 := by
      rw [← val_mul, inv_mul_cancel]; rfl
    have e₂ : (h₂ : M3) * ((h₂⁻¹ : SL3) : M3) = 1 := by
      rw [← val_mul, mul_inv_cancel]; rfl
    simp only [g, val_mul]
    rw [hA, ← he₁, ← he₂, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e₁, Matrix.one_mul,
      Matrix.mul_assoc, e₂, Matrix.mul_one]
  have hD : D 0 * D 1 * D 2 = 1 := by
    have := g.prop
    rw [hg, det_diagonal, Fin.prod_univ_three] at this
    exact this
  have hDg : diagonal D = diagonal ![D 0, D 1, D 2] := by
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨h₃, hh₃, he₃⟩ := exists_mem_of_wordMat H le_rfl (diagWord (D 0) (D 1))
  rw [diagCheck _ _ _ hD, toMatrix_diagMat, ← hDg, ← hg] at he₃
  have hgH : g ∈ H := by rw [← Subtype.ext he₃]; exact hh₃
  have hA' : A = h₁ * g * h₂ := by simp only [g]; group
  rw [hA']
  exact H.mul_mem (H.mul_mem hh₁ hgH) hh₂

theorem card_SL3 : Nat.card SL3 = 60480 := by
  rw [Matrix.card_SL_field, F4.card]
  simp [Fin.prod_univ_three]

theorem card_center_SL3_le : Nat.card (center SL3) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  exact (card_rootsOfUnity F4 _).trans (by simp)

theorem card_PSL3_ge : 20160 ≤ Nat.card PSL3 := by
  have h := (center SL3).card_eq_card_quotient_mul_card_subgroup
  rw [card_SL3] at h
  have := card_center_SL3_le
  change 60480 = Nat.card PSL3 * Nat.card (center SL3) at h
  nlinarith

noncomputable def toPSL : SL3 →* PSL3 := QuotientGroup.mk' _

theorem toPSL_surjective : Function.Surjective toPSL := QuotientGroup.mk'_surjective _

noncomputable def genX : Fin 2 → PSL3 := fun i => toPSL (genSL i)

theorem lift_genX
    : FreeGroup.lift genX = toPSL.comp (FreeGroup.lift genSL) :=
  FreeGroup.ext_hom _ _ fun i => by simp [genX]

theorem toPSL_eq_one {g : SL3} (h : g ∈ center SL3) : toPSL g = 1 :=
  (QuotientGroup.eq_one_iff g).mpr h

theorem lift_genX_rels
    : ∀ r ∈ wordSet rels, FreeGroup.lift genX r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  have h := rels_isScalar
  rw [List.all_eq_true] at h
  rw [lift_genX, MonoidHom.comp_apply]
  exact toPSL_eq_one (lift_genSL_mem_center (h w hw))

theorem closure_genX : closure (Set.range genX) = ⊤ := by
  have : Set.range genX = toPSL '' Set.range genSL := by
    rw [← Set.range_comp]
    rfl
  rw [this, ← MonoidHom.map_closure, closure_genSL, Subgroup.map_top, MonoidHom.range_eq_top]
  exact toPSL_surjective

theorem isPresentation_genX
    : IsPresentation genX (wordSet rels) := by
  obtain ⟨hfin, hle⟩ := cyclic_card_le
  exact IsPresentation.of_card_le lift_genX_rels closure_genX (hle.trans card_PSL3_ge)

section FieldChange

variable {R S : Type} [CommRing R] [CommRing S] (n : Type) [Fintype n] [DecidableEq n]

noncomputable def slEquiv (e : R ≃+* S) :
    Matrix.SpecialLinearGroup n R ≃* Matrix.SpecialLinearGroup n S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)
    (MonoidHom.ext fun A => Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp)

noncomputable def pslEquiv (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup n R ≃* Matrix.ProjectiveSpecialLinearGroup n S :=
  QuotientGroup.congr _ _ (slEquiv n e) (map_center_eq (slEquiv n e))

end FieldChange

end CFSG.LieType.Multipliers.L34
