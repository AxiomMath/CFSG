module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClGraph
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBClField

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Cl

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (exists_frame det_eq_one_of_mem_commutator)
open CFSG.ComponentClassification.Burgoyne.C (exists_statedSU_two_equiv)
open CFSG.ComponentClassification.CatLeafProof.EndOddLin (two_ne_zero_of_unitary QuatBlock
  quatBlock_map_of_sl2)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (hu : UnitaryFieldData p f K) {n : ℕ}

section Frame

variable {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {s : K}
  (hs : s ≠ 0) {R : GL (Fin n) hu.fixedField}
  (hR : (R : Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype =
    s • ((P.map hu.bar)ᵀ * P))

include hPPi hPiP in
theorem fixOf_uLift_bar_le {A : uU hu n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map hu.bar) = P) :
    fixOf (uLift hu A (barEq hu)) ≤ (gHom hu hPPi hPiP hs hR).range := by
  intro g hg
  have hg' : uLift hu A (barEq hu) g = g := hg
  set gm := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hgm
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  set Aim := (((A : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAim
  have hAi : Aim * Am = 1 := by rw [hAim, hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : Am * gm.map hu.bar * Aim = gm := by
    have e0 := congrArg (fun x : StatedSU n (p ^ f) K =>
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg'
    simp only [coe_uLift] at e0
    exact e0
  have hAg : Am * gm.map hu.bar = gm * Am := by
    calc Am * gm.map hu.bar = Am * gm.map hu.bar * (Aim * Am) := by rw [hAi, Matrix.mul_one]
      _ = gm * Am := by rw [← Matrix.mul_assoc, e]
  have hPb : P.map hu.bar * Pi.map hu.bar = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero hu.bar) (map_one hu.bar)]
  have hAP : Am * P.map hu.bar = b⁻¹ • P := by
    calc Am * P.map hu.bar = b⁻¹ • (b • (Am * P.map hu.bar)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • P := by rw [hbP]
  have hPbi : Pi.map hu.bar = b • (Pi * Am) := by
    have e1 : (b • (Pi * Am)) * P.map hu.bar = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc, hAP, Matrix.mul_smul, hPiP, smul_smul,
        mul_inv_cancel₀ hb, one_smul]
    calc Pi.map hu.bar = ((b • (Pi * Am)) * P.map hu.bar) * Pi.map hu.bar := by
          rw [e1, Matrix.one_mul]
      _ = b • (Pi * Am) := by rw [Matrix.mul_assoc, hPb, Matrix.mul_one]
  set Y₁ := Pi * gm * P with hY₁
  have hY₁b : Y₁.map hu.bar = Y₁ := by
    rw [hY₁, Matrix.map_mul, Matrix.map_mul, hPbi]
    calc b • (Pi * Am) * gm.map hu.bar * P.map hu.bar
        = b • (Pi * (Am * gm.map hu.bar) * P.map hu.bar) := by
          rw [Matrix.smul_mul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = b • (Pi * gm * (Am * P.map hu.bar)) := by rw [hAg]; simp only [Matrix.mul_assoc]
      _ = Pi * gm * P := by
          rw [hAP, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hb, one_smul]
  obtain ⟨Y, hY⟩ := exists_fmap_of_bar hu hY₁b
  have hgU : (gm.map hu.bar)ᵀ * gm = 1 := ((mem_unitarySU_iff hu).1 g.2).2
  have hg1 : gm.det = 1 := ((mem_unitarySU_iff hu).1 g.2).1
  have e1 : P * Y₁ = gm * P := by
    rw [hY₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have e2 : P.map hu.bar * Y₁ = gm.map hu.bar * P.map hu.bar := by
    have e3 := congrArg (fun M => M.map hu.bar) e1
    simp only [Matrix.map_mul, hY₁b] at e3
    exact e3
  have hiso : (Y.map hu.fixedField.subtype)ᵀ *
      (R : Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype *
      Y.map hu.fixedField.subtype =
      (R : Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype := by
    rw [hY, hR, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    calc Y₁ᵀ * ((P.map hu.bar)ᵀ * P) * Y₁ = (P.map hu.bar * Y₁)ᵀ * (P * Y₁) := by
          rw [transpose_mul (P.map hu.bar) Y₁]; simp only [Matrix.mul_assoc]
      _ = (gm.map hu.bar * P.map hu.bar)ᵀ * (gm * P) := by rw [e1, e2]
      _ = (P.map hu.bar)ᵀ * ((gm.map hu.bar)ᵀ * gm) * P := by
          rw [transpose_mul (gm.map hu.bar) (P.map hu.bar)]; simp only [Matrix.mul_assoc]
      _ = (P.map hu.bar)ᵀ * P := by rw [hgU, Matrix.mul_one]
  have hYR : Yᵀ * (R : Matrix (Fin n) (Fin n) hu.fixedField) * Y = R := by
    apply fmap_injective hu
    change (Yᵀ * (R : Matrix (Fin n) (Fin n) hu.fixedField) * Y).map hu.fixedField.subtype =
      (R : Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map]
    exact hiso
  have hdetY : Y.det = 1 := by
    have e3 : (Y.map hu.fixedField.subtype).det = 1 := by
      have hPP : Pi.det * P.det = 1 := by rw [← det_mul, hPiP, det_one]
      rw [hY, hY₁, det_mul, det_mul]
      calc Pi.det * gm.det * P.det = gm.det * (Pi.det * P.det) := by ring
        _ = 1 := by rw [hg1, hPP, mul_one]
    have e4 := RingHom.map_det hu.fixedField.subtype Y
    rw [RingHom.mapMatrix_apply] at e4
    rw [← e4] at e3
    exact hu.fixedField.subtype_injective (by rw [e3, map_one])
  set YG : GL (Fin n) hu.fixedField := Matrix.nonsingInvUnit Y (by rw [hdetY]; exact isUnit_one)
    with hYG
  have hYmem : YG ∈ iso1 hu R := by
    refine ⟨(CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hYR, ?_⟩
    show YG ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) hu.fixedField →*
      hu.fixedFieldˣ).ker
    rw [MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact hdetY
  refine ⟨⟨YG, hYmem⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_gHom]
  change P * Y.map hu.fixedField.subtype * Pi = gm
  rw [hY, hY₁]
  calc P * (Pi * gm * P) * Pi = (P * Pi) * gm * (P * Pi) := by simp only [Matrix.mul_assoc]
    _ = gm := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]

include hPPi hPiP in
theorem range_gHom_le_fixOf {A : uU hu n} {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map hu.bar) = P) :
    (gHom hu hPPi hPiP hs hR).range ≤ fixOf (uLift hu A (barEq hu)) := by
  rintro _ ⟨X, rfl⟩
  exact uLift_gHom hu hPPi hPiP hs hR hb hbP X

include hPPi hPiP in
theorem gHom_not_mem_scalars {X : iso1 hu R}
    (hX : ∀ c : hu.fixedField, ((X : GL (Fin n) hu.fixedField) :
      Matrix (Fin n) (Fin n) hu.fixedField) ≠ c • 1) (hn : 1 ≤ n) :
    gHom hu hPPi hPiP hs hR X ∉
      (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K) := by
  intro hmem
  rw [mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : P * ((X : GL (Fin n) hu.fixedField) :
      Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype * Pi = (c : K) • 1 := by
    have e := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K)) hc
    simp only [GeneralLinearGroup.coe_scalar] at e
    have e2 : (((gHom hu hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = P * ((X : GL (Fin n) hu.fixedField) :
          Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype * Pi :=
      coe_gHom hu hPPi hPiP hs hR X
    rw [← e2, ← e, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hXm : ((X : GL (Fin n) hu.fixedField) :
      Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype = (c : K) • 1 := by
    calc ((X : GL (Fin n) hu.fixedField) : Matrix (Fin n) (Fin n) hu.fixedField).map
          hu.fixedField.subtype
        = Pi * (P * ((X : GL (Fin n) hu.fixedField) :
            Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype * Pi) * P := by
          simp only [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPiP, Matrix.mul_one]
      _ = (c : K) • 1 := by rw [hc', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPiP]
  set x0 := ((X : GL (Fin n) hu.fixedField) : Matrix (Fin n) (Fin n) hu.fixedField)
    ⟨0, hn⟩ ⟨0, hn⟩ with hx0
  apply hX x0
  ext i j
  have e := congrFun (congrFun hXm i) j
  have e0 := congrFun (congrFun hXm ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.map_apply, Subfield.subtype_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one] at e0
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.map_apply, Subfield.subtype_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      smul_eq_mul, mul_one] at e
    simp [hx0, e, e0]
  · simp only [Matrix.map_apply, Subfield.subtype_apply, Matrix.smul_apply,
      Matrix.one_apply_ne hij, smul_eq_mul, mul_zero] at e
    simp [e, Matrix.one_apply_ne hij]

end Frame

section Types

variable [Finite K] {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
  {b s : K} (hb : b ≠ 0) (hs : s ≠ 0) {A : uU hu n}
  (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map hu.bar) = P)
  {R : GL (Fin n) hu.fixedField}
  (hR : (R : Matrix (Fin n) (Fin n) hu.fixedField).map hu.fixedField.subtype =
    s • ((P.map hu.bar)ᵀ * P))

include hPPi hPiP hb hs hbP hR in
theorem noL2At_uGraph_orth (hp2 : p ≠ 2) (hn : 6 ≤ n) (hn1 : 1 ≤ n)
    (hRs : (R : Matrix (Fin n) (Fin n) hu.fixedField)ᵀ = R) :
    NoL2At (uConjAut hu hn1 A * uFieldAut hu hn1 (barEq hu)) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hF2 := ringChar_subfield_ne_two hK hu.fixedField
  have h2F : (2 : hu.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  have hZ := scalars_subgroupOf_le_center (H := StatedSU n (p ^ f) K)
  set G := gHom hu hPPi hPiP hs hR with hG
  set I := CatalogueBGraphForm.isometryGroup n hu.fixedField R with hI
  set Ω := ⁅I, I⁆ with hΩ
  have hΩle : Ω ≤ iso1 hu R := by
    intro X hX
    refine ⟨commutator_le_self' I hX, ?_⟩
    show X ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) hu.fixedField →* hu.fixedFieldˣ).ker
    rw [MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_eq_one_of_mem_commutator hX
  set L := (Ω.subgroupOf (iso1 hu R)).map G with hL
  have hfix1 := fixOf_uLift_bar_le hu hPPi hPiP hs hR hb hbP
  have hLF : L ≤ fixOf (uLift hu A (barEq hu)) :=
    (map_le_range _ _).trans (range_gHom_le_fixOf hu hPPi hPiP hs hR hb hbP)
  have hcomm : ⁅fixOf (uLift hu A (barEq hu)), fixOf (uLift hu A (barEq hu))⁆ ≤ L := by
    refine (commutator_mono hfix1 hfix1).trans ?_
    rw [MonoidHom.range_eq_map, ← map_commutator]
    refine map_mono ?_
    rw [commutator_le]
    intro a _ b _
    rw [mem_subgroupOf]
    have e : ((⁅a, b⁆ : iso1 hu R) : GL (Fin n) hu.fixedField) =
        ⁅(a : GL (Fin n) hu.fixedField), (b : GL (Fin n) hu.fixedField)⁆ := by
      simp [commutatorElement_def]
    rw [e]
    exact commutator_mem_commutator (mem_inf.1 a.2).1 (mem_inf.1 b.2).1
  have hq : IsQuasisimple L :=
    LocalCores.isQuasisimple_of_mulEquiv (((Ω.subgroupOf (iso1 hu R)).equivMapOfInjective G
      (gHom_injective hu hPPi hPiP hs hR)).symm.trans (Subgroup.subgroupOfEquivOfLe hΩle)).symm
      (isQuasisimple_orthCommutator hF2 hn R hRs)
  obtain ⟨P₀, w, -, hw1, hP₀⟩ := exists_frame hF2 (by omega) R hRs one_ne_zero
  obtain ⟨E, F', hFE, hc1, hc2⟩ := frame_emb (by omega : 4 ≤ n) (Units.mul_inv P₀)
    (Units.inv_mul P₀) (fun a => hw1 _ (by simp; omega)) hP₀
  obtain ⟨X, Y, Z, hX, hY, hz2, hxz, hyz, hxy, hZn⟩ :=
    exists_orth_quat_pair h2F (by omega) hFE hc1 hc2
  have hZΩ : Z ∈ Ω := hxz ▸ pow_mem hX 2
  set x' : iso1 hu R := ⟨X, hΩle hX⟩ with hx'
  set y' : iso1 hu R := ⟨Y, hΩle hY⟩ with hy'
  set z' : iso1 hu R := ⟨Z, hΩle hZΩ⟩ with hz'
  refine noL2At_of_fix_layer hZ (uLift_proj hu hn1 A (barEq hu)) hLF hcomm ?_
  refine quatBlock_map_of_pair hq (x := G x') (y := G y') (z := G z')
    ⟨x', mem_subgroupOf.2 hX, rfl⟩ ⟨y', mem_subgroupOf.2 hY, rfl⟩ ?_ ?_ ?_ ?_
    (gHom_not_mem_scalars hu hPPi hPiP hs hR hZn hn1)
  · rw [← map_pow, show z' ^ 2 = 1 from Subtype.ext hz2, map_one]
  · rw [← map_pow, show x' ^ 2 = z' from Subtype.ext hxz]
  · rw [← map_pow, show y' ^ 2 = z' from Subtype.ext hyz]
  · rw [← map_mul, ← map_mul, ← map_mul, show x' * y' = z' * (y' * x') from Subtype.ext hxy]

include hPPi hPiP hb hs hbP hR in
theorem noL2At_uGraph_symp (hp2 : p ≠ 2) (hn : 4 ≤ n) (hn1 : 1 ≤ n)
    (hRa : (R : Matrix (Fin n) (Fin n) hu.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) hu.fixedField)) :
    NoL2At (uConjAut hu hn1 A * uFieldAut hu hn1 (barEq hu)) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hF2 := ringChar_subfield_ne_two hK hu.fixedField
  have h2F : (2 : hu.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  have hZ := scalars_subgroupOf_le_center (H := StatedSU n (p ^ f) K)
  set G := gHom hu hPPi hPiP hs hR with hG
  set I := CatalogueBGraphForm.isometryGroup n hu.fixedField R with hI
  have hIiso : iso1 hu R = I := by
    refine le_antisymm inf_le_left fun X hX => ⟨hX, ?_⟩
    show X ∈ (Matrix.GeneralLinearGroup.det : GL (Fin n) hu.fixedField →* hu.fixedFieldˣ).ker
    rw [MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_eq_one_of_mem_isometryGroup_alt hF2 hn hRa hX
  have hq : IsQuasisimple G.range :=
    LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective
      (gHom_injective hu hPPi hPiP hs hR))
      (LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hIiso).symm
        (isQuasisimple_isometryGroup_alt hF2 hn hRa))
  have hLF := range_gHom_le_fixOf hu hPPi hPiP hs hR hb hbP
  have hcomm : ⁅fixOf (uLift hu A (barEq hu)), fixOf (uLift hu A (barEq hu))⁆ ≤ G.range :=
    (commutator_le_self' _).trans (fixOf_uLift_bar_le hu hPPi hPiP hs hR hb hbP)
  obtain ⟨e, e', hee⟩ := exists_hyperbolic_pair (by omega) R
  obtain ⟨E, F', hFE, h1, h2'⟩ := alt_emb h2F hRa hee
  let ι : SL(2, hu.fixedField) →* iso1 hu R :=
    (SpecialLinearGroup.toGL.comp (embSL hFE)).codRestrict (iso1 hu R) fun g => by
      refine ⟨(CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 ?_, ?_⟩
      · exact embT_isometry hFE h1 h2' (transpose_J₂_mul g)
      · show SpecialLinearGroup.toGL (embSL hFE g) ∈ (Matrix.GeneralLinearGroup.det :
          GL (Fin n) hu.fixedField →* hu.fixedFieldˣ).ker
        rw [MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one]
        exact (embSL hFE g).2
  refine noL2At_of_fix_layer hZ (uLift_proj hu hn1 A (barEq hu)) hLF hcomm
    (quatBlock_map_of_sl2 hq hF2 (G.comp ι) (fun g => ⟨ι g, rfl⟩) ?_)
  refine gHom_not_mem_scalars hu hPPi hPiP hs hR (X := ι (-1)) (fun c hc => ?_) hn1
  change embT E F' ((-1 : SL(2, hu.fixedField)) : Matrix (Fin 2) (Fin 2) hu.fixedField) =
    c • 1 at hc
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at hc
  exact embT_neg_one_ne_smul h2F hFE (by simp; omega) c hc

end Types

theorem noL2At_uGraph [Finite K] (hp2 : p ≠ 2) (hn : 6 ≤ n) (hn1 : 1 ≤ n) {A : uU hu n} {c : K}
    (hAc : ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map hu.bar = c • 1) :
    NoL2At (uConjAut hu hn1 A * uFieldAut hu hn1 (barEq hu)) := by
  have : Fact p.Prime := ⟨hu.prime⟩
  have := hu.charP
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hF2 := ringChar_subfield_ne_two hK hu.fixedField
  have h2F : (2 : hu.fixedField) ≠ 0 := Ring.two_ne_zero hF2
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hA : (Am.map hu.bar)ᵀ * Am = 1 := (mem_uU hu).1 A.2
  have hc0 : c ≠ 0 := by
    rintro rfl
    have e : Am.map hu.bar = 0 := by
      calc Am.map hu.bar = ((Am.map hu.bar)ᵀ * Am) * Am.map hu.bar := by rw [hA, Matrix.one_mul]
        _ = 0 := by rw [Matrix.mul_assoc, hAc, zero_smul, Matrix.mul_zero]
    rw [e, transpose_zero, Matrix.zero_mul] at hA
    have := congrFun (congrFun hA ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  obtain ⟨hc1, P, Pi, b, s, R, hPPi, hPiP, hb, hs, hbP, hR, hsym, halt⟩ :=
    exists_graph_frame hu hp2 (by omega) hA hc0 hAc
  have hdetP : P.det ≠ 0 := by
    intro e
    have := congrArg Matrix.det hPPi
    rw [Matrix.det_mul, e, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetPb : (P.map hu.bar).det ≠ 0 := by
    have e := RingHom.map_det hu.bar P
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact (map_ne_zero hu.bar).2 hdetP
  have hdetR : R.det ≠ 0 := by
    intro e
    have e1 := congrArg Matrix.det hR
    have e2 := RingHom.map_det hu.fixedField.subtype R
    rw [RingHom.mapMatrix_apply] at e2
    rw [← e2, e, map_zero, Matrix.det_smul, Matrix.det_mul, det_transpose] at e1
    exact mul_ne_zero (pow_ne_zero _ hs) (mul_ne_zero hdetPb hdetP) e1.symm
  set RG : GL (Fin n) hu.fixedField := Matrix.nonsingInvUnit R (isUnit_iff_ne_zero.2 hdetR)
    with hRGdef
  rcases hc1 with rfl | rfl
  · exact noL2At_uGraph_orth hu hPPi hPiP hb hs hbP (R := RG) hR hp2 hn hn1 (hsym rfl)
  · exact noL2At_uGraph_symp hu hPPi hPiP hb hs hbP (R := RG) hR hp2 (by omega) hn1 (halt rfl)

end CFSG.ComponentClassification.Burgoyne.Cl
