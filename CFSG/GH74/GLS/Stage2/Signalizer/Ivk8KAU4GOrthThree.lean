module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3N
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4GO3S
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGOrth
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAU4SplitThree

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
  CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.CatalogueBLinearHigherB CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

theorem kaU4G3_normalize {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    (hF2 : ringChar h.fixedField ≠ 2) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K}
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    {R : GL (Fin 4) h.fixedField}
    (hRs : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = R)
    (hR : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P)) :
    ∃ (P' Pi' : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → h.fixedField)
      (hw : PSL.OrthNF w) (Q : GL (Fin 4) h.fixedField),
      P' * Pi' = 1 ∧ Pi' * P' = 1 ∧
      b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P'.map h.bar) = P' ∧
      ((PSL.diagGL hw.1 : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
        h.fixedField.subtype = s • ((P'.map h.bar)ᵀ * P') ∧
      ((Q : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ *
        ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) * Q =
        diagonal w := by
  obtain ⟨Q, w, hw, hQ⟩ := PSL.exists_orth_normal_form hF2 (by norm_num) R hRs
  set Qm := ((Q : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) with hQm
  set Qim := ((Q⁻¹ : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField) with hQim
  have hQQ : Qm * Qim = 1 := by rw [hQm, hQim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : Qim * Qm = 1 := by rw [hQm, hQim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hone : (1 : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  set P' := P * Qm.map h.fixedField.subtype with hP'
  set Pi' := Qim.map h.fixedField.subtype * Pi with hPi'
  have hPPi' : P' * Pi' = 1 := by
    calc P' * Pi' = P * (Qm * Qim).map h.fixedField.subtype * Pi := by
          rw [Matrix.map_mul]; simp only [hP', hPi', Matrix.mul_assoc]
      _ = 1 := by rw [hQQ, hone, Matrix.mul_one, hPPi]
  have hPiP' : Pi' * P' = 1 := by
    calc Pi' * P' = Qim.map h.fixedField.subtype * (Pi * P) * Qm.map h.fixedField.subtype := by
          simp only [hP', hPi', Matrix.mul_assoc]
      _ = 1 := by rw [hPiP, Matrix.mul_one, ← Matrix.map_mul, hQQ', hone]
  have hbP' : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P'.map h.bar) = P' := by
    rw [hP', Matrix.map_mul, map_bar_fmap, ← Matrix.mul_assoc, ← Matrix.smul_mul, hbP]
  have hR' : ((PSL.diagGL hw.1 : GL (Fin 4) h.fixedField) :
      Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype =
        s • ((P'.map h.bar)ᵀ * P') := by
    rw [PSL.coe_diagGL, ← hQ, Matrix.map_mul, Matrix.map_mul, hR, hP', Matrix.map_mul,
      map_bar_fmap, transpose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, transpose_map]
  exact ⟨P', Pi', w, hw, Q, hPPi', hPiP', hbP', hR', hQ⟩

theorem kaU4G3_of_data {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    (hs : s ≠ 0) {w : Fin 4 → h.fixedField} (hw : PSL.OrthNF w)
    (hR : ((PSL.diagGL hw.1 : GL (Fin 4) h.fixedField) :
      Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype =
        s • ((P.map h.bar)ᵀ * P))
    (hdata : PSL.OrthComponentData 4 h.fixedField (PSL.diagGL hw.1)) :
    KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hq : ¬(4 = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
  have hnq : ((4 : ℕ), p ^ f) ≠ (3, 2) := fun e => by
    have := congrArg Prod.fst e
    simp at this
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hinj := ka_conj_inj_pu hK (by norm_num) hnq
  set R : GL (Fin 4) h.fixedField := PSL.diagGL hw.1 with hRdef
  set Iso := CatalogueBGraphForm.isometryGroup 4 h.fixedField R with hIso
  obtain ⟨hperf, m, L, hsup, hL⟩ := hdata
  have hcle : ⁅Iso, Iso⁆ ≤ Iso := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hΩ1 : ⁅Iso, Iso⁆ ≤ iso1 h R := by
    intro X hX
    refine Subgroup.mem_inf.2 ⟨hcle hX, ?_⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact PSL.det_eq_one_of_mem_commutator hX
  have hΩ : ∀ (Y : GL (Fin 4) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin 4) (Fin 4) h.fixedField) →
          ∀ X ∈ ⁅Iso, Iso⁆, Y * X * Y⁻¹ ∈ ⁅Iso, Iso⁆ :=
    fun Y μ hμ hY X hX => conj_mem_commutator_isometryGroup_of_similitude hY hμ hX
  set G := gHom h hPPi hPiP hs hR with hG
  set φ := uLift h A (barEq h) with hφdef
  set FΩ := ((⁅Iso, Iso⁆).subgroupOf (iso1 h R)).map G with hFΩ
  have hφ : ∀ g, (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h) :
      MulAut (StatedProj (StatedSU 4 (p ^ f) K))) (projH (StatedSU 4 (p ^ f) K) g) =
        projH (StatedSU 4 (p ^ f) K) (φ g) :=
    fun g => uLift_proj h (by norm_num) A (barEq h) g
  have hF1 : ∀ g ∈ FΩ, φ g = g := by
    rintro _ ⟨X', -, rfl⟩
    exact uLift_gHom h hPPi hPiP hs hR hb hbP X'
  have hF2 : ∀ H : StatedSU 4 (p ^ f) K, H⁻¹ * φ H ∈
      (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) →
      ∀ g ∈ FΩ, H * g * H⁻¹ ∈ FΩ :=
    fun H hH g hg => conj_mem_map_gHom h hPPi hPiP hs hR (by norm_num) hb hbP hΩ1 hΩ hH hg
  have hQq : ∀ i, IsQuasisimple (((L i).subgroupOf (iso1 h R)).map G) := by
    intro i
    obtain ⟨hq', hLΩ, -⟩ := hL i
    have e1 : (L i).subgroupOf (iso1 h R) ≃* L i := subgroupOfEquivOfLe (hLΩ.trans hΩ1)
    have e2 : (L i).subgroupOf (iso1 h R) ≃* ((L i).subgroupOf (iso1 h R)).map G :=
      ((L i).subgroupOf (iso1 h R)).equivMapOfInjective G (gHom_injective h hPPi hPiP hs hR)
    exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hq'
  have hΩsup : (⁅Iso, Iso⁆.subgroupOf (iso1 h R)) = ⨆ i, (L i).subgroupOf (iso1 h R) := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : GL (Fin 4) h.fixedField) ∈ ⨆ i, L i := by rw [hsup]; exact hx
      have hmap : (⨆ i, (L i).subgroupOf (iso1 h R)).map (iso1 h R).subtype = ⨆ i, L i := by
        rw [Subgroup.map_iSup]
        exact iSup_congr fun i => by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 ((hL i).2.1.trans hΩ1)]
      rw [← hmap] at hx'
      obtain ⟨x', hx', e⟩ := hx'
      rwa [← Subtype.ext e]
    · exact iSup_le fun i x hx => (hL i).2.1 hx
  have hFsup : FΩ = ⨆ i, ((L i).subgroupOf (iso1 h R)).map G := by
    rw [hFΩ, hΩsup, Subgroup.map_iSup]
  have hperfA : ⁅⁅Iso, Iso⁆.subgroupOf (iso1 h R), ⁅Iso, Iso⁆.subgroupOf (iso1 h R)⁆ =
      ⁅Iso, Iso⁆.subgroupOf (iso1 h R) := by
    apply Subgroup.map_injective (iso1 h R).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hΩ1, hperf]
  have hperfF : ⁅FΩ, FΩ⁆ = FΩ := by rw [hFΩ, ← map_commutator, hperfA]
  refine ka_orth_all_of_components hinj (projH (StatedSU 4 (p ^ f) K)) projH_surjective φ hφ
    hF1 (fun H hH => hF2 H (projH_eq_projH_iff.1 hH.symm)) hperfF
    (fun i => ((L i).subgroupOf (iso1 h R)).map G) hQq
    (fun i => Subgroup.map_mono (fun x hx => (hL i).2.1 hx)) hFsup.le ?_ ?_
  ·
    rintro i _ ⟨x, hx, rfl⟩ _ ⟨l, hl, rfl⟩
    refine ⟨x * l * x⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (hL i).2.2 _ hx _ hl
  ·
    intro p' hp' hp2' e hpg hc hfixL
    have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp' hp2' hpg (Subgroup.mem_zpowers e)
    obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h (by norm_num) hq e
    refine kaUGOrth_trivial h hp2 (by norm_num) hPPi hPiP hb hbP hs hw hR hodd hc ?_
    intro X hX
    have e1 := uSemilinear_eq_of_fix h (by norm_num) hperfF
      (fun g hg => hfixL _ ⟨g, hg, rfl⟩) (g := G ⟨X, hΩ1 hX⟩)
      ⟨⟨X, hΩ1 hX⟩, Subgroup.mem_subgroupOf.2 hX, rfl⟩
    rwa [coe_gHom] at e1

theorem kaU4G3_nonsplit {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (hp3 : p ^ f = 3) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    (hs : s ≠ 0) {R : GL (Fin 4) h.fixedField}
    (hRs : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = R)
    (hR : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    (hns : ¬ ∃ S : Submodule h.fixedField (Fin 4 → h.fixedField),
      Module.finrank h.fixedField ↥S = 2 ∧ ∀ x ∈ S, matrixQuadraticForm R x = 0) :
    KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h)) := by
  have hF3 : Nat.card h.fixedField = 3 := by rw [h.card_fixedField, hp3]
  have : Finite h.fixedField := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
  have hF2 : ringChar h.fixedField ≠ 2 := ka_ringChar_ne_two_of_card_three hF3
  obtain ⟨P', Pi', w, hw, Q, hPPi', hPiP', hbP', hR', hQ⟩ :=
    kaU4G3_normalize h hF2 hPPi hPiP hbP hRs hR
  have hsymD : ((PSL.diagGL hw.1 : GL (Fin 4) h.fixedField) :
      Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = PSL.diagGL hw.1 := by
    rw [PSL.coe_diagGL, diagonal_transpose]
  have hnsD := ka_noSplit_congr (R := R) (P := Q) (R' := PSL.diagGL hw.1)
    (by rw [PSL.coe_diagGL]; exact hQ) hns
  exact kaU4G3_of_data h hp2 hPPi' hPiP' hb hbP' hs hw hR'
    (ka_orthData_nonsplit_three hF3 (PSL.diagGL hw.1) hsymD hnsD)

theorem kaU4G3_exists_of_fixed {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    (hs : s ≠ 0) {R : GL (Fin 4) h.fixedField}
    (hR : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {g : StatedSU 4 (p ^ f) K} (hg : uLift h A (barEq h) g = g) :
    ∃ X : iso1 h R, gHom h hPPi hPiP hs hR X = g := by
  set Am := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAm
  set gm := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hgm
  set Ami := (((A : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAmi
  have hiA : Ami * Am = 1 := by rw [hAm, hAmi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcomm : Am * gm.map h.bar = gm * Am := by
    have e := congrArg (fun x : StatedSU 4 (p ^ f) K =>
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hg
    simp only [coe_uLift] at e
    calc Am * gm.map h.bar = (Am * gm.map h.bar * Ami) * Am := by
          rw [Matrix.mul_assoc _ Ami, hiA, Matrix.mul_one]
      _ = gm * Am := by rw [show Am * gm.map h.bar * Ami = gm from e]
  have hPb : P.map h.bar * Pi.map h.bar = 1 := by
    rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]
  have hAP : Am * P.map h.bar = b⁻¹ • P := by
    calc Am * P.map h.bar = b⁻¹ • (b • (Am * P.map h.bar)) := by
          rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • P := by rw [hbP]
  have hPbi : Pi.map h.bar = b • (Pi * Am) := by
    have e1 : (b • (Pi * Am)) * P.map h.bar = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc, hAP, Matrix.mul_smul, hPiP, smul_smul,
        mul_inv_cancel₀ hb, one_smul]
    calc Pi.map h.bar = ((b • (Pi * Am)) * P.map h.bar) * Pi.map h.bar := by
          rw [e1, Matrix.one_mul]
      _ = b • (Pi * Am) := by rw [Matrix.mul_assoc, hPb, Matrix.mul_one]
  set X0 := Pi * gm * P with hX0
  have hX0b : X0.map h.bar = X0 := by
    rw [hX0, Matrix.map_mul, Matrix.map_mul, hPbi]
    calc b • (Pi * Am) * gm.map h.bar * P.map h.bar
        = b • (Pi * (Am * gm.map h.bar) * P.map h.bar) := by
          rw [Matrix.smul_mul, Matrix.smul_mul]; simp only [Matrix.mul_assoc]
      _ = b • (Pi * gm * (Am * P.map h.bar)) := by
          rw [hcomm]; simp only [Matrix.mul_assoc]
      _ = Pi * gm * P := by rw [hAP, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hb, one_smul]
  obtain ⟨Y, hY⟩ := exists_fmap_of_bar h hX0b
  obtain ⟨hdetg, hgU⟩ := (mem_unitarySU_iff h).1 g.2
  have hgram : (X0.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * X0 = (P.map h.bar)ᵀ * P := by
    have hPbT : (Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, hPb, transpose_one]
    rw [hX0, conjT_mul h, conjT_mul h]
    calc (P.map h.bar)ᵀ * ((gm.map h.bar)ᵀ * (Pi.map h.bar)ᵀ) * ((P.map h.bar)ᵀ * P) *
          (Pi * gm * P) =
        (P.map h.bar)ᵀ * (gm.map h.bar)ᵀ * ((Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ) * (P * Pi) *
          gm * P := by simp only [Matrix.mul_assoc]
      _ = (P.map h.bar)ᵀ * P := by
          rw [hPbT, hPPi, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc _ _ gm, hgU,
            Matrix.mul_one]
  have hYR : Yᵀ * (R : Matrix (Fin 4) (Fin 4) h.fixedField) * Y =
      (R : Matrix (Fin 4) (Fin 4) h.fixedField) := by
    apply fmap_injective h
    show (Yᵀ * (R : Matrix (Fin 4) (Fin 4) h.fixedField) * Y).map h.fixedField.subtype =
      (R : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype
    rw [Matrix.map_mul, Matrix.map_mul, transpose_map, hY, hR, Matrix.mul_smul,
      Matrix.smul_mul]
    congr 1
    have e : X0ᵀ = (X0.map h.bar)ᵀ := by rw [hX0b]
    rw [e]
    exact hgram
  have hdetY : Y.det = 1 := by
    have e1 := RingHom.map_det h.fixedField.subtype Y
    rw [RingHom.mapMatrix_apply, hY] at e1
    have e2 : X0.det = 1 := by
      rw [hX0, Matrix.det_mul, Matrix.det_mul]
      have := congrArg Matrix.det hPiP
      rw [Matrix.det_mul, Matrix.det_one] at this
      calc Pi.det * gm.det * P.det = gm.det * (Pi.det * P.det) := by ring
        _ = 1 := by rw [this, hdetg, mul_one]
    rw [e2] at e1
    exact Subtype.ext (by simpa using e1)
  have hYu : IsUnit Y.det := by rw [hdetY]; exact isUnit_one
  set YG : GL (Fin 4) h.fixedField := ⟨Y, Y⁻¹, Matrix.mul_nonsing_inv Y hYu,
    Matrix.nonsing_inv_mul Y hYu⟩ with hYG
  have hYGmem : YG ∈ iso1 h R := by
    refine Subgroup.mem_inf.2 ⟨(CatalogueBGraphForm.mem_isometryGroup _ _ _ _).2 hYR, ?_⟩
    rw [MonoidHom.mem_ker]
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact hdetY)
  refine ⟨⟨YG, hYGmem⟩, Subtype.ext (Units.ext ?_)⟩
  rw [coe_gHom]
  change P * Y.map h.fixedField.subtype * Pi = gm
  rw [hY, hX0]
  calc P * (Pi * gm * P) * Pi = (P * Pi) * gm * (P * Pi) := by simp only [Matrix.mul_assoc]
    _ = gm := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]

theorem kaU4G3_scalar_of_fmap {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    {M : Matrix (Fin 4) (Fin 4) h.fixedField} {c : K} (hc : c ≠ 0)
    (hM : M.map h.fixedField.subtype = c • 1) :
    ∃ μ : h.fixedFieldˣ, M = Matrix.scalar (Fin 4) (μ : h.fixedField) := by
  have hM' : ∀ i j, (M i j : K) = (c • (1 : Matrix (Fin 4) (Fin 4) K)) i j := fun i j =>
    congrFun (congrFun hM i) j
  have hdiag : ∀ i, (M i i : K) = c := fun i => by
    rw [hM' i i]
    simp
  have hoff : ∀ i j, i ≠ j → M i j = 0 := fun i j hij => by
    apply Subtype.ext
    rw [hM' i j]
    simp [Matrix.one_apply_ne hij]
  have h00 : M 0 0 ≠ 0 := fun e => hc (by rw [← hdiag 0, e]; rfl)
  refine ⟨Units.mk0 (M 0 0) h00, ?_⟩
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.val_mk0]
    exact (hdiag i).trans (hdiag 0).symm
  · rw [hoff i j hij, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem kaU4G3_split_of_model {p f : ℕ} {K : Type} [Field K] [Finite K]
    (h : UnitaryFieldData p f K) (hp3 : p ^ f = 3) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    (hs : s ≠ 0) {R : GL (Fin 4) h.fixedField}
    (hR : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {O : Type} [Group O] (θ : O →* GL (Fin 4) h.fixedField)
    (ρ : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →* O)
    (hθI : ∀ d, θ d ∈ CatalogueBGraphForm.isometryGroup 4 h.fixedField R)
    (hθS : ∀ X ∈ CatalogueBGraphForm.isometryGroup 4 h.fixedField R, ∃ d, θ d = X)
    (hsq : ∀ d : O, d * d ∈ ρ.range)
    (hker : ∀ (z : SpecialLinearGroup (Fin 2) h.fixedField ×
        SpecialLinearGroup (Fin 2) h.fixedField) (μ : h.fixedFieldˣ),
      θ (ρ z) = GeneralLinearGroup.scalar (Fin 4) μ →
        z.1 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) h.fixedField) ∧
        z.2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) h.fixedField)) :
    KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hF3 : Nat.card h.fixedField = 3 := by rw [h.card_fixedField, hp3]
  have : Finite h.fixedField := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
  have hq : ¬(4 = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
  have hnq : ((4 : ℕ), p ^ f) ≠ (3, 2) := fun e => by
    have := congrArg Prod.fst e
    simp at this
  have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hinj := ka_conj_inj_pu hK (by norm_num) hnq
  set G := gHom h hPPi hPiP hs hR with hG
  have hdet : ∀ z, ((θ (ρ z) : GL (Fin 4) h.fixedField) :
      Matrix (Fin 4) (Fin 4) h.fixedField).det = 1 := by
    intro z
    have e := congrArg Units.val
      (kaGO3S_hom_units_trivial hF3 (GeneralLinearGroup.det.comp (θ.comp ρ)) z)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using e
  let Ψ' : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →*
      iso1 h R := (θ.comp ρ).codRestrict (iso1 h R) fun z => Subgroup.mem_inf.2 ⟨hθI _, by
        rw [MonoidHom.mem_ker]
        exact Units.ext (by
          rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
          exact hdet z)⟩
  set β : SpecialLinearGroup (Fin 2) h.fixedField × SpecialLinearGroup (Fin 2) h.fixedField →*
      StatedProj (StatedSU 4 (p ^ f) K) := (projH (StatedSU 4 (p ^ f) K)).comp (G.comp Ψ')
    with hβ
  have hβz : ∀ z, β z = projH (StatedSU 4 (p ^ f) K) (G (Ψ' z)) := fun z => rfl
  refine ka_all_of_oddcore_triv hinj β.range ?_ (kaGO3S_gen hF3 β) ?_ ?_
    (fun q hq hq2 P hP hinn => kaU4S3_outTriv h hp3 q hq hq2 P hP hinn)
  ·
    rintro _ ⟨z, rfl⟩
    rw [mem_fixSub, hβz, uLift_proj h (by norm_num) A (barEq h)]
    rw [uLift_gHom h hPPi hPiP hs hR hb hbP]
  ·
    intro c hc hodd
    rw [mem_fixSub] at hc
    obtain ⟨g, rfl⟩ := projH_surjective c
    rw [uLift_proj h (by norm_num) A (barEq h)] at hc
    set φ := uLift h A (barEq h) with hφdef
    have hz0 : g⁻¹ * φ g ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) :=
      projH_eq_projH_iff.1 hc.symm
    have hz0c : g⁻¹ * φ g ∈ Subgroup.center (StatedSU 4 (p ^ f) K) :=
      scalars_subgroupOf_le_center hz0
    have hz04 : (g⁻¹ * φ g) ^ 4 = 1 := by
      obtain ⟨c0, hc0⟩ := hz0
      have hmat : (((g⁻¹ * φ g : StatedSU 4 (p ^ f) K) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) = (c0 : K) • 1 := by
        have e := congrArg (fun M : GL (Fin 4) K => (M : Matrix (Fin 4) (Fin 4) K)) hc0
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal] at e
        exact e.symm
      have hdetz : (c0 : K) ^ 4 = 1 := by
        have e := ((mem_unitarySU_iff h).1 (g⁻¹ * φ g).2).1
        rw [hmat, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at e
        exact e
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one, hmat,
        smul_pow, one_pow, hdetz, one_smul]
    obtain ⟨j, hj⟩ : ∃ j, 4 ∣ 1 + orderOf (projH (StatedSU 4 (p ^ f) K) g) * j := by
      obtain ⟨t, ht⟩ := hodd
      have h4 : orderOf (projH (StatedSU 4 (p ^ f) K) g) % 4 = 1 ∨
          orderOf (projH (StatedSU 4 (p ^ f) K) g) % 4 = 3 := by omega
      rcases h4 with h1 | h1
      · exact ⟨3, by omega⟩
      · exact ⟨1, by omega⟩
    have hφg' : φ (g ^ (1 + orderOf (projH (StatedSU 4 (p ^ f) K) g) * j)) =
        g ^ (1 + orderOf (projH (StatedSU 4 (p ^ f) K) g) * j) := by
      have e : φ g = g * (g⁻¹ * φ g) := by rw [mul_inv_cancel_left]
      have hcom : Commute g (g⁻¹ * φ g) := Subgroup.mem_center_iff.1 hz0c g
      obtain ⟨t, ht⟩ := hj
      rw [map_pow, e, hcom.mul_pow, ht, pow_mul (g⁻¹ * φ g), hz04, one_pow, mul_one]
    have hπg' : projH (StatedSU 4 (p ^ f) K)
        (g ^ (1 + orderOf (projH (StatedSU 4 (p ^ f) K) g) * j)) =
          projH (StatedSU 4 (p ^ f) K) g := by
      rw [map_pow, pow_add, pow_mul, pow_orderOf_eq_one, one_pow, mul_one, pow_one]
    obtain ⟨X, hX⟩ := kaU4G3_exists_of_fixed h hPPi hPiP hb hbP hs hR hφg'
    obtain ⟨d, hd⟩ := hθS _ (Subgroup.mem_inf.1 X.2).1
    obtain ⟨z, hz⟩ := hsq d
    have hXX : X * X = Ψ' z := Subtype.ext (by
      rw [Subgroup.coe_mul, ← hd, ← map_mul, ← hz]
      rfl)
    refine ka_odd_mem_of_sq_mem ⟨z, ?_⟩ hodd
    rw [hβz, ← hXX, map_mul, hX, map_mul, hπg']
  ·
    intro p' hp' hp2' X hXp hXR hXn
    have : Fact p'.Prime := ⟨hp'⟩
    have hodd : Odd (Nat.card X) := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hXp
      rw [hn]
      exact (hp'.odd_of_ne_two hp2').pow
    refine CFSG.ComponentClassification.CatFactsL4U4.eq_bot_of_odd_block
      ⟨3, 1, Nat.prime_three, by decide, le_refl 1, by rw [hF3]; norm_num⟩ β ?_ X hXR ?_ hodd
    · intro z hz
      have hz1 : projH (StatedSU 4 (p ^ f) K) (G (Ψ' z)) = 1 := by
        rw [← hβz]
        exact hz
      have h1 : G (Ψ' z) ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (p ^ f) K) :=
        (QuotientGroup.eq_one_iff (G (Ψ' z))).1 hz1
      obtain ⟨c0, hc0⟩ := h1
      have hmat : (((G (Ψ' z) : StatedSU 4 (p ^ f) K) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) = (c0 : K) • 1 := by
        have e := congrArg (fun M : GL (Fin 4) K => (M : Matrix (Fin 4) (Fin 4) K)) hc0
        simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          ← Matrix.smul_one_eq_diagonal] at e
        exact e.symm
      rw [coe_gHom] at hmat
      have hM : ((θ (ρ z) : GL (Fin 4) h.fixedField) :
          Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype = (c0 : K) • 1 := by
        change gTr h P Pi ((θ (ρ z) : GL (Fin 4) h.fixedField) :
          Matrix (Fin 4) (Fin 4) h.fixedField) = _ at hmat
        calc ((θ (ρ z) : GL (Fin 4) h.fixedField) :
              Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype
            = Pi * (P * ((θ (ρ z) : GL (Fin 4) h.fixedField) :
              Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype * Pi) * P := by
              simp only [Matrix.mul_assoc, hPiP, Matrix.mul_one]
              rw [← Matrix.mul_assoc Pi, hPiP, Matrix.one_mul]
          _ = (c0 : K) • 1 := by
              rw [show P * ((θ (ρ z) : GL (Fin 4) h.fixedField) :
                Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype * Pi =
                  (c0 : K) • 1 from hmat, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
                hPiP]
      obtain ⟨μ, hμ⟩ := kaU4G3_scalar_of_fmap h c0.ne_zero hM
      exact hker z μ (Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hμ))
    · intro g hg r hr
      exact (Subgroup.mem_normalizer_iff.1 (hXn g hg) r).1 hr

theorem kaU4G3_split {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K)
    (hp3 : p ^ f = 3) {A : uU h 4} {P Pi : Matrix (Fin 4) (Fin 4) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * P.map h.bar) = P) {s : K}
    (hs : s ≠ 0) {R : GL (Fin 4) h.fixedField}
    (hRs : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = R)
    (hR : ((R : GL (Fin 4) h.fixedField) : Matrix (Fin 4) (Fin 4) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    (hsp : ∃ S : Submodule h.fixedField (Fin 4 → h.fixedField),
      Module.finrank h.fixedField ↥S = 2 ∧ ∀ x ∈ S, matrixQuadraticForm R x = 0) :
    KAAll (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) (barEq h)) := by
  have hF3 : Nat.card h.fixedField = 3 := by rw [h.card_fixedField, hp3]
  have : Finite h.fixedField := Nat.finite_of_card_ne_zero (by rw [hF3]; norm_num)
  have hK : ringChar h.fixedField ≠ 2 := ka_ringChar_ne_two_of_card_three hF3
  obtain ⟨S, hS2, hS0⟩ := hsp
  obtain ⟨ψ, e, -, -, hψ⟩ := split_four_determinant_form_isometry (matrixQuadraticForm R)
    (polarBilin_matrixQuadraticForm_nondegenerate hK R hRs) (Module.finrank_fin_fun h.fixedField)
    S hS2 hS0
  refine kaU4G3_split_of_model h hp3 hPPi hPiP hb hbP hs hR (kaGO3STheta hK hRs e) specialRho
    (kaGO3STheta_mem hK hRs e) (fun X hX => kaGO3STheta_surj hK hRs e hX) (fun d => ?_)
    (fun z μ hz => ?_)
  · rw [← pow_two]
    exact LocalAnalysis.ComponentInitial.determinant_sq_mem_specialImage d
  · have hmul := fun v => kaGO3STheta_mulVec hK hRs e ψ hψ (specialRho z) v
    rw [hz] at hmul
    have hd : ∀ X : Matrix (Fin 2) (Fin 2) h.fixedField,
        (specialRho z).val X = (μ : h.fixedField) • X := by
      intro X
      apply ψ.symm.injective
      have h1 := hmul (ψ.symm X)
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [map_smul, ← h1]
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    exact kaGO3S_center_of_sandwich μ.ne_zero fun X => by rw [← specialRho_apply]; exact hd X

theorem kaU4GOrthThree_thm : KAU4GOrthThree := by
  intro p f K _ _ h hp2 hp3 A hA
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  set Am := ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with hAm
  have hU : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  have hAc : Am * Am.map h.bar = (1 : K) • 1 := hA
  obtain ⟨-, P, Pi, b, s, R, hPPi, hPiP, hb, hs, hbP, hR, hsym, -⟩ :=
    exists_graph_frame h hp2 (by norm_num) hU one_ne_zero hAc
  have hdetP : P.det ≠ 0 := by
    intro e
    have := congrArg Matrix.det hPPi
    rw [Matrix.det_mul, e, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdetPb : (P.map h.bar).det ≠ 0 := by
    have e := RingHom.map_det h.bar P
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]
    exact (map_ne_zero h.bar).2 hdetP
  have hdetR : R.det ≠ 0 := by
    intro e
    have e1 := congrArg Matrix.det hR
    have e2 := RingHom.map_det h.fixedField.subtype R
    rw [RingHom.mapMatrix_apply] at e2
    rw [← e2, e, map_zero, Matrix.det_smul, Matrix.det_mul, det_transpose] at e1
    exact mul_ne_zero (pow_ne_zero _ hs) (mul_ne_zero hdetPb hdetP) e1.symm
  set RG : GL (Fin 4) h.fixedField := Matrix.nonsingInvUnit R (isUnit_iff_ne_zero.2 hdetR)
    with hRGdef
  have hRsym : (RG : Matrix (Fin 4) (Fin 4) h.fixedField)ᵀ = RG := hsym rfl
  by_cases hsp : ∃ S : Submodule h.fixedField (Fin 4 → h.fixedField),
      Module.finrank h.fixedField ↥S = 2 ∧ ∀ x ∈ S, matrixQuadraticForm RG x = 0
  · exact kaU4G3_split h hp3 hPPi hPiP hb hbP hs hRsym hR hsp
  · exact kaU4G3_nonsplit h hp2 hp3 hPPi hPiP hb hbP hs hRsym hR hsp

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
