module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthThree
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphHom
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUThree

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL signMat signMat_mul_self
  pow_eight_eq_one_of_commute_sign eq_bot_of_four_group conj_mem_oddCoreIn
  mem_of_mem_oddCoreIn commute_signMat_iff)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem graph_prime_props {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1)
    (hPiP : Pi * P = 1) {Am : Matrix (Fin n) (Fin n) K} {b : K} (hb : b ≠ 0)
    (hbP : b • (Am * P.map h.bar) = P) {Dm : Matrix (Fin n) (Fin n) K}
    (hDmU : (Dm.map h.bar)ᵀ * Dm = 1) {κ : K} (hκ0 : κ ≠ 0)
    (hκ : Dm * Am = κ • (Am * Dm.map h.bar)) :
    Pi * Dm * P = κ • (Pi * Dm * P).map h.bar ∧
      ((Pi * Dm * P).map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * (Pi * Dm * P) =
        (P.map h.bar)ᵀ * P := by
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
  refine ⟨?_, ?_⟩
  · have hADm : Am * Dm.map h.bar = κ⁻¹ • (Dm * Am) := by
      rw [hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    rw [Matrix.map_mul, Matrix.map_mul, hPbi]
    calc Pi * Dm * P = κ • ((b * κ⁻¹) • (Pi * Dm * (Am * P.map h.bar))) := by
          rw [hAP, Matrix.mul_smul, smul_smul, smul_smul,
            show κ * (b * κ⁻¹) * b⁻¹ = 1 by field_simp, one_smul]
      _ = κ • (b • (Pi * Am) * Dm.map h.bar * P.map h.bar) := by
          congr 1
          rw [Matrix.smul_mul, Matrix.smul_mul, mul_smul, Matrix.mul_assoc Pi Am, hADm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · have hPbT : (Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, hPb, transpose_one]
    rw [conjT_mul h, conjT_mul h]
    calc (P.map h.bar)ᵀ * ((Dm.map h.bar)ᵀ * (Pi.map h.bar)ᵀ) * ((P.map h.bar)ᵀ * P) *
          (Pi * Dm * P) =
        (P.map h.bar)ᵀ * (Dm.map h.bar)ᵀ * ((Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ) * (P * Pi) *
          Dm * P := by simp only [Matrix.mul_assoc]
      _ = (P.map h.bar)ᵀ * P := by
          rw [hPbT, hPPi, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc _ _ Dm, hDmU,
            Matrix.mul_one]

theorem uConjAut_of_mem_SU (hn : 1 ≤ n) (g : StatedSU n (p ^ f) K) :
    uConjAut h hn ⟨(g : GL (Fin n) K), statedSU_le_uU h g.2⟩ =
      conjProjH (StatedSU n (p ^ f) K) g := by
  ext x
  obtain ⟨y, rfl⟩ := projH_surjective x
  rw [uConjAut_proj]
  change projH _ _ = projH _ g * projH _ y * (projH _ g)⁻¹
  rw [← map_mul, ← map_inv, ← map_mul]
  rfl

@[expose] def signIso {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin n))
    (hJ : Even J.card) : iso1 h (diagGL hw) :=
  ⟨⟨signMat h.fixedField J, signMat h.fixedField J, signMat_mul_self J, signMat_mul_self J⟩,
    Subgroup.mem_inf.2 ⟨by
      rw [CatalogueBGraphForm.mem_isometryGroup]
      change (signMat h.fixedField J)ᵀ * diagonal w * signMat h.fixedField J = diagonal w
      rw [signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      ext x
      split_ifs <;> simp, by
      rw [MonoidHom.mem_ker]
      refine Units.ext ?_
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      change (signMat h.fixedField J).det = 1
      rw [PSL.det_signMat, hJ.neg_one_pow]⟩⟩

theorem coe_signIso {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0) (J : Finset (Fin n))
    (hJ : Even J.card) :
    (((signIso h hw J hJ : iso1 h (diagGL hw)) : GL (Fin n) h.fixedField) :
      Matrix (Fin n) (Fin n) h.fixedField) = signMat h.fixedField J := rfl

theorem graph_three_fpf (hp3 : p ^ f = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0)
    (hR : ((diagGL hw : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {i j : Fin n} (hij : i ≠ j) {x : MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hx : x ∈ oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)))
    (hxs : conjProjH (StatedSU n (p ^ f) K) (gHom h hPPi hPiP hs hR
      (signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two))) * x =
      x * conjProjH (StatedSU n (p ^ f) K) (gHom h hPPi hPiP hs hR
        (signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two)))) :
    x = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by omega
  have hp3' : p = 3 :=
    (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_three).1
      (by rw [← hp3]; exact dvd_pow_self p (by have := h.one_le; omega))
  have h3K : (3 : K) = 0 := by
    have := CharP.cast_eq_zero K p
    rw [hp3'] at this
    exact_mod_cast this
  have h2K : (2 : K) ≠ 0 := by
    intro e
    have : (1 : K) = 0 := by linear_combination h3K - e
    exact one_ne_zero this
  have hodd := odd_orderOf_of_mem_oddCoreIn hx
  have hxBC := mem_of_mem_oddCoreIn hx
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq x
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn3 hq (pow_orderOf_eq_one _)
  have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm fun c hc => by
    rcases mem_three_of_bar h hp3 hc with rfl | rfl | rfl <;> simp
  subst hτ1
  simp only [map_one, mul_one] at hodd hxBC hxs ⊢
  set g := gHom h hPPi hPiP hs hR
    (signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two)) with hg
  set g' : uU h n := ⟨(g : GL (Fin n) K), statedSU_le_uU h g.2⟩ with hg'
  have hgg : g' * g' = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one]
    change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, ← map_mul]
    have : signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two) *
        signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two) = 1 :=
      Subtype.ext (Units.ext (signMat_mul_self _))
    rw [this, map_one]
    rfl
  have hcg : uConjAut h (by omega) g' = conjProjH (StatedSU n (p ^ f) K) g :=
    uConjAut_of_mem_SU h (by omega) g
  have hDg : D * g' = g' * D := uCommute_of_odd h hn3 (by rw [hgg, map_one]) hodd
    (by rw [hcg]; exact hxs.symm)
  set Dm := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDm
  have hDmU : (Dm.map h.bar)ᵀ * Dm = 1 := (mem_uU h).1 D.2
  obtain ⟨κ, hκ⟩ := exists_scalar_of_commute_graph h hn3 (mem_centralizer_singleton_iff.1 hxBC.2)
  obtain ⟨hD'bar, hD'U⟩ := graph_prime_props h hPPi hPiP hb hbP hDmU κ.ne_zero hκ
  set D' := Pi * Dm * P with hD'
  have hsignK : (signMat h.fixedField {i, j}).map h.fixedField.subtype = signMat K {i, j} := by
    ext x y
    simp only [signMat, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hgm : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = P * signMat K {i, j} * Pi := by
    rw [hg, coe_gHom, coe_signIso, gTr, hsignK]
  have hD'S : D' * signMat K {i, j} = signMat K {i, j} * D' := by
    have e := congrArg (fun x : uU h n => ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hDg
    simp only [Subgroup.coe_mul, Units.val_mul] at e
    change Dm * ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Dm at e
    rw [hgm] at e
    have hPiP' : ∀ M : Matrix (Fin n) (Fin n) K, Pi * (P * M) = M := fun M => by
      rw [← Matrix.mul_assoc, hPiP, Matrix.one_mul]
    calc D' * signMat K {i, j} = Pi * (Dm * (P * signMat K {i, j} * Pi)) * P := by
          rw [hD']; simp only [Matrix.mul_assoc, hPiP, Matrix.mul_one]
      _ = Pi * ((P * signMat K {i, j} * Pi) * Dm) * P := by rw [e]
      _ = signMat K {i, j} * D' := by
          rw [hD']; simp only [Matrix.mul_assoc, hPiP']
  have hD'ne : D' ≠ 0 := by
    intro e0
    have : P * D' * Pi = Dm := by
      rw [hD']
      calc P * (Pi * Dm * P) * Pi = (P * Pi) * Dm * (P * Pi) := by simp only [Matrix.mul_assoc]
        _ = Dm := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
    rw [e0, Matrix.mul_zero, Matrix.zero_mul] at this
    have h1 := hDmU
    rw [← this, Matrix.mul_zero] at h1
    have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  have hbarD' : D'.map h.bar = h.bar (κ : K) • D' := by
    have e1 : D'.map h.bar = ((κ : K) • D'.map h.bar).map h.bar :=
      congrArg (fun M => M.map h.bar) hD'bar
    rw [show ((κ : K) • D'.map h.bar).map h.bar = h.bar (κ : K) • (D'.map h.bar).map h.bar by
      ext x y; simp [map_mul]] at e1
    rw [e1]
    congr 1
    ext x y
    simp [h.bar_bar]
  have hκN : h.norm (κ : K) = 1 := by
    have e1 : D' = ((κ : K) * h.bar (κ : K)) • D' := by
      rw [← smul_smul, ← hbarD']
      exact hD'bar
    have e2 : (1 - (κ : K) * h.bar (κ : K)) • D' = 0 := by
      rw [sub_smul, one_smul, ← e1, sub_self]
    rcases smul_eq_zero.1 e2 with e3 | e3
    · rw [UnitaryFieldData.norm]
      linear_combination -e3
    · exact absurd e3 hD'ne
  obtain ⟨r, hr0, hr⟩ := h.exists_div_bar_eq hκN
  have hbr0 : h.bar r ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hfix : (h.bar r • D').map h.bar = h.bar r • D' := by
    rw [show (h.bar r • D').map h.bar = h.bar (h.bar r) • D'.map h.bar by ext x y; simp [map_mul],
      h.bar_bar, hbarD', smul_smul]
    congr 1
    rw [← hr, map_div₀, h.bar_bar]
    field_simp
  obtain ⟨D₀, hD₀⟩ := exists_fmap_of_bar h hfix
  have hsmul_map : ∀ (c : K) (M : Matrix (Fin n) (Fin n) K), (c • M).map h.bar =
      h.bar c • M.map h.bar := fun c M => by ext x y; simp [map_mul]
  have hD₀bar : D₀.map h.fixedField.subtype = r • D'.map h.bar := by
    rw [hD₀, ← hfix, hsmul_map, h.bar_bar]
  have hNr : h.norm r ∈ h.fixedField := h.norm_mem_fixedField r
  set μ : h.fixedField := ⟨h.norm r, hNr⟩ with hμ
  have hμ0 : μ ≠ 0 := by
    intro e
    have := congrArg Subtype.val e
    simp only [hμ, ZeroMemClass.coe_zero] at this
    rw [UnitaryFieldData.norm] at this
    exact mul_ne_zero hr0 hbr0 this
  have hRw : (diagonal fun x => (w x : K)) = s • ((P.map h.bar)ᵀ * P) := by
    rw [← hR, PSL.coe_diagGL, diagonal_map (map_zero _)]
    rfl
  have hfsmul : ∀ (c : h.fixedField) (M : Matrix (Fin n) (Fin n) h.fixedField),
      (c • M).map h.fixedField.subtype = (c : K) • M.map h.fixedField.subtype := fun c M => by
    ext x y
    simp
  have hsim : D₀ᵀ * diagonal w * D₀ = μ • diagonal w := by
    apply fmap_injective h
    simp only [Matrix.map_mul, transpose_map, hfsmul, diagonal_map (map_zero _)]
    change (D₀.map h.fixedField.subtype)ᵀ * (diagonal fun x => (w x : K)) *
      D₀.map h.fixedField.subtype = (μ : K) • diagonal fun x => (w x : K)
    rw [hRw]
    nth_rewrite 1 [hD₀bar]
    rw [hD₀]
    simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [show (D'.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * D' = (P.map h.bar)ᵀ * P from hD'U]
    simp only [hμ, UnitaryFieldData.norm]
    congr 1
    ring
  have hcommF : D₀ * signMat h.fixedField {i, j} = signMat h.fixedField {i, j} * D₀ := by
    apply fmap_injective h
    simp only [Matrix.map_mul, hsignK]
    rw [hD₀, Matrix.smul_mul, Matrix.mul_smul, hD'S]
  have h3F : Nat.card h.fixedField = 3 := by rw [h.card_fixedField, hp3]
  have hsim' : D₀ᵀ * diagonal w * D₀ᵀᵀ = diagonal fun x => μ * w x := by
    rw [transpose_transpose, hsim, ← diagonal_smul]
    rfl
  have hcomm' : D₀ᵀ * signMat h.fixedField {i, j} = signMat h.fixedField {i, j} * D₀ᵀ := by
    have e := congrArg transpose hcommF
    rw [transpose_mul, transpose_mul] at e
    have hS : (signMat h.fixedField {i, j})ᵀ = signMat h.fixedField {i, j} :=
      diagonal_transpose _
    rw [hS] at e
    exact e.symm
  have h8 := pow_eight_eq_one_of_commute_sign h3F hn3 hn4 hw hμ0 hsim' hij hcomm'
  have hD08 : D₀ ^ 8 = 1 := by
    have := congrArg transpose h8
    rwa [← transpose_pow, transpose_transpose, transpose_one] at this
  have hD'8 : D' ^ 8 = (h.bar r)⁻¹ ^ 8 • 1 := by
    have e : (D₀.map h.fixedField.subtype) ^ 8 = 1 := by
      rw [← Matrix.map_pow, hD08, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hD₀, smul_pow] at e
    calc D' ^ 8 = ((h.bar r)⁻¹ ^ 8 * h.bar r ^ 8) • D' ^ 8 := by
          rw [← mul_pow, inv_mul_cancel₀ hbr0, one_pow, one_smul]
      _ = _ := by rw [mul_smul, e]
  have hconjpow : ∀ k : ℕ, (P * D' * Pi) ^ k = P * D' ^ k * Pi := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hPPi]
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc P * D' ^ k * Pi * (P * D' * Pi) = P * D' ^ k * (Pi * P) * D' * Pi := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hPiP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hDmP : Dm = P * D' * Pi := by
    rw [hD']
    calc Dm = (P * Pi) * Dm * (P * Pi) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hc0 : (h.bar r)⁻¹ ^ 8 ≠ 0 := pow_ne_zero 8 (inv_ne_zero hbr0)
  have hD8 : uConjAut h (by omega) (D ^ 8) = 1 := by
    refine (uConjAut_eq_one_iff h hn3 _).2 ⟨Units.mk0 _ hc0, Units.ext ?_⟩
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, GeneralLinearGroup.coe_scalar]
    change Dm ^ 8 = _
    rw [hDmP, hconjpow, hD'8, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPPi,
      Matrix.smul_one_eq_diagonal]
    rfl
  rw [map_pow] at hD8
  have hdvd := orderOf_dvd_of_pow_eq_one hD8
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  obtain ⟨k, hk⟩ := hodd
  have h3' : orderOf (uConjAut h (by omega) D) ≠ 3 := fun e3 => by
    rw [e3] at hdvd
    norm_num at hdvd
  have h5' : orderOf (uConjAut h (by omega) D) ≠ 5 := fun e5 => by
    rw [e5] at hdvd
    norm_num at hdvd
  have h7' : orderOf (uConjAut h (by omega) D) ≠ 7 := fun e7 => by
    rw [e7] at hdvd
    norm_num at hdvd
  exact orderOf_eq_one_iff.1 (by omega)

@[expose] def signConj {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1)
    (hPiP : Pi * P = 1) {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0)
    (hR : ((diagGL hw : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {i j : Fin n} (hij : i ≠ j) : MulAut (StatedProj (StatedSU n (p ^ f) K)) :=
  conjProjH (StatedSU n (p ^ f) K) (gHom h hPPi hPiP hs hR
    (signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two)))

theorem graphOrth_oddCoreIn_eq_bot_three (hp3 : p ^ f = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0)
    (hR : ((diagGL hw : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P)) :
    oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) = ⊥ := by
  have := h.finite
  have : Finite (oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h))) :=
    inferInstance
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp
  have hmemC : ∀ {i j : Fin n} (hij : i ≠ j), signConj h hPPi hPiP hs hw hR hij ∈
      B ⊓ centralizer ({uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)} :
        Set (MulAut (StatedProj (StatedSU n (p ^ f) K)))) := by
    intro i j hij
    refine Subgroup.mem_inf.2 ⟨hB ⟨_, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have hfix := uLift_gHom h hPPi hPiP hs hR hb hbP
      (signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two))
    have key : (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) *
        signConj h hPPi hPiP hs hw hR hij *
        (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h))⁻¹ =
          signConj h hPPi hPiP hs hw hR hij := by
      rw [signConj, MonoidHom.comp_apply, PSL.mul_conj_mul_inv, uLift_proj h (by omega) A,
        hfix]
    exact (mul_inv_eq_iff_eq_mul.1 key).symm
  have hsq : ∀ {i j : Fin n} (hij : i ≠ j),
      signConj h hPPi hPiP hs hw hR hij * signConj h hPPi hPiP hs hw hR hij = 1 := by
    intro i j hij
    rw [signConj, ← map_mul, ← map_mul]
    have : signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two) *
        signIso h hw {i, j} (by rw [Finset.card_pair hij]; exact even_two) = 1 :=
      Subtype.ext (Units.ext (signMat_mul_self _))
    rw [this, map_one, map_one]
  have hprod : signConj h hPPi hPiP hs hw hR h01 * signConj h hPPi hPiP hs hw hR h02 =
      signConj h hPPi hPiP hs hw hR h12 := by
    rw [signConj, signConj, signConj, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    apply Units.ext
    change signMat h.fixedField {⟨0, by omega⟩, ⟨1, by omega⟩} *
        signMat h.fixedField {⟨0, by omega⟩, ⟨2, by omega⟩} =
      signMat h.fixedField {⟨1, by omega⟩, ⟨2, by omega⟩}
    rw [signMat, signMat, signMat, diagonal_mul_diagonal]
    congr 1
    ext x
    by_cases hx0 : x = ⟨0, by omega⟩
    · subst hx0
      simp [h01, h02]
    by_cases hx1 : x = ⟨1, by omega⟩
    · subst hx1
      simp [h12, Ne.symm h01]
    by_cases hx2 : x = ⟨2, by omega⟩
    · subst hx2
      simp [Ne.symm h12, Ne.symm h02]
    simp [hx0, hx1, hx2]
  have hfpf : ∀ {i j : Fin n} (hij : i ≠ j), ∀ x ∈ oddCoreIn B
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)),
      signConj h hPPi hPiP hs hw hR hij * x = x * signConj h hPPi hPiP hs hw hR hij → x = 1 :=
    fun hij x hx hc => graph_three_fpf h hp3 hn3 hn4 hPPi hPiP hb hbP hs hw hR hij hx hc
  refine eq_bot_of_four_group (hsq h01) (hsq h02)
    (fun x hx => conj_mem_oddCoreIn hx (hmemC h01))
    (fun x hx => conj_mem_oddCoreIn hx (hmemC h02)) (hfpf h01) (hfpf h02) ?_
  rw [hprod]
  exact hfpf h12

end CFSG.ComponentClassification.Burgoyne.U
