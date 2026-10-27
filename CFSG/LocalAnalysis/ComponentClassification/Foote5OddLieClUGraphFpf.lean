module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphThree
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL signMat signMat_mul_self
  pow_eight_eq_one_of_commute_sign eq_bot_of_four_group commute_signMat_iff isometrySL)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ClU.graph_three_fpf (hp3 : p ^ f = 3) (hn3 : 3 ≤ n) (hn4 : n ≤ 4)
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : ∀ i, w i ≠ 0)
    (hR : ((diagGL hw : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {i j : Fin n} (hij : i ≠ j) {x : MulAut (StatedProj (StatedSU n (p ^ f) K))}
    (hodd : Odd (orderOf x))
    (hxt : x * (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) * x)
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
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq x
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn3 hq (pow_orderOf_eq_one _)
  have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm fun c hc => by
    rcases mem_three_of_bar h hp3 hc with rfl | rfl | rfl <;> simp
  subst hτ1
  simp only [map_one, mul_one] at hodd hxt hxs ⊢
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
  obtain ⟨κ, hκ⟩ := exists_scalar_of_commute_graph h hn3 hxt
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
    rw [← hR, Burgoyne.PSL.coe_diagGL, diagonal_map (map_zero _)]
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

end CFSG.ComponentClassification.Foote5.OddLieCore
