module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphTools
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthData
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSplit

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL reflGL rotGL reflGL_mem rotGL_mem
  commutatorElement_reflGL_rotGL rotMat rotMat_neg_one_zero rotMat_apply_left signMat
  offDiag_eq_zero_of_commute_sign conj_apply_diag_of_offDiag orthComponentData
  det_eq_one_of_mem_commutator mem_of_mem_oddCoreIn)
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem conj_fmap_of_conj_gTr {P Pi : Matrix (Fin n) (Fin n) K} (hPiP : Pi * P = 1)
    {D Di : Matrix (Fin n) (Fin n) K} (τ : K ≃+* K)
    {X : Matrix (Fin n) (Fin n) h.fixedField}
    (e : D * (gTr h P Pi X).map τ * Di = gTr h P Pi X) :
    (Pi * D * P.map τ) * (X.map h.fixedField.subtype).map τ * (Pi.map τ * Di * P) =
      X.map h.fixedField.subtype := by
  rw [gTr, Matrix.map_mul, Matrix.map_mul] at e
  calc (Pi * D * P.map τ) * (X.map h.fixedField.subtype).map τ * (Pi.map τ * Di * P) =
      Pi * (D * (P.map τ * (X.map h.fixedField.subtype).map τ * Pi.map τ) * Di) * P := by
        simp only [Matrix.mul_assoc]
    _ = Pi * (P * X.map h.fixedField.subtype * Pi) * P := by rw [e]
    _ = (Pi * P) * X.map h.fixedField.subtype * (Pi * P) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hPiP, Matrix.one_mul, Matrix.mul_one]

theorem graphOrth_oddCoreIn_eq_bot (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : OrthNF w)
    (hR : ((diagGL hw.1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    (hexc : ¬ (p ^ f = 3 ∧ n ≤ 4)) :
    oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) = ⊥ := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have h2K : (2 : K) ≠ 0 := by
    intro e
    have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
    rw [CharP.cast_eq_zero_iff K p] at e'
    have := Nat.le_of_dvd (by norm_num) e'
    have := h.prime.two_le
    exact hp2 (by omega)
  have h2F : (2 : h.fixedField) ≠ 0 := fun e => h2K (by
    have h1 : ((1 + 1 : h.fixedField) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
    rw [← one_add_one_eq_two] at e ⊢
    rw [← h1, e, Subfield.coe_zero])
  have hF2 : ringChar h.fixedField ≠ 2 := fun e => h2F (by
    have := ringChar.spec h.fixedField 2
    exact_mod_cast (this.2 (by rw [e])))
  obtain ⟨I, hI3, hIc, hIw⟩ := hw.2
  set R := diagGL hw.1 with hRdef
  have hRsym : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ = R := diagonal_transpose _
  have hexcF : ¬ (Nat.card h.fixedField = 3 ∧ n ≤ 4) := by rwa [h.card_fixedField]
  obtain ⟨hperf, m, L, hsup, hL⟩ := orthComponentData hF2 hn R hRsym hexcF
  set Iso := CatalogueBGraphForm.isometryGroup n h.fixedField R with hIso
  have hcle : ⁅Iso, Iso⁆ ≤ Iso := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hΩ1 : ⁅Iso, Iso⁆ ≤ iso1 h R := by
    intro X hX
    refine Subgroup.mem_inf.2 ⟨hcle hX, ?_⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_eq_one_of_mem_commutator hX
  have hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) →
          ∀ X ∈ ⁅Iso, Iso⁆, Y * X * Y⁻¹ ∈ ⁅Iso, Iso⁆ :=
    fun Y μ hμ hY X hX => conj_mem_commutator_isometryGroup_of_similitude hY hμ hX
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hyBC := mem_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq y
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
  have hfixΩ := fun (X : iso1 h R) (hX : (X : GL (Fin n) h.fixedField) ∈ ⁅Iso, Iso⁆) =>
    graph_fix_of_components h hn hinj hB hPPi hPiP hs hR hb hbP hΩ1 hΩ hperf hsup hL hy hX
  set Dm := ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDm
  set Dmi := (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDmi
  have hDD : Dm * Dmi = 1 := by rw [hDm, hDmi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set D' := Pi * Dm * P.map τ with hD'
  set D'i := Pi.map τ * Dmi * P with hD'i
  have hD'D'i : D' * D'i = 1 := by
    have e1 : P.map τ * Pi.map τ = 1 := by
      rw [← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero τ) (map_one τ)]
    calc D' * D'i = Pi * Dm * (P.map τ * Pi.map τ) * Dmi * P := by
          simp only [hD', hD'i, Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, Matrix.mul_assoc Pi, hDD, Matrix.mul_one, hPiP]
  have hX' : ∀ X ∈ ⁅Iso, Iso⁆, D' * ((X : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype).map τ * D'i = (X : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype := by
    intro X hX
    have e := hfixΩ ⟨X, hΩ1 hX⟩ hX
    rw [coe_gHom] at e
    exact conj_fmap_of_conj_gTr h hPiP τ e
  have hD'iD' : D'i * D' = 1 := mul_eq_one_comm.1 hD'D'i
  set D'G : GL (Fin n) K := ⟨D', D'i, hD'D'i, hD'iD'⟩ with hD'G
  have hG : ∀ {i j : Fin n} (hi : i ∈ I) (hj : j ∈ I) (hij : i ≠ j) {a c : h.fixedField}
      (hac : a ^ 2 + c ^ 2 = 1), ⁅reflGL (K := h.fixedField) i, rotGL i j hij hac⁆ ∈
        ⁅Iso, Iso⁆ :=
    fun hi hj hij _ _ hac => commutator_mem_commutator (reflGL_mem hw.1 _)
      (rotGL_mem hw.1 hij (hIw _ hi _ hj) hac)
  have hsign : ∀ J : Finset (Fin n),
      ((signMat h.fixedField J).map h.fixedField.subtype).map τ = signMat K J := by
    intro J
    ext x y
    simp only [signMat, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hsign' : ∀ J : Finset (Fin n),
      (signMat h.fixedField J).map h.fixedField.subtype = signMat K J := by
    intro J
    ext x y
    simp only [signMat, map_apply, diagonal_apply]
    split_ifs <;> simp
  have hS : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D' * signMat K {i, j} = signMat K {i, j} * D' := by
    intro i hi j hj hij
    have hab : (0 : h.fixedField) ^ 2 + 1 ^ 2 = 1 := by ring
    have e := hX' _ (hG hi hj hij hab)
    rw [commutatorElement_reflGL_rotGL, show (0 : h.fixedField) ^ 2 - 1 ^ 2 = -1 by ring,
      show -(2 * (0 : h.fixedField) * 1) = 0 by ring, rotMat_neg_one_zero hij, hsign,
      hsign'] at e
    calc D' * signMat K {i, j} = D' * signMat K {i, j} * (D'i * D') := by
          rw [hD'iD', Matrix.mul_one]
      _ = signMat K {i, j} * D' := by rw [← Matrix.mul_assoc, e]
  have hdiag := offDiag_eq_zero_of_commute_sign h2K hI3 hIc hS
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ I, ∃ j ∈ I, i ≠ j := Finset.one_lt_card.1 (by omega)
  have hcirc : ∀ a c : h.fixedField, a ^ 2 + c ^ 2 = 1 → τ (a : K) = a := by
    intro a c hac
    set Mx := ((⁅reflGL (K := h.fixedField) i, rotGL i j hij hac⁆ : GL (Fin n) h.fixedField) :
      Matrix (Fin n) (Fin n) h.fixedField) with hMx
    have e : D' * (Mx.map h.fixedField.subtype).map τ * D'i = Mx.map h.fixedField.subtype :=
      hX' _ (hG hi hj hij hac)
    have e2 := conj_apply_diag_of_offDiag (D := D'G) hdiag
      ((Mx.map h.fixedField.subtype).map τ) i
    change (D' * (Mx.map h.fixedField.subtype).map τ * D'i) i i = _ at e2
    rw [e] at e2
    have hMii : Mx i i = a ^ 2 - c ^ 2 := by
      rw [hMx, commutatorElement_reflGL_rotGL, rotMat_apply_left hij]
    simp only [map_apply, hMii] at e2
    have hc2 : c ^ 2 = 1 - a ^ 2 := by linear_combination hac
    rw [hc2] at e2
    simp only [map_sub, map_pow, map_one, Subfield.subtype_apply] at e2
    have hτa2 : τ (a : K) ^ 2 = (a : K) ^ 2 := by
      have : (2 : K) * (τ (a : K) ^ 2 - (a : K) ^ 2) = 0 := by linear_combination -e2
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left h2K)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hτa2 with e3 | e3
    · exact e3
    · have hpow : ∀ k : ℕ, (τ ^ k) (a : K) = (-1) ^ k * a := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ]
          change (τ ^ k) (τ (a : K)) = _
          rw [e3, map_neg, ih, pow_succ]
          ring
      have := hpow (orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ))
      rw [hτm, hodd.neg_one_pow] at this
      change (a : K) = -1 * a at this
      have ha0 : (a : K) = 0 := by
        have : (2 : K) * a = 0 := by linear_combination this
        exact (mul_eq_zero.1 this).resolve_left h2K
      rw [e3, ha0, neg_zero]
  have hτF := fix_fixedField_of_fix_circle h hp2 hcirc
  have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm fun c hc => hτF ⟨c, hc⟩
  subst hτ1
  simp only [map_one, mul_one] at hodd hyBC ⊢
  have hD'1 : D' = Pi * Dm * P := by rw [hD', map_one_ringEquiv]
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  obtain ⟨κ, hκ⟩ := exists_scalar_of_commute_graph h hn (mem_centralizer_singleton_iff.1 hyBC.2)
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
  have hκ0 : (κ : K) ≠ 0 := κ.ne_zero
  have hD'bar : D' = (κ : K) • D'.map h.bar := by
    have hADm : Am * Dm.map h.bar = (κ : K)⁻¹ • (Dm * Am) := by
      rw [hκ, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
    rw [hD'1, Matrix.map_mul, Matrix.map_mul, hPbi]
    calc Pi * Dm * P = (κ : K) • ((b * (κ : K)⁻¹) • (Pi * Dm * (Am * P.map h.bar))) := by
          rw [hAP, Matrix.mul_smul, smul_smul, smul_smul,
            show (κ : K) * (b * (κ : K)⁻¹) * b⁻¹ = 1 by field_simp, one_smul]
      _ = (κ : K) • (b • (Pi * Am) * Dm.map h.bar * P.map h.bar) := by
          congr 1
          rw [Matrix.smul_mul, Matrix.smul_mul, mul_smul, Matrix.mul_assoc Pi Am, hADm]
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hDmU : (Dm.map h.bar)ᵀ * Dm = 1 := (mem_uU h).1 D.2
  have hPD : P * D' = Dm * P := by
    rw [hD'1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPi, Matrix.one_mul]
  have hG₀ : (D'.map h.bar)ᵀ * ((P.map h.bar)ᵀ * P) * D' = (P.map h.bar)ᵀ * P := by
    have hPbT : (Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ = 1 := by
      rw [← transpose_mul, hPb, transpose_one]
    rw [hD'1, conjT_mul h, conjT_mul h]
    calc (P.map h.bar)ᵀ * ((Dm.map h.bar)ᵀ * (Pi.map h.bar)ᵀ) * ((P.map h.bar)ᵀ * P) *
          (Pi * Dm * P) =
        (P.map h.bar)ᵀ * (Dm.map h.bar)ᵀ * ((Pi.map h.bar)ᵀ * (P.map h.bar)ᵀ) * (P * Pi) *
          Dm * P := by simp only [Matrix.mul_assoc]
      _ = (P.map h.bar)ᵀ * P := by
          rw [hPbT, hPPi, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc _ _ Dm, hDmU,
            Matrix.mul_one]
  have hPP : (P.map h.bar)ᵀ * P = s⁻¹ • diagonal fun x => (w x : K) := by
    have e := hR
    rw [hRdef, PSL.coe_diagGL, diagonal_map (map_zero _)] at e
    rw [show (diagonal fun x => (w x : K)) =
      diagonal fun m => h.fixedField.subtype (w m) from rfl, e, smul_smul, inv_mul_cancel₀ hs,
      one_smul]
  set d : Fin n → K := fun x => D' x x with hd
  have hDd : D' = diagonal d := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      rw [diagonal_apply_eq]
    · rw [hdiag x y hxy, diagonal_apply_ne _ hxy]
  have hN : ∀ x, h.bar (d x) * d x = 1 := by
    intro x
    have e := congrFun (congrFun hG₀ x) x
    rw [hPP, hDd, diagonal_map (map_zero _), diagonal_transpose, Matrix.mul_smul,
      Matrix.smul_mul, diagonal_mul_diagonal, diagonal_mul_diagonal, Matrix.smul_apply,
      Matrix.smul_apply, diagonal_apply_eq, diagonal_apply_eq, smul_eq_mul, smul_eq_mul] at e
    have hw0 : (w x : K) ≠ 0 := fun e0 => hw.1 x (Subtype.ext e0)
    have : s⁻¹ * (w x : K) * (h.bar (d x) * d x - 1) = 0 := by linear_combination e
    rcases mul_eq_zero.1 this with e1 | e1
    · exact absurd e1 (mul_ne_zero (inv_ne_zero hs) hw0)
    · exact sub_eq_zero.1 e1
  have hsq : ∀ x, d x * d x = κ := by
    intro x
    have e := congrFun (congrFun hD'bar x) x
    rw [hDd] at e
    simp only [Matrix.smul_apply, map_apply, diagonal_apply_eq, smul_eq_mul] at e
    calc d x * d x = (κ : K) * h.bar (d x) * d x := by rw [← e]
      _ = κ := by rw [mul_assoc, hN, mul_one]
  have hD2 : uConjAut h (by omega) (D * D) = 1 := by
    refine (uConjAut_eq_one_iff h hn _).2 ⟨κ, Units.ext ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
    change Dm * Dm = _
    have hDmP : Dm = P * D' * Pi := by
      rw [hD'1]
      calc Dm = (P * Pi) * Dm * (P * Pi) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]
    have hD'2 : D' * D' = (κ : K) • 1 := by
      rw [hDd, diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
      congr 1
      ext x
      exact hsq x
    rw [hDmP]
    calc P * D' * Pi * (P * D' * Pi) = P * (D' * D') * Pi := by
          rw [show P * D' * Pi * (P * D' * Pi) = P * D' * (Pi * P) * D' * Pi by
            simp only [Matrix.mul_assoc], hPiP, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hD'2, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPPi,
            Matrix.smul_one_eq_diagonal]
          rfl
  rw [map_mul] at hD2
  have h2 : orderOf (uConjAut h (by omega) D) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hD2)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with e | e
  · exact orderOf_eq_one_iff.1 e
  · rw [e] at hodd
    exact absurd hodd (by decide)

end CFSG.ComponentClassification.Burgoyne.U
