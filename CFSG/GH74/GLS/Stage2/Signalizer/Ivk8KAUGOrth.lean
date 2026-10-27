module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphOrth
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.ComponentClassification.Burgoyne
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (OrthNF diagGL reflGL rotGL reflGL_mem rotGL_mem
  commutatorElement_reflGL_rotGL rotMat_neg_one_zero rotMat_apply_left signMat
  offDiag_eq_zero_of_commute_sign conj_apply_diag_of_offDiag orthComponentData
  det_eq_one_of_mem_commutator)
open scoped commutatorElement

section Rigid

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

include h in
theorem kaUGOrth_two_ne (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

theorem kaUGOrth_ringChar (hp2 : p ≠ 2) : ringChar h.fixedField ≠ 2 := by
  have h2K := kaUGOrth_two_ne h hp2
  have h2F : (2 : h.fixedField) ≠ 0 := fun e => h2K (by
    have h1 : ((1 + 1 : h.fixedField) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
    rw [← one_add_one_eq_two] at e ⊢
    rw [← h1, e, Subfield.coe_zero])
  exact fun e => h2F (by
    have := ringChar.spec h.fixedField 2
    exact_mod_cast (this.2 (by rw [e])))

theorem kaUGOrth_trivial (hp2 : p ≠ 2) (hn : 3 ≤ n) {A : uU h n}
    {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : OrthNF w)
    (hR : ((diagGL hw.1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P))
    {D : uU h n} {τ : K ≃+* K}
    (hodd : Odd (orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ)))
    (hc : (uConjAut h (by omega) D * uFieldAut h (by omega) τ) *
        (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) =
      (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) *
        (uConjAut h (by omega) D * uFieldAut h (by omega) τ))
    (hfixΩ : ∀ X ∈ ⁅CatalogueBGraphForm.isometryGroup n h.fixedField (diagGL hw.1),
        CatalogueBGraphForm.isometryGroup n h.fixedField (diagGL hw.1)⁆,
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (gTr h P Pi ((X : GL (Fin n) h.fixedField) :
          Matrix (Fin n) (Fin n) h.fixedField)).map τ *
        (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      gTr h P Pi ((X : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)) :
    uConjAut h (by omega) D * uFieldAut h (by omega) τ = 1 := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have h2K := kaUGOrth_two_ne h hp2
  obtain ⟨I, hI3, hIc, hIw⟩ := hw.2
  set Iso := CatalogueBGraphForm.isometryGroup n h.fixedField (diagGL hw.1) with hIso
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn hq (pow_orderOf_eq_one _)
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
        h.fixedField.subtype := fun X hX => conj_fmap_of_conj_gTr h hPiP τ (hfixΩ X hX)
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
  simp only [map_one, mul_one] at hodd hc ⊢
  have hD'1 : D' = Pi * Dm * P := by rw [hD', map_one_ringEquiv]
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  obtain ⟨κ, hκ⟩ := exists_scalar_of_commute_graph h hn hc
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
    rw [PSL.coe_diagGL, diagonal_map (map_zero _)] at e
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

end Rigid

section Frame

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem kaUGOrth_of_frame (hp2 : p ≠ 2) (hn : 3 ≤ n) (hexc : ¬ (p ^ f = 3 ∧ n ≤ 4))
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {w : Fin n → h.fixedField} (hw : OrthNF w)
    (hR : ((diagGL hw.1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P)) :
    KAAll (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨_, e⟩ => by
    rw [e] at hqodd
    exact absurd hqodd (by decide)
  have hchar := kaUGOrth_ringChar h hp2
  set R := diagGL hw.1 with hRdef
  have hRsym : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ = R := diagonal_transpose _
  have hexcF : ¬ (Nat.card h.fixedField = 3 ∧ n ≤ 4) := by rwa [h.card_fixedField]
  obtain ⟨hperf, m, L, hsup, hL⟩ := orthComponentData hchar hn R hRsym hexcF
  set Iso := CatalogueBGraphForm.isometryGroup n h.fixedField R with hIso
  have hcle : ⁅Iso, Iso⁆ ≤ Iso := Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hΩ1 : ⁅Iso, Iso⁆ ≤ iso1 h R := by
    intro X hX
    refine Subgroup.mem_inf.2 ⟨hcle hX, ?_⟩
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact PSL.det_eq_one_of_mem_commutator hX
  have hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) →
          ∀ X ∈ ⁅Iso, Iso⁆, Y * X * Y⁻¹ ∈ ⁅Iso, Iso⁆ :=
    fun Y μ hμ hY X hX => conj_mem_commutator_isometryGroup_of_similitude hY hμ hX
  have hnK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hinj := ka_conj_inj_pu hnK hn (fun e => hq ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩)
  set φ := uLift h A (barEq h) with hφdef
  have hφ : ∀ g, (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h) :
      MulAut (StatedProj (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) (φ g) :=
    fun g => uLift_proj h (by omega) A (barEq h) g
  set G := gHom h hPPi hPiP hs hR with hG
  set FΩ := ((⁅Iso, Iso⁆ : Subgroup (GL (Fin n) h.fixedField)).subgroupOf (iso1 h R)).map G
    with hFΩ
  have hfixS : ∀ g ∈ FΩ, φ g = g := by
    rintro _ ⟨X', -, rfl⟩
    exact uLift_gHom h hPPi hPiP hs hR hb hbP X'
  have hnormS : ∀ H : StatedSU n (p ^ f) K, projH (StatedSU n (p ^ f) K) (φ H) =
      projH (StatedSU n (p ^ f) K) H → ∀ g ∈ FΩ, H * g * H⁻¹ ∈ FΩ :=
    fun H hH g hg => conj_mem_map_gHom h hPPi hPiP hs hR (by omega) hb hbP hΩ1 hΩ
      (projH_eq_projH_iff.1 hH.symm) hg
  have hQq : ∀ i, IsQuasisimple (((L i).subgroupOf (iso1 h R)).map G) := by
    intro i
    obtain ⟨hq, hLΩ, -⟩ := hL i
    have e1 : (L i).subgroupOf (iso1 h R) ≃* L i := subgroupOfEquivOfLe (hLΩ.trans hΩ1)
    have e2 : (L i).subgroupOf (iso1 h R) ≃* ((L i).subgroupOf (iso1 h R)).map G :=
      ((L i).subgroupOf (iso1 h R)).equivMapOfInjective G (gHom_injective h hPPi hPiP hs hR)
    exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hq
  have hQF : ∀ i, ((L i).subgroupOf (iso1 h R)).map G ≤ FΩ :=
    fun i => Subgroup.map_mono (fun x hx => (hL i).2.1 hx)
  have hΩsup : ((⁅Iso, Iso⁆ : Subgroup (GL (Fin n) h.fixedField)).subgroupOf (iso1 h R)) =
      ⨆ i, (L i).subgroupOf (iso1 h R) := by
    apply le_antisymm
    · intro x hx
      have hx' : (x : GL (Fin n) h.fixedField) ∈ ⨆ i, L i := by rw [hsup]; exact hx
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
  have hperfA : ⁅(⁅Iso, Iso⁆ : Subgroup (GL (Fin n) h.fixedField)).subgroupOf (iso1 h R),
      (⁅Iso, Iso⁆ : Subgroup (GL (Fin n) h.fixedField)).subgroupOf (iso1 h R)⁆ =
      (⁅Iso, Iso⁆ : Subgroup (GL (Fin n) h.fixedField)).subgroupOf (iso1 h R) := by
    apply Subgroup.map_injective (iso1 h R).subtype_injective
    rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hΩ1, hperf]
  have hperfF : ⁅FΩ, FΩ⁆ = FΩ := by rw [hFΩ, ← map_commutator, hperfA]
  have hFn : ∀ i, ∀ H ∈ FΩ, ∀ g ∈ ((L i).subgroupOf (iso1 h R)).map G,
      H * g * H⁻¹ ∈ ((L i).subgroupOf (iso1 h R)).map G := by
    intro i H hH g hg
    obtain ⟨X', hX', rfl⟩ := hH
    obtain ⟨l, hl, rfl⟩ := hg
    refine ⟨X' * l * X'⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (hL i).2.2 _ hX' _ hl
  refine ka_orth_all_of_components hinj (projH (StatedSU n (p ^ f) K)) projH_surjective φ hφ hfixS
    hnormS hperfF (fun i => ((L i).subgroupOf (iso1 h R)).map G) hQq hQF (le_of_eq hFsup) hFn ?_
  intro p' hp' hp'2 e hpg hc hfixL
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp' hp'2 hpg (Subgroup.mem_zpowers e)
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn hq e
  have hfix : ∀ g ∈ FΩ, (uConjAut h (by omega) D * uFieldAut h (by omega) τ :
      MulAut (StatedProj (StatedSU n (p ^ f) K))) (projH (StatedSU n (p ^ f) K) g) =
        projH (StatedSU n (p ^ f) K) g :=
    fun g hg => hfixL _ ⟨g, hg, rfl⟩
  refine kaUGOrth_trivial h hp2 hn hPPi hPiP hb hbP hs hw hR hodd hc ?_
  intro X hX
  have e1 := uSemilinear_eq_of_fix h (by omega) hperfF hfix
    (g := G ⟨X, hΩ1 hX⟩) ⟨⟨X, hΩ1 hX⟩, hX, rfl⟩
  rwa [coe_gHom] at e1

end Frame

theorem kaUGOrth_thm : KAUGOrth := by
  intro p f K _ _ h n hn hp2 hexc A hAc
  have hchar := kaUGOrth_ringChar h hp2
  set Am := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hAm
  have hA : (Am.map h.bar)ᵀ * Am = 1 := (mem_uU h).1 A.2
  obtain ⟨-, P, Pi, b, s, R, hPPi, hPiP, hb, hs, hbP, hR, hsym, -⟩ :=
    exists_graph_frame h hp2 (by omega) hA (c := 1) one_ne_zero hAc
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
  set RG : GL (Fin n) h.fixedField := Matrix.nonsingInvUnit R (isUnit_iff_ne_zero.2 hdetR)
    with hRGdef
  have hRG : (RG : Matrix (Fin n) (Fin n) h.fixedField) = R := rfl
  have hRsym : (RG : Matrix (Fin n) (Fin n) h.fixedField)ᵀ = RG := hsym rfl
  obtain ⟨Q, w, hw, hQ⟩ := PSL.exists_orth_normal_form hchar hn RG hRsym
  set Qm := ((Q : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) with hQm
  set Qim := ((Q⁻¹ : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)
    with hQim
  have hQQ : Qm * Qim = 1 := by rw [hQm, hQim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQQ' : Qim * Qm = 1 := by rw [hQm, hQim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hone : (1 : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = 1 :=
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
  have hbP' : b • (Am * P'.map h.bar) = P' := by
    rw [hP', Matrix.map_mul, map_bar_fmap, ← Matrix.mul_assoc, ← Matrix.smul_mul, hbP]
  have hR' : ((diagGL hw.1 : GL (Fin n) h.fixedField) :
      Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
        s • ((P'.map h.bar)ᵀ * P') := by
    rw [PSL.coe_diagGL, ← hQ, Matrix.map_mul, Matrix.map_mul, hRG, hR, hP', Matrix.map_mul,
      map_bar_fmap, transpose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, transpose_map]
  exact kaUGOrth_of_frame h hp2 hn hexc hPPi' hPiP' hb hbP' hs hw hR'

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
