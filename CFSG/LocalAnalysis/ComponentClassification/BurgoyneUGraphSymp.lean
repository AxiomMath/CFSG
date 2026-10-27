module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphOrth

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.U

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank Module
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ComponentClassification.Burgoyne.PSL (exists_eigen_of_commute_vecMulVec
  vecMul_dotProduct_self_of_alt symTransv_mem unipSL coe_unipSL exists_vecMul_ne_zero
  commutator_eq_self_of_isQuasisimple)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem eq_scalar_of_eigen_fixedField {D : Matrix (Fin n) (Fin n) K} (a : Fin n)
    (hD : ∀ v : Fin n → h.fixedField, ∃ μ : K,
      D *ᵥ (fun i => (v i : K)) = μ • fun i => (v i : K)) :
    D = Matrix.scalar (Fin n) (D a a) := by
  have hcol : ∀ i j, i ≠ j → D i j = 0 := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := hD (Pi.single j 1)
    have := congrFun hμ i
    have hv : (fun k => ((Pi.single j (1 : h.fixedField) : Fin n → h.fixedField) k : K)) =
        Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    rw [hv] at this
    simp only [mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply, hij,
      ↓reduceIte, smul_zero] at this
    simpa using this
  have hdiag : ∀ i j, D i i = D j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨μ, hμ⟩ := hD (Pi.single i 1 + Pi.single j 1)
    have hv : (fun k => ((Pi.single i (1 : h.fixedField) + Pi.single j 1 :
        Fin n → h.fixedField) k : K)) = Pi.single i 1 + Pi.single j 1 := by
      funext k
      by_cases hki : k = i
      · subst hki
        simp [hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [hki]
        · simp [hki, hkj]
    rw [hv] at hμ
    have hi := congrFun hμ i
    have hj := congrFun hμ j
    simp only [mulVec_add, mulVec_single_one, Matrix.col_apply, Pi.add_apply, Pi.smul_apply,
      Pi.single_apply, hij, Ne.symm hij, ↓reduceIte, smul_eq_mul] at hi hj
    rw [hcol i j hij] at hi
    rw [hcol j i (Ne.symm hij)] at hj
    simp only [add_zero, zero_add, mul_one] at hi hj
    rw [hi, hj]
  ext i j
  rw [scalar_apply, diagonal_apply]
  split_ifs with hij
  · rw [hij, hdiag j a]
  · exact hcol i j hij

theorem graphSymp_oddCoreIn_eq_bot (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B)
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
    (hRalt : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) h.fixedField))
    (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
      s • ((P.map h.bar)ᵀ * P)) :
    oddCoreIn B (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) = ⊥ := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have hpodd : Odd p := h.prime.odd_of_ne_two hp2
  have hqodd : Odd (p ^ f) := hpodd.pow
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
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
  set Ω := CatalogueBGraphForm.isometryGroup n h.fixedField R with hΩdef
  have hI : IsQuasisimple Ω :=
    LocalCores.isQuasisimple_of_mulEquiv (CatalogueBLinearHigherB.isometryGroupEquiv R)
      (CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le _
        (CatalogueBLinearHigherB.matrixForm_isAlt hF2 R hRalt)
        (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
        (by rwa [Module.finrank_fin_fun])
        (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two h.fixedField hF2))
  have hperf : ⁅Ω, Ω⁆ = Ω := commutator_eq_self_of_isQuasisimple hI
  have hΩ1 : Ω ≤ iso1 h R := by
    intro X hX
    refine Subgroup.mem_inf.2 ⟨hX, ?_⟩
    rw [← hperf] at hX
    rw [MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact PSL.det_eq_one_of_mem_commutator hX
  have hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) → ∀ X ∈ Ω, Y * X * Y⁻¹ ∈ Ω :=
    fun Y μ hμ hY X hX => conj_mem_isometryGroup_of_similitude hY hμ hX
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq y
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn3 hq (pow_orderOf_eq_one _)
  have hfixΩ := fun (X : iso1 h R) (hX : (X : GL (Fin n) h.fixedField) ∈ Ω) =>
    graph_fix_of_components h hn3 hinj hB hPPi hPiP hs hR hb hbP hΩ1 hΩ hperf
      (L := fun _ : Fin 1 => Ω) (by rw [iSup_const])
      (fun _ => ⟨hI, le_rfl, fun x hx l hl => mul_mem (mul_mem hx hl) (inv_mem hx)⟩) hy hX
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
  have hD'iD' : D'i * D' = 1 := mul_eq_one_comm.1 hD'D'i
  set D'G : GL (Fin n) K := ⟨D', D'i, hD'D'i, hD'iD'⟩ with hD'G
  have hX' : ∀ X ∈ Ω, D' * ((X : Matrix (Fin n) (Fin n) h.fixedField).map
      h.fixedField.subtype).map τ * D'i = (X : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype := by
    intro X hX
    have e := hfixΩ ⟨X, hΩ1 hX⟩ hX
    rw [coe_gHom] at e
    exact conj_fmap_of_conj_gTr h hPiP τ e
  set R' := (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype with hR'
  have htr : ∀ (v : Fin n → h.fixedField) (c : h.fixedField),
      ((SpecialLinearGroup.toGL (unipSL (vecMul_dotProduct_self_of_alt hF2 hRalt v) c) :
        GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
          h.fixedField.subtype =
        1 + (c : K) • vecMulVec (fun i => (v i : K)) ((fun i => (v i : K)) ᵥ* R') := by
    intro v c
    change (1 + c • vecMulVec v (v ᵥ* (R : Matrix (Fin n) (Fin n) h.fixedField))).map
      h.fixedField.subtype = _
    ext i j
    simp only [map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
      one_apply, hR', vecMul, dotProduct]
    split_ifs <;> simp
  have htrm : ∀ (v : Fin n → h.fixedField) (c : h.fixedField),
      SpecialLinearGroup.toGL (unipSL (vecMul_dotProduct_self_of_alt hF2 hRalt v) c) ∈ Ω :=
    fun v c => symTransv_mem hF2 hRalt v c
  set R'G : GL (Fin n) K := Matrix.GeneralLinearGroup.map h.fixedField.subtype R with hR'G
  have hR'Gc : (R'G : Matrix (Fin n) (Fin n) K) = R' := rfl
  set e0 : Fin n → h.fixedField := _root_.Pi.single ⟨0, by omega⟩ 1 with he0
  have he0ne : (fun i => (e0 i : K)) ≠ 0 := by
    intro e
    have := congrFun e ⟨0, by omega⟩
    simp [he0] at this
  obtain ⟨b0, hb0⟩ := exists_vecMul_ne_zero R'G he0ne
  rw [hR'Gc] at hb0
  have hN0ne : vecMulVec (fun i => (e0 i : K)) ((fun i => (e0 i : K)) ᵥ* R') ⟨0, by omega⟩ b0
      ≠ 0 := by
    rw [vecMulVec_apply]
    simpa [he0] using hb0
  have hτF : ∀ c, h.bar c = c → τ c = c := fix_of_conj_family h (D := D'G) hN0ne fun c hc => by
    have e := hX' _ (htrm e0 ⟨c, hc⟩)
    rw [htr] at e
    exact e
  have hτ1 : τ = 1 := eq_one_of_odd_of_fix h hodd hτm hτF
  subst hτ1
  have heig : ∀ v : Fin n → h.fixedField, ∃ μ : K,
      D' *ᵥ (fun i => (v i : K)) = μ • fun i => (v i : K) := by
    intro v
    by_cases hv : (fun i => (v i : K)) = 0
    · exact ⟨0, by rw [hv, mulVec_zero, smul_zero]⟩
    obtain ⟨b1, hb1⟩ := exists_vecMul_ne_zero R'G hv
    rw [hR'Gc] at hb1
    have e := hX' _ (htrm v 1)
    rw [htr, map_one_ringEquiv] at e
    set N := vecMulVec (fun i => (v i : K)) ((fun i => (v i : K)) ᵥ* R') with hN
    have hc : D' * N = N * D' := by
      have e1 : D' * (1 + (((1 : h.fixedField) : K)) • N) = (1 + (((1 : h.fixedField) : K)) • N) *
          D' := by
        calc D' * (1 + (((1 : h.fixedField) : K)) • N) =
            D' * (1 + (((1 : h.fixedField) : K)) • N) * (D'i * D') := by
              rw [hD'iD', Matrix.mul_one]
          _ = _ := by rw [← Matrix.mul_assoc, e]
      simpa [Matrix.mul_add, Matrix.add_mul] using e1
    exact exists_eigen_of_commute_vecMulVec hb1 hc
  have hsc := eq_scalar_of_eigen_fixedField h ⟨0, by omega⟩ heig
  set c0 := D' ⟨0, by omega⟩ ⟨0, by omega⟩ with hc0def
  have hD'0 : c0 ≠ 0 := by
    intro h0
    have e := hD'D'i
    rw [hsc, h0, map_zero, Matrix.zero_mul] at e
    have := congrFun (congrFun e ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at this
  rw [map_one, mul_one]
  refine (uConjAut_eq_one_iff h hn3 D).2 ⟨Units.mk0 _ hD'0, Units.ext ?_⟩
  rw [GeneralLinearGroup.coe_scalar]
  change Dm = _
  have hDmP : Dm = P * D' * Pi := by
    rw [hD', map_one_ringEquiv]
    calc Dm = (P * Pi) * Dm * (P * Pi) := by rw [hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hDmP, hsc, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, hPPi, Matrix.smul_one_eq_diagonal]
  rfl

end CFSG.ComponentClassification.Burgoyne.U
