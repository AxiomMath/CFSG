module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUDef
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphSymp
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUGraphDescent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank Module CFSG.ComponentClassification
  CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.Burgoyne.PSL (exists_eigen_of_commute_vecMulVec
  vecMul_dotProduct_self_of_alt symTransv_mem unipSL exists_vecMul_ne_zero)
open scoped commutatorElement

section GSp

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem ka_u_ringChar_ne_two (hp2 : p ≠ 2) : ringChar h.fixedField ≠ 2 := by
  have := h.charP
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
  exact fun e => h2F (by
    have := ringChar.spec h.fixedField 2
    exact_mod_cast (this.2 (by rw [e])))

theorem ka_u_gsp_quasisimple (hp2 : p ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) h.fixedField}
    (hRalt : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) h.fixedField)) :
    IsQuasisimple (CatalogueBGraphForm.isometryGroup n h.fixedField R) := by
  have := h.finite
  have hF2 := ka_u_ringChar_ne_two h hp2
  exact LocalCores.isQuasisimple_of_mulEquiv (CatalogueBLinearHigherB.isometryGroupEquiv R)
    (CatalogueBAlternatingIsometry.isometry_quasisimple_of_four_le _
      (CatalogueBLinearHigherB.matrixForm_isAlt hF2 R hRalt)
      (CatalogueBLinearHigherB.matrixForm_nondegenerate R)
      (by rwa [Module.finrank_fin_fun])
      (CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two h.fixedField hF2))

theorem ka_u_gsp_le_iso1 (hp2 : p ≠ 2) (hn : 4 ≤ n) {R : GL (Fin n) h.fixedField}
    (hRalt : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) h.fixedField)) :
    CatalogueBGraphForm.isometryGroup n h.fixedField R ≤ iso1 h R := by
  have hperf := CFSG.ComponentClassification.Burgoyne.PSL.commutator_eq_self_of_isQuasisimple
    (ka_u_gsp_quasisimple h hp2 hn hRalt)
  intro X hX
  refine Subgroup.mem_inf.2 ⟨hX, ?_⟩
  rw [← hperf] at hX
  rw [MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact CFSG.ComponentClassification.Burgoyne.PSL.det_eq_one_of_mem_commutator hX

theorem ka_u_gsp_rigid (hp2 : p ≠ 2) (hn : 4 ≤ n) {P Pi : Matrix (Fin n) (Fin n) K}
    (hPPi : P * Pi = 1) (hPiP : Pi * P = 1) {s : K} (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
    (hRalt : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) h.fixedField))
    (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
      s • ((P.map h.bar)ᵀ * P)) {D : uU h n} {τ : K ≃+* K}
    (hodd : Odd (orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ)))
    (hfixΩ : ∀ X : iso1 h R,
      (X : GL (Fin n) h.fixedField) ∈ CatalogueBGraphForm.isometryGroup n h.fixedField R →
      ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((gHom h hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K).map τ *
        (((D : GL (Fin n) K)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((gHom h hPPi hPiP hs hR X : StatedSU n (p ^ f) K) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) :
    uConjAut h (by omega) D * uFieldAut h (by omega) τ = 1 := by
  have := h.finite
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
  have hF2 := ka_u_ringChar_ne_two h hp2
  set Ω := CatalogueBGraphForm.isometryGroup n h.fixedField R with hΩdef
  have hΩ1 : Ω ≤ iso1 h R := ka_u_gsp_le_iso1 h hp2 hn hRalt
  have hτm : τ ^ orderOf (uConjAut h (by omega) D * uFieldAut h (by omega) τ) = 1 :=
    fieldAut_pow_eq_one h hn3 hq (pow_orderOf_eq_one _)
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

theorem ka_u_gsp_all [Finite K] (hp2 : p ≠ 2) (hn : 4 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {A : uU h n} {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) (hPiP : Pi * P = 1)
    {b : K} (hb : b ≠ 0)
    (hbP : b • (((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * P.map h.bar) = P)
    {s : K} (hs : s ≠ 0) {R : GL (Fin n) h.fixedField}
    (hRalt : (R : Matrix (Fin n) (Fin n) h.fixedField)ᵀ =
      -(R : Matrix (Fin n) (Fin n) h.fixedField))
    (hR : (R : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype =
      s • ((P.map h.bar)ᵀ * P)) :
    KAAll (uConjAut h (by omega) A * uFieldAut h (by omega) (barEq h)) := by
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun ⟨e, _⟩ => by omega
  set Ω := CatalogueBGraphForm.isometryGroup n h.fixedField R with hΩdef
  have hI : IsQuasisimple Ω := ka_u_gsp_quasisimple h hp2 hn hRalt
  have hperf : ⁅Ω, Ω⁆ = Ω :=
    CFSG.ComponentClassification.Burgoyne.PSL.commutator_eq_self_of_isQuasisimple hI
  have hΩ1 : Ω ≤ iso1 h R := ka_u_gsp_le_iso1 h hp2 hn hRalt
  have hΩ : ∀ (Y : GL (Fin n) h.fixedField) (μ : h.fixedField), μ ≠ 0 →
      (Y : Matrix (Fin n) (Fin n) h.fixedField)ᵀ * R * Y =
        μ • (R : Matrix (Fin n) (Fin n) h.fixedField) → ∀ X ∈ Ω, Y * X * Y⁻¹ ∈ Ω :=
    fun Y μ hμ hY X hX => conj_mem_isometryGroup_of_similitude hY hμ hX
  set S : Subgroup (StatedSU n (p ^ f) K) :=
    (Ω.subgroupOf (iso1 h R)).map (gHom h hPPi hPiP hs hR) with hS
  have hSq : IsQuasisimple S := by
    have e1 : Ω.subgroupOf (iso1 h R) ≃* Ω := subgroupOfEquivOfLe hΩ1
    have e2 : Ω.subgroupOf (iso1 h R) ≃* S :=
      (Ω.subgroupOf (iso1 h R)).equivMapOfInjective _ (gHom_injective h hPPi hPiP hs hR)
    exact LocalCores.isQuasisimple_of_mulEquiv (e1.symm.trans e2) hI
  have hSperf : ⁅S, S⁆ = S := by
    have hperfA : ⁅Ω.subgroupOf (iso1 h R), Ω.subgroupOf (iso1 h R)⁆ =
        Ω.subgroupOf (iso1 h R) := by
      apply Subgroup.map_injective (iso1 h R).subtype_injective
      rw [map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hΩ1, hperf]
    rw [hS, ← map_commutator, hperfA]
  have hfix : ∀ g ∈ S, uLift h A (barEq h) g = g := by
    rintro _ ⟨X', -, rfl⟩
    exact uLift_gHom h hPPi hPiP hs hR hb hbP X'
  have hnorm : ∀ H : StatedSU n (p ^ f) K,
      projH (StatedSU n (p ^ f) K) (uLift h A (barEq h) H) = projH (StatedSU n (p ^ f) K) H →
      ∀ g ∈ S, H * g * H⁻¹ ∈ S := by
    intro H hH g hg
    exact conj_mem_map_gHom h hPPi hPiP hs hR (by omega) hb hbP hΩ1 hΩ
      (projH_eq_projH_iff.1 hH.symm) hg
  refine ka_orth_all_of_components hinj (projH (StatedSU n (p ^ f) K)) projH_surjective
    (uLift h A (barEq h)) (fun g => uLift_proj h (by omega) A (barEq h) g) hfix hnorm hSperf
    (m := 1) (fun _ => S) (fun _ => hSq) (fun _ => le_rfl) (le_iSup (fun _ : Fin 1 => S) 0)
    (fun _ x hx l hl => mul_mem (mul_mem hx hl) (inv_mem hx)) ?_
  intro ℓ hℓ hℓ2 e hpg hc hfixL
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hℓ hℓ2 hpg (Subgroup.mem_zpowers e)
  obtain ⟨D, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq e
  exact ka_u_gsp_rigid h hp2 hn hPPi hPiP hs hRalt hR hodd
    (fun X hX => uSemilinear_eq_of_fix h (by omega) hSperf
      (fun g hg => hfixL _ ⟨g, hg, rfl⟩) ⟨X, hX, rfl⟩)

theorem ka_u_frame_det_ne_zero {P Pi : Matrix (Fin n) (Fin n) K} (hPPi : P * Pi = 1) {s : K}
    (hs : s ≠ 0) {R : Matrix (Fin n) (Fin n) h.fixedField}
    (hR : R.map h.fixedField.subtype = s • ((P.map h.bar)ᵀ * P)) : R.det ≠ 0 := by
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
  intro e
  have e1 := congrArg Matrix.det hR
  have e2 := RingHom.map_det h.fixedField.subtype R
  rw [RingHom.mapMatrix_apply] at e2
  rw [← e2, e, map_zero, Matrix.det_smul, Matrix.det_mul, det_transpose] at e1
  exact mul_ne_zero (pow_ne_zero _ hs) (mul_ne_zero hdetPb hdetP) e1.symm

end GSp

theorem kaU4GSp_thm : KAU4GSp := by
  intro p f K _ _ h hp2 A hA
  have : Fact p.Prime := ⟨h.prime⟩
  have hU : (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map h.bar)ᵀ *
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := (mem_uU h).1 A.2
  obtain ⟨-, P, Pi, b, s, R, hPPi, hPiP, hb, hs, hbP, hR, -, halt⟩ :=
    exists_graph_frame h hp2 (by norm_num) hU (neg_ne_zero.2 one_ne_zero) hA
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.2 (ka_u_frame_det_ne_zero h hPPi hs hR)
  exact ka_u_gsp_all h hp2 (le_refl 4)
    (ka_conj_inj_pu h.card_eq_sq (by norm_num) (by simp)) hPPi hPiP hb hbP hs
    (R := Matrix.nonsingInvUnit R hRu) (halt rfl) hR

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
