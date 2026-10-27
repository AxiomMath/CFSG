module

public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6A5Cube CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.ClassicalInvolution.Balance.StrongBalance (GUid mem_GUid conjSUid coe_conjSUid)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc

section Arith

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem unitaryInvolution_eq_inv_of_pow_three {c : Kˣ} (hc : c ^ 3 = 1) (h3 : 3 ∣ ℓ ^ f + 1) :
    unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K) := by
  obtain ⟨m, hm⟩ := h3
  have e : ℓ ^ f = 3 * (m - 1) + 2 := by omega
  have hc2 : c ^ (ℓ ^ f) = c⁻¹ := by
    rw [e, pow_add, pow_mul, hc, one_pow, one_mul]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hc])
  rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, hc2]

end Arith

section Perm

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

omit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
theorem permMatrix_apply (π : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    (π.permMatrix K) i j = if π i = j then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]

@[expose] noncomputable def permSU (π : Equiv.Perm (Fin 6)) (hπ : Equiv.Perm.sign π = 1) :
    Su K ℓ f 6 :=
  ⟨(Matrix.permMatrixHom (n := Fin 6) (R := K)).toHomUnits π, by
    refine ⟨?_, ?_⟩
    · change ((π⁻¹).permMatrix K).det = 1
      rw [Matrix.det_permutation, Equiv.Perm.sign_inv, hπ]
      simp
    · change conjTr (unitaryInvolution K ℓ f) ((π⁻¹).permMatrix K) * (π⁻¹).permMatrix K = 1
      have hmap : ((π⁻¹).permMatrix K).map (unitaryInvolution K ℓ f) = (π⁻¹).permMatrix K := by
        ext i j
        rw [Matrix.map_apply, permMatrix_apply]
        split_ifs <;> simp
      rw [conjTr, hmap, Matrix.transpose_permMatrix, inv_inv, ← Matrix.permMatrix_mul,
        inv_mul_cancel, Matrix.permMatrix_one]⟩

theorem coe_permSU (π : Equiv.Perm (Fin 6)) (hπ : Equiv.Perm.sign π = 1) :
    (((permSU π hπ : Su K ℓ f 6) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      (π⁻¹).permMatrix K :=
  rfl

omit [Finite K] [Fact ℓ.Prime] [CharP K ℓ] in
theorem eq_of_diagonal_mul_permMatrix {a : Fin 6 → K} (ha : ∀ i, a i ≠ 0) {l : K}
    {π : Equiv.Perm (Fin 6)} {i₀ : Fin 6} (hi₀ : π i₀ = i₀)
    (h : diagonal a * (π⁻¹).permMatrix K = l • ((π⁻¹).permMatrix K * diagonal a)) (i : Fin 6) :
    a (π i) = a i := by
  have hent : ∀ r s, a r * (if π⁻¹ r = s then (1 : K) else 0) =
      l * ((if π⁻¹ r = s then (1 : K) else 0) * a s) := fun r s => by
    have := congrFun (congrFun h r) s
    rwa [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, permMatrix_apply,
      smul_eq_mul] at this
  have hi₀' : π⁻¹ i₀ = i₀ := by rw [Equiv.Perm.inv_eq_iff_eq, hi₀]
  have hl : l = 1 := by
    have h1 := hent i₀ i₀
    rw [if_pos hi₀', mul_one, one_mul] at h1
    have h2 : (l - 1) * a i₀ = 0 := by linear_combination -h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (ha i₀))
  have h1 := hent (π i) i
  rw [if_pos (by simp), mul_one, one_mul, hl, one_mul] at h1
  exact h1

end Perm

section Scalar

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)

theorem eq_of_forall_leviSU_conjSUid_eq {A : GUid (unitaryInvolution K ℓ f) 6} {a : Fin 6 → K}
    (hA : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal a)
    (h : ∀ y : Su K ℓ f 6,
      leviSU hK hf hζ hσζ P hP (conjSUid (unitaryInvolution K ℓ f) 6 A y) =
        leviSU hK hf hζ hσζ P hP y) (i j : Fin 6) : a i = a j := by
  have ha : ∀ i, a i ≠ 0 := fun i hi => by
    have h1 : ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        (((A : GL (Fin 6) K)⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h2 := congrFun (congrFun h1 i) i
    rw [hA, Matrix.diagonal_mul, hi, zero_mul, Matrix.one_apply_eq] at h2
    exact zero_ne_one h2
  have key : ∀ (π : Equiv.Perm (Fin 6)) (hπ : Equiv.Perm.sign π = 1) {i₀ : Fin 6}, π i₀ = i₀ →
      ∀ r, a (π r) = a r := by
    intro π hπ i₀ hi₀
    have h1 := h (permSU π hπ)
    rw [← mul_inv_eq_one, ← map_inv, ← map_mul] at h1
    obtain ⟨l, hl⟩ := exists_smul_of_leviSU_eq_one hK hf hζ hσζ P hP h1
    refine eq_of_diagonal_mul_permMatrix (l := l) ha hi₀ ?_
    have e : (A : GL (Fin 6) K) * ((permSU π hπ : Su K ℓ f 6) : GL (Fin 6) K) =
        ((conjSUid (unitaryInvolution K ℓ f) 6 A (permSU π hπ) * (permSU π hπ)⁻¹ : Su K ℓ f 6) :
          GL (Fin 6) K) * (((permSU π hπ : Su K ℓ f 6) : GL (Fin 6) K) * (A : GL (Fin 6) K)) := by
      rw [Subgroup.coe_mul, coe_conjSUid, Subgroup.coe_inv]
      group
    have e2 := congrArg (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) e
    simp only [Units.val_mul] at e2
    rw [hl, hA, coe_permSU, Matrix.smul_mul, Matrix.one_mul] at e2
    exact e2
  have hs : ∀ {u v w x : Fin 6}, u ≠ v → w ≠ x →
      Equiv.Perm.sign (Equiv.swap u v * Equiv.swap w x) = 1 := fun h1 h2 => by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]
    rfl
  have k1 := key _ (hs (u := 0) (v := 1) (w := 2) (x := 3) (by decide) (by decide))
    (i₀ := 4) (by decide)
  have k2 := key _ (hs (u := 1) (v := 2) (w := 3) (x := 4) (by decide) (by decide))
    (i₀ := 0) (by decide)
  have k3 := key _ (hs (u := 0) (v := 1) (w := 4) (x := 5) (by decide) (by decide))
    (i₀ := 2) (by decide)
  have e10 : a 1 = a 0 := by
    have h := k1 0
    rwa [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) 0 = 1 by decide] at h
  have e32 : a 3 = a 2 := by
    have h := k1 2
    rwa [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 6)) 2 = 3 by decide] at h
  have e21 : a 2 = a 1 := by
    have h := k2 1
    rwa [show (Equiv.swap (1 : Fin 6) 2 * Equiv.swap 3 4 : Equiv.Perm (Fin 6)) 1 = 2 by decide] at h
  have e43 : a 4 = a 3 := by
    have h := k2 3
    rwa [show (Equiv.swap (1 : Fin 6) 2 * Equiv.swap 3 4 : Equiv.Perm (Fin 6)) 3 = 4 by decide] at h
  have e54 : a 5 = a 4 := by
    have h := k3 4
    rwa [show (Equiv.swap (0 : Fin 6) 1 * Equiv.swap 4 5 : Equiv.Perm (Fin 6)) 4 = 5 by decide] at h
  have h0 : ∀ r, a r = a 0 := by
    intro r
    fin_cases r
    · rfl
    · exact e10
    · exact e21.trans e10
    · exact e32.trans (e21.trans e10)
    · exact e43.trans (e32.trans (e21.trans e10))
    · exact e54.trans (e43.trans (e32.trans (e21.trans e10)))
  rw [h0 i, h0 j]

end Scalar

section DMatrix

variable {K : Type} [Field K]

@[expose] def vtwB (c : Kˣ) : Fin TwistTag.E6.tag.rank → Kˣ :=
  (![c, 1, 1, 1, 1, c⁻¹] : Fin 6 → Kˣ)

@[expose] def vtwBa (c : Kˣ) : Fin Tag.E6.rank → Kˣ := (![c, 1, 1, 1, 1, c⁻¹] : Fin 6 → Kˣ)

@[expose] def vtwE (c : Kˣ) : Fin 6 → Kˣ := ![1, c⁻¹, c⁻¹, c⁻¹, c⁻¹, 1]

@[expose] noncomputable def vtwD (c : Kˣ) : ModGL TwistTag.E6.tag K :=
  rootDiagUnit TwistTag.E6.tag (vtwB c)

theorem conjDiag_transvection (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) {i j : Fin 6} (hij : i ≠ j)
    (a : K) :
    conjDiag K e he (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij (e i * a * (e j)⁻¹) := by
  apply Subtype.ext
  rw [E6A5Cube.coe_conjDiag, SpecialLinearGroup.transvection_coe,
    SpecialLinearGroup.transvection_coe]
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.add_apply, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases hrs : r = s
  · subst hrs
    have hn : ¬ (i = r ∧ j = r) := fun h => hij (h.1.trans h.2.symm)
    simp only [if_true, hn, if_false, add_zero, mul_one]
    exact mul_inv_cancel₀ (he r)
  · by_cases h2 : i = r ∧ j = s
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [hrs, if_false, and_self, if_true, zero_add]
    · simp only [hrs, h2, if_false, add_zero, mul_zero, zero_mul]

theorem vtwBa_jA (c : Kˣ) (t : Fin 5) :
    ((vtwBa c (C2E6Std.jA t) : Kˣ) : K) =
      (vtwE c t.castSucc : K) * ((vtwE c t.succ : Kˣ) : K)⁻¹ := by
  fin_cases t <;> simp [vtwBa, vtwE, C2E6Std.jA]

theorem vtwBa_jA_inv (c : Kˣ) (t : Fin 5) :
    (((vtwBa c (C2E6Std.jA t))⁻¹ : Kˣ) : K) =
      (vtwE c t.succ : K) * ((vtwE c t.castSucc : Kˣ) : K)⁻¹ := by
  fin_cases t <;> simp [vtwBa, vtwE, C2E6Std.jA]

end DMatrix

section DLift

variable {K : Type} [Field K] [Finite K]

theorem vtwD_conj_liftA (c : Kˣ) (h : SpecialLinearGroup (Fin 6) K) :
    rootDiagUnit Tag.E6 (vtwBa c) * ((liftA K h : groupA K) : ModGL Tag.E6 K) *
        (rootDiagUnit Tag.E6 (vtwBa c))⁻¹ =
      ((liftA K (conjDiag K (fun i => (vtwE c i : K)) (fun i => (vtwE c i).ne_zero) h) :
        groupA K) : ModGL Tag.E6 K) := by
  have key : (MulAut.conj (rootDiagUnit Tag.E6 (vtwBa c))).toMonoidHom.comp
        ((groupA K).subtype.comp (liftA K)) =
      ((groupA K).subtype.comp (liftA K)).comp
        (conjDiag K (fun i => (vtwE c i : K)) fun i => (vtwE c i).ne_zero) := by
    refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
    rintro _ ⟨t, a, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [conjDiag_transvection, liftA_upAdj, liftA_upAdj]
      simp only [Subgroup.coe_mk]
      rw [(root_diagonal_conjugation _ K _).1, vtwBa_jA]
      congr 1
      ring
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [conjDiag_transvection, liftA_downAdj, liftA_downAdj]
      simp only [Subgroup.coe_mk]
      rw [(root_diagonal_conjugation _ K _).2.1, vtwBa_jA_inv]
      congr 1
      ring
  exact DFunLike.congr_fun key h

end DLift

section DFacts

variable {K : Type} [Field K] {c : Kˣ}

theorem vtwB_perm {σ : K ≃+* K} (hσc : σ (c : K) = ((c⁻¹ : Kˣ) : K))
    (i : Fin TwistTag.E6.tag.rank) :
    vtwB c (TwistTag.E6.perm i) = Units.map σ.toRingHom.toMonoidHom (vtwB c i) := by
  have hp : ∀ i : Fin 6, (Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i =
      (![5, 1, 4, 3, 2, 0] : Fin 6 → Fin 6) i := by decide
  have hσc' : σ ((c⁻¹ : Kˣ) : K) = (c : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσc, Units.val_inv_eq_inv_val, inv_inv]
  have key : ∀ i : Fin 6, ((vtwB c ((Equiv.swap 0 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i) :
      Kˣ) : K) = σ ((vtwB c i : Kˣ) : K) := by
    intro i
    rw [hp]
    fin_cases i
    · simpa [vtwB] using hσc.symm
    · simp [vtwB]
    · simp [vtwB]
    · simp [vtwB]
    · simp [vtwB]
    · simpa [vtwB] using hσc'.symm
  exact Units.ext (key i)

theorem vtwD_mem_twistedE6DiagGL
    {σ : K ≃+* K}
    (hσc : σ (c : K) = ((c⁻¹ : Kˣ) : K)) : vtwD c ∈ twistedE6DiagGL K σ := by
  obtain ⟨u, hu⟩ := exists_compatDiag_eq (t := TwistTag.E6) (σ := σ.toRingHom) (b := vtwB c)
    (vtwB_perm hσc)
  exact ⟨u, show rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) = vtwD c by
    rw [hu]; rfl⟩

theorem rootChar_vtwB : rootChar (τ := TwistTag.E6.tag) (vtwB c) e6HighestRoot = 1 := by
  change ∏ i : Fin 6,
    (![c, 1, 1, 1, 1, c⁻¹] : Fin 6 → Kˣ) i ^ (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ) i = 1
  rw [Fin.prod_univ_six]
  simp

theorem vtwD_conj_rootSL2
    (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    vtwD c * rootSL2 TwistTag.E6.tag K e6HighestRoot A * (vtwD c)⁻¹ =
      rootSL2 TwistTag.E6.tag K e6HighestRoot A := by
  have h := rootDiagUnit_conj_rootSL2 (τ := TwistTag.E6.tag) (K := K) (vtwB c)
    isRoot_e6HighestRoot A
  rw [rootChar_vtwB, conjSL_diagUnitOne_one] at h
  exact h

theorem vtwD_pow_three (hc3 : c ^ 3 = 1) : vtwD c ^ 3 = 1 := by
  have h6 : ∀ i : Fin 6, (![c, 1, 1, 1, 1, c⁻¹] : Fin 6 → Kˣ) i ^ 3 = 1 := by
    intro i
    fin_cases i <;> simp [hc3, inv_pow]
  have hb : vtwB c ^ 3 = 1 := by
    funext i
    rw [Pi.pow_apply, Pi.one_apply]
    exact h6 i
  have hpow : ∀ n : ℕ, rootDiagUnit TwistTag.E6.tag (vtwB c) ^ n =
      rootDiagUnit TwistTag.E6.tag (vtwB c ^ n) := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
    | succ n ih => rw [pow_succ, ih, pow_succ, rootDiagUnit_mul]
  rw [vtwD, hpow, hb, rootDiagUnit_one]

end DFacts

section DLevi

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  (hK : Nat.card K = (ℓ ^ f) ^ 2) (hf : 1 ≤ f)
  {ζ : K} (hζ : ζ ≠ 0) (hσζ : unitaryInvolution K ℓ f ζ = -ζ)
  (P : GL (Fin 6) K) (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
    (P : Matrix (Fin 6) (Fin 6) K) = antidiag 6)
  {c : Kˣ}

theorem conjTr_vtwE_mul_antidiag (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K)) :
    conjTr (unitaryInvolution K ℓ f) (diagonal fun i => (vtwE c i : K)) * antidiag 6 *
      diagonal (fun i => (vtwE c i : K)) = antidiag 6 := by
  have hσc' : unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) = (c : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hσc, Units.val_inv_eq_inv_val, inv_inv]
  have hcc : ((c⁻¹ : Kˣ) : K) * (c : K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcc' : (c : K) * ((c⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ∀ i : Fin 6,
      unitaryInvolution K ℓ f (vtwE c i : K) * 1 * (vtwE c (Fin.rev i) : K) = 1 := by
    intro i
    fin_cases i
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * 1 * ((1 : Kˣ) : K) = 1
      simp
    · show unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) * 1 * ((c⁻¹ : Kˣ) : K) = 1
      rw [hσc', mul_one, hcc']
    · show unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) * 1 * ((c⁻¹ : Kˣ) : K) = 1
      rw [hσc', mul_one, hcc']
    · show unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) * 1 * ((c⁻¹ : Kˣ) : K) = 1
      rw [hσc', mul_one, hcc']
    · show unitaryInvolution K ℓ f ((c⁻¹ : Kˣ) : K) * 1 * ((c⁻¹ : Kˣ) : K) = 1
      rw [hσc', mul_one, hcc']
    · show unitaryInvolution K ℓ f ((1 : Kˣ) : K) * 1 * ((1 : Kˣ) : K) = 1
      simp
  rw [conjTr, diagonal_map (map_zero _), diagonal_transpose, antidiag_eq_antiDiag,
    diagonal_mul_antiDiag_mul_diagonal]
  congr 1
  funext i
  exact key i

@[expose] noncomputable def vtwC (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K)) :
    GUid (unitaryInvolution K ℓ f) 6 :=
  ⟨P * diagGL K 6 (vtwE c) * P⁻¹, by
    have hE := conjTr_vtwE_mul_antidiag (ℓ := ℓ) (f := f) hσc
    have hPP : (P : Matrix (Fin 6) (Fin 6) K) *
        ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [mem_GUid, Units.val_mul, Units.val_mul, coe_diagGL]
    calc conjTr (unitaryInvolution K ℓ f) ((P : Matrix (Fin 6) (Fin 6) K) *
          (diagonal fun i => (vtwE c i : K)) * ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
          ((P : Matrix (Fin 6) (Fin 6) K) * (diagonal fun i => (vtwE c i : K)) *
            ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K))
        = conjTr (unitaryInvolution K ℓ f) ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            (conjTr (unitaryInvolution K ℓ f) (diagonal fun i => (vtwE c i : K)) *
              (conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
                (P : Matrix (Fin 6) (Fin 6) K)) * (diagonal fun i => (vtwE c i : K))) *
            ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = conjTr (unitaryInvolution K ℓ f) ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
            (conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin 6) (Fin 6) K) *
              (P : Matrix (Fin 6) (Fin 6) K)) *
            ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
          rw [hP, hE, ← hP]
      _ = conjTr (unitaryInvolution K ℓ f) ((P : Matrix (Fin 6) (Fin 6) K) *
            ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) *
            ((P : Matrix (Fin 6) (Fin 6) K) *
              ((P⁻¹ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hPP, conjTr_one, Matrix.one_mul]⟩

theorem coe_vtwC (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K)) :
    ((vtwC P hP hσc : GUid (unitaryInvolution K ℓ f) 6) : GL (Fin 6) K) =
      P * diagGL K 6 (vtwE c) * P⁻¹ :=
  rfl

omit [Finite K] in
theorem conjDiag_conjSU (e : Fin 6 → K) (he : ∀ i, e i ≠ 0) {σ : K ≃+* K} (hζ : ζ ≠ 0)
    {z z' : SU σ 6}
    (hz' : ((z' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal e * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) * diagonal (fun i => (e i)⁻¹)) :
    conjDiag K e he (conjSU σ hζ z) = conjSU σ hζ z' := by
  apply Subtype.ext
  rw [E6A5Cube.coe_conjDiag]
  change diagonal e * (diagonal (eDiag K ζ) * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      diagonal (fun i => (eDiag K ζ i)⁻¹)) * diagonal (fun i => (e i)⁻¹) =
    diagonal (eDiag K ζ) * ((z' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      diagonal (fun i => (eDiag K ζ i)⁻¹)
  rw [hz']
  have h1 : diagonal e * diagonal (eDiag K ζ) = diagonal (eDiag K ζ) * diagonal e := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have h2 : diagonal (fun i => (eDiag K ζ i)⁻¹) * diagonal (fun i => (e i)⁻¹) =
      diagonal (fun i => (e i)⁻¹) * diagonal (fun i => (eDiag K ζ i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  calc diagonal e * (diagonal (eDiag K ζ) * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagonal (fun i => (eDiag K ζ i)⁻¹)) * diagonal (fun i => (e i)⁻¹)
      = (diagonal e * diagonal (eDiag K ζ)) * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (diagonal (fun i => (eDiag K ζ i)⁻¹) * diagonal (fun i => (e i)⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = (diagonal (eDiag K ζ) * diagonal e) * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
          (diagonal (fun i => (e i)⁻¹) * diagonal (fun i => (eDiag K ζ i)⁻¹)) := by rw [h1, h2]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem vtwD_conj_leviSU (hσc : unitaryInvolution K ℓ f (c : K) = ((c⁻¹ : Kˣ) : K))
    (y : Su K ℓ f 6) :
    vtwD c * (leviSU hK hf hζ hσζ P hP y : ModGL TwistTag.E6.tag K) * (vtwD c)⁻¹ =
      (leviSU hK hf hζ hσζ P hP (conjSUid (unitaryInvolution K ℓ f) 6 (vtwC P hP hσc) y) :
        ModGL TwistTag.E6.tag K) := by
  set z := (conjEquiv P hP).symm y with hz
  set z' := (conjEquiv P hP).symm (conjSUid (unitaryInvolution K ℓ f) 6 (vtwC P hP hσc) y)
    with hz'def
  have hz' : ((z' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
      diagonal (fun i => (vtwE c i : K)) * ((z : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        diagonal (fun i => (vtwE c i : K)⁻¹) := by
    have e : (z' : GL (Fin 6) K) =
        diagGL K 6 (vtwE c) * (z : GL (Fin 6) K) * (diagGL K 6 (vtwE c))⁻¹ := by
      change P⁻¹ * ((P * diagGL K 6 (vtwE c) * P⁻¹) * (y : GL (Fin 6) K) *
          (P * diagGL K 6 (vtwE c) * P⁻¹)⁻¹) * P =
        diagGL K 6 (vtwE c) * (P⁻¹ * (y : GL (Fin 6) K) * P) * (diagGL K 6 (vtwE c))⁻¹
      group
    rw [e, Units.val_mul, Units.val_mul, coe_diagGL, ← map_inv, coe_diagGL]
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  change rootDiagUnit Tag.E6 (vtwBa c) * ((liftA K (conjSU (unitaryInvolution K ℓ f) hζ z) :
      groupA K) : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 (vtwBa c))⁻¹ =
    ((liftA K (conjSU (unitaryInvolution K ℓ f) hζ z') : groupA K) : ModGL Tag.E6 K)
  rw [vtwD_conj_liftA, conjDiag_conjSU _ _ hζ hz']

end DLevi

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Vtw

end
