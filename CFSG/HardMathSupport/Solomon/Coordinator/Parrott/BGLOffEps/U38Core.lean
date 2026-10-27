module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Check
public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38Lift
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8Sound
public import Certificates.Certificate188005

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

section Transfer

theorem toMat_msig (ι : Q8 →+* F) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 4) (A : M3 Q8) :
    toMat ι (msig A) = (toMat ι A).map σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, msig, M3.map, q4_eq, hσ]

theorem toMat_mstar (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F) (A : M3 Q8) :
    toMat ι (mstar A) = ((toMat ι A).map h.bar)ᵀ := by
  have e : A.map q8p = A.map (· ^ (2 ^ 3)) := by
    congr 1
    funext x
    rw [q8p_eq]
    norm_num
  rw [mstar, e, toMat_transpose_map h ι A]

theorem toMat_mpow (ι : Q8 →+* F) (Y : M3 Q8) (n : ℕ) :
    toMat ι (mpow Y n) = toMat ι Y ^ n := by
  induction n with
  | zero => exact toMat_one ι
  | succ n ih => rw [mpow, toMat_mul, ih, pow_succ]

theorem pow_three_of_mem_mu3 {l : Q8} (hl : l ∈ mu3) : l ^ 3 = 1 := by
  simp only [mu3, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl
  · exact one_pow 3
  · exact QExt.omega_pow_three
  · rw [mul_pow, QExt.omega_pow_three, one_mul]

theorem exists_scalar_of_cube (h : UnitaryFieldData 2 3 F) {c : F} (hc : c ^ 3 = 1) :
    ∃ z ∈ unitaryScalars h 3, ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  set u : Fˣ := Units.mk0 c hc0 with hu
  have hn : h.norm (u : F) = 1 := by
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, Units.val_mk0]
    calc c * c ^ 2 ^ 3 = (c ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hc, one_pow]
  have hu3 : u ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hc]; rfl)
  refine ⟨⟨_, scalar_mem_unitarySU h (by norm_num) hn hu3⟩, ⟨u, hn, hu3, rfl⟩, ?_⟩
  change ((GeneralLinearGroup.scalar (Fin 3) u : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = _
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.smul_one_eq_diagonal]
  rfl

@[expose] def IsMatIn (Q : Subgroup (unitarySU 2 3 F 3)) (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ g ∈ Q, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = M

theorem isMatIn_one (Q : Subgroup (unitarySU 2 3 F 3)) : IsMatIn Q 1 := ⟨1, Q.one_mem, rfl⟩

theorem isMatIn_mul {Q : Subgroup (unitarySU 2 3 F 3)} {A B : Matrix (Fin 3) (Fin 3) F}
    (hA : IsMatIn Q A) (hB : IsMatIn Q B) : IsMatIn Q (A * B) := by
  obtain ⟨g, hg, rfl⟩ := hA
  obtain ⟨g', hg', rfl⟩ := hB
  exact ⟨g * g', Q.mul_mem hg hg', rfl⟩

theorem isMatIn_evalW {Q : Subgroup (unitarySU 2 3 F 3)} (ι : Q8 →+* F) {letters : List (M3 Q8)}
    (hl : ∀ x ∈ letters, IsMatIn Q (toMat ι x)) :
    ∀ w : List ℕ, IsMatIn Q (toMat ι (evalW letters w))
  | [] => by simpa [evalW, toMat_one] using isMatIn_one Q
  | i :: w => by
    rw [evalW, toMat_mul]
    refine isMatIn_mul ?_ (isMatIn_evalW ι hl w)
    by_cases hi : i < letters.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact hl _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (not_lt.1 hi), toMat_one]
      exact isMatIn_one Q

theorem isMatIn_of_smul (h : UnitaryFieldData 2 3 F) {Q : Subgroup (unitarySU 2 3 F 3)}
    (hQ : unitaryScalars h 3 ≤ Q) {c : F} (hc : c ^ 3 = 1) {M : Matrix (Fin 3) (Fin 3) F}
    (hM : IsMatIn Q (c • M)) : IsMatIn Q M := by
  obtain ⟨g, hg, hgM⟩ := hM
  obtain ⟨z, hz, hzc⟩ := exists_scalar_of_cube h hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    norm_num at hc
  refine ⟨z⁻¹ * g, Q.mul_mem (Q.inv_mem (hQ hz)) hg, ?_⟩
  have h1 : ((z⁻¹ : unitarySU 2 3 F 3) : GL (Fin 3) F) * (z : GL (Fin 3) F) = 1 := by
    rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one]
  have h2 : (((z⁻¹ : unitarySU 2 3 F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      c⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have h3 : (((z⁻¹ : unitarySU 2 3 F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (c • (1 : Matrix (Fin 3) (Fin 3) F)) = 1 := by
      rw [← hzc, ← Units.val_mul, h1, Units.val_one]
    calc (((z⁻¹ : unitarySU 2 3 F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
        = (((z⁻¹ : unitarySU 2 3 F 3) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            (c • (1 : Matrix (Fin 3) (Fin 3) F)) * (c⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F)) := by
          rw [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc0,
            one_smul, Matrix.mul_one]
      _ = c⁻¹ • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [h3, Matrix.one_mul]
  rw [Subgroup.coe_mul, Units.val_mul, h2, hgM, Matrix.smul_mul, Matrix.one_mul, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

theorem heisB12_le_of_isMatIn (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F)
    (hι : Function.Surjective ι) {Q : Subgroup (unitarySU 2 3 F 3)} {letters : List (M3 Q8)}
    {ws₂ : List (List ℕ)} (hl : ∀ x ∈ letters, IsMatIn Q (toMat ι x))
    (hcov : CoverOk (2 ^ 3) (ws₂.map (evalW letters))) : heisB12 2 3 F ≤ Q := by
  have hL2 : ∀ x ∈ ws₂.map (evalW letters), IsMatIn Q (toMat ι x) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact isMatIn_evalW ι hl w
  intro g hg
  obtain ⟨A, hA, hgA⟩ := mem_heisB12.1 hg
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).1 hA
  obtain ⟨e10, e11, enorm⟩ := su2_entries h hdet hu
  obtain ⟨a, ha⟩ := hι ((A : Matrix (Fin 2) (Fin 2) F) 0 0)
  obtain ⟨b, hb⟩ := hι ((A : Matrix (Fin 2) (Fin 2) F) 0 1)
  have hn : a * a ^ 2 ^ 3 + b * b ^ 2 ^ 3 = 1 := by
    apply ι.injective
    simp only [map_add, map_mul, map_pow, ha, hb, enorm, map_one]
  obtain ⟨g', hg', hgg⟩ := hL2 _ (hcov a b hn)
  have hmat : toMat ι (blockM3 (2 ^ 3) a b) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hgA]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMat, blockM3, ha, hb, e10, e11]
  have : g' = g := Subtype.ext (Units.ext (hgg.trans hmat))
  exact this ▸ hg'

theorem fixedSub_of_fixOk (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F) {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c ^ 4) {Y : M3 Q8} (Yu : unitaryIsom3 h)
    (hYu : ((Yu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι Y)
    (hYfix : glAut σ (Yu : GL (Fin 3) F) = Yu) (t : ℕ) {A : M3 Q8} (g : unitarySU 2 3 F 3)
    (hg : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι A)
    (hA : ∃ l ∈ mu3, mpow Y t * msig A = M3.smul l (A * mpow Y t)) :
    unitaryProj h 3 g ∈ fixSubgroup (psuField h σ * psuConj h Yu ^ t) := by
  obtain ⟨l, hl, he⟩ := hA
  have hl3 : (ι l) ^ 3 = 1 := by rw [← map_pow, pow_three_of_mem_mu3 hl, map_one]
  obtain ⟨z, hz, hzc⟩ := exists_scalar_of_cube h hl3
  have hY'm : ((((Yu ^ t : unitaryIsom3 h) : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) =
      toMat ι (mpow Y t) := by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hYu, toMat_mpow]
  have hY'fix : glAut σ ((Yu ^ t : unitaryIsom3 h) : GL (Fin 3) F) =
      ((Yu ^ t : unitaryIsom3 h) : GL (Fin 3) F) := by
    rw [Subgroup.coe_pow, map_pow, hYfix]
  have hkey : ((Yu ^ t : unitaryIsom3 h) : GL (Fin 3) F) * glAut σ (g : GL (Fin 3) F) =
      (z : GL (Fin 3) F) * (g : GL (Fin 3) F) * ((Yu ^ t : unitaryIsom3 h) : GL (Fin 3) F) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_glAut, hg, hY'm, hzc,
      ← toMat_msig ι hσ, ← toMat_mul, he, toMat_smul, toMat_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.smul_mul]
  have hw : suField h σ (suConj h (Yu ^ t) g) = z * g := by
    apply Subtype.ext
    rw [coe_suField, coe_suConj, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv,
      hY'fix, hkey, mul_inv_cancel_right]
  rw [mem_fixSubgroup, ← map_pow, MulAut.mul_apply]
  change psuField h σ (psuConj h (Yu ^ t) (g : unitaryPSU h 3)) = (g : unitaryPSU h 3)
  rw [psuConj_mk, psuField_mk, hw, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff z).2 hz, one_mul]

end Transfer

section Core


theorem top_le_fixJoin_of_check (h : UnitaryFieldData 2 3 F) (ι : Q8 →+* F)
    (hι : Function.Surjective ι) {σ : F ≃+* F} (hσ : ∀ c, σ c = c ^ 4) {D : LiftData}
    (hD : D.check = true) (Yu : unitaryIsom3 h)
    (hYu : ((Yu : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι D.Y) :
    (⊤ : Subgroup (unitaryPSU h 3)) ≤ fixJoin (psuField h σ) (psuConj h Yu) := by
  classical
  obtain ⟨-, hYsig, hpairs, htargets⟩ := LiftData.check_spec hD
  have hYfix : glAut σ (Yu : GL (Fin 3) F) = Yu := by
    apply Units.ext
    rw [coe_glAut, hYu, ← toMat_msig ι hσ, hYsig]
  set J := fixJoin (psuField h σ) (psuConj h Yu) with hJ
  set Q : Subgroup (unitarySU 2 3 F 3) := J.comap (unitaryProj h 3) with hQ
  have hscal : unitaryScalars h 3 ≤ Q := by
    intro z hz
    show unitaryProj h 3 z ∈ J
    have : unitaryProj h 3 z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [this]
    exact J.one_mem
  have hsu : ∀ A : M3 Q8, A.det = 1 → mstar A * A = 1 →
      ∃ g : unitarySU 2 3 F 3, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι A := by
    intro A hd hu
    refine CFSG.RankThree.PartTwo.Sec19.U38F.exists_su_of_matrix h
      (by rw [toMat_det, hd, map_one]) ?_
    rw [← toMat_mstar h ι, ← toMat_mul, hu, toMat_one]
  have hcomm : ∀ (A B : M3 Q8) (ga gb : unitarySU 2 3 F 3),
      ((ga : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι A →
      ((gb : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = toMat ι B →
      ⁅ga, gb⁆ ∈ Q → IsMatIn Q (toMat ι (comm A B)) := by
    intro A B ga gb hga hgb hc
    refine ⟨⁅ga, gb⁆, hc, ?_⟩
    rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Units.val_mul, Units.val_mul, Units.val_mul, CFSG.LieType.SeitzGeneration.val_inv_eq_star h,
      CFSG.LieType.SeitzGeneration.val_inv_eq_star h, hga, hgb, comm, toMat_mul, toMat_mul,
      toMat_mul, toMat_mstar h ι, toMat_mstar h ι]
  have hgen : ∀ G ∈ D.gens, IsMatIn Q (toMat ι G) := by
    intro G hG
    simp only [LiftData.gens, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hG
    obtain ⟨p, hp, hGp⟩ := hG
    obtain ⟨ht, ⟨hda, hua⟩, ⟨hdb, hub⟩, hfa, hfb⟩ := hpairs p hp
    obtain ⟨ga, hga⟩ := hsu _ hda hua
    obtain ⟨gb, hgb⟩ := hsu _ hdb hub
    have hfa' := fixedSub_of_fixOk h ι hσ Yu hYu hYfix p.1 ga hga hfa
    have hfb' := fixedSub_of_fixOk h ι hσ Yu hYu hYfix p.1 gb hgb hfb
    have hmem : ∀ x y : unitarySU 2 3 F 3,
        unitaryProj h 3 x ∈ fixSubgroup (psuField h σ * psuConj h Yu ^ p.1) →
        unitaryProj h 3 y ∈ fixSubgroup (psuField h σ * psuConj h Yu ^ p.1) → ⁅x, y⁆ ∈ Q := by
      intro x y hx hy
      show unitaryProj h 3 ⁅x, y⁆ ∈ J
      rw [map_commutatorElement]
      exact le_iSup₂_of_le (f := fun (i : ℕ) (_ : i < 3) =>
        ⁅fixSubgroup (psuField h σ * psuConj h Yu ^ i),
          fixSubgroup (psuField h σ * psuConj h Yu ^ i)⁆) p.1 ht le_rfl
        (Subgroup.commutator_mem_commutator hx hy)
    rcases hGp with rfl | rfl
    · exact hcomm _ _ ga gb hga hgb (hmem ga gb hfa' hfb')
    · exact hcomm _ _ gb ga hgb hga (hmem gb ga hfb' hfa')
  have htarg : ∀ T ∈ targets, IsMatIn Q (toMat ι T) := by
    intro T hT
    obtain ⟨wl, -, hl, he⟩ := htargets T hT
    have h1 := isMatIn_evalW ι hgen wl.1
    rw [he, toMat_smul] at h1
    have hl3 : (ι wl.2) ^ 3 = 1 := by rw [← map_pow, pow_three_of_mem_mu3 hl, map_one]
    exact isMatIn_of_smul h hscal hl3 h1
  have hcov : CoverOk (2 ^ 3) (words2_8.map (evalW outerLetters8)) :=
    of_decide_eq_true
      (CFSG.RankThree.PartTwo.Sec19.U38F.u38Check_parts Certificates.certificate188005).2.1
  have hB : heisB12 2 3 F ≤ Q := heisB12_le_of_isMatIn h ι hι
    (fun x hx => htarg x (List.mem_append_left _ hx)) hcov
  obtain ⟨s, hs, hsm⟩ := htarg sM3 (List.mem_append_right _ (List.mem_singleton_self _))
  rw [toMat_sM3] at hsm
  have hQtop : Q = ⊤ := eq_top_of_shift_of_heisB12_le h (by norm_num) hsm hs hB
  intro z _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 z
  have hg : g ∈ Q := hQtop ▸ Subgroup.mem_top g
  exact hg

end Core

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.U38
