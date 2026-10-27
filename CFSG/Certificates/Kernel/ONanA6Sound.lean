
module

public import Certificates.Data.Kernel.ONanA6
public import CFSG.Certificates.Kernel.LocalQTSmallSound
public import CFSG.LocalAnalysis.OddStandard.ONanB2A6FactsBase
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate113

public section

namespace CFSG.KC.ONanA6

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.QuasithinUnique CFSG.OddStandard.ONanRec.A6C

local notation "P10" => A6Facts.P10

theorem h10 : (10 : ℕ) ≤ 32 := by norm_num

theorem I10_eq : I10 = code (1 : P10) := by
  rw [← code_one]
  decide +kernel

theorem codeL_code (x : P10) : S.codeL (A6Facts.code x) = code x := by
  rw [S.codeL_eq, A6Facts.code_length, code_eq]
  refine E_congr fun i hi => ?_
  exact (A6Facts.code_getD x ⟨i, hi⟩).trans (vals_fin x ⟨i, hi⟩).symm

theorem codeL_comp : S.codeL ∘ A6Facts.code = (code : P10 → ℕ) := by
  funext x
  rw [Function.comp_apply]
  exact codeL_code x

theorem nonEmpty_iff (l : List ℕ) : nonEmpty l = true ↔ l ≠ [] := by
  cases l
  · exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd rfl h⟩
  · exact ⟨fun _ => List.cons_ne_nil _ _, fun _ => rfl⟩

theorem rec_cons_eq (y : ℕ) (R base : List ℕ) :
    List.rec (motive := fun _ => List ℕ) base (fun r _ ih2 => List.cons (mul 10 y r) ih2) R =
      R.map (mul 10 y) ++ base := by
  induction R with
  | nil => rfl
  | cons r R ih => exact congrArg (List.cons (mul 10 y r)) ih

theorem prodL_eq (L R : List ℕ) : prodL L R = L.flatMap fun y => R.map (mul 10 y) := by
  induction L with
  | nil => rfl
  | cons y L ih =>
    change List.rec (motive := fun _ => List ℕ) (prodL L R)
      (fun r _ ih2 => List.cons (mul 10 y r) ih2) R = _
    rw [rec_cons_eq, ih, List.flatMap_cons]

theorem zipAll_mem {f : ℕ → ℕ → Bool} : ∀ {L G : List ℕ}, zipAll L G f = true →
    ∀ x ∈ L, ∃ g, f x g = true
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | y :: L, [], h, _, _ => absurd h Bool.false_ne_true
  | y :: L, g :: G, h, x, hx => by
    change andB (f y g) (zipAll L G f) = true at h
    rw [andB_iff] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨g, h.1⟩
    · exact zipAll_mem h.2 x hx

theorem mem_lc {lc : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc) (x : P10) :
    code x ∈ lc ↔ x ∈ A6Models.psl29 := by
  subst hl
  rw [List.mem_map, A6Facts.mem_psl29_iff]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain ⟨y, hy, rfl⟩ := A6Facts.exists_psl29_of_code hc
    rw [codeL_code] at he
    rw [← code_inj h10 he]
    exact (A6Facts.mem_psl29_iff y).1 hy
  · exact fun h => ⟨_, h, codeL_code x⟩

theorem of_mem_lc {lc : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc) {c : ℕ} (hc : c ∈ lc) :
    ∃ x ∈ A6Models.psl29, code x = c := by
  subst hl
  obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
  obtain ⟨y, hy, rfl⟩ := A6Facts.exists_psl29_of_code hc'
  exact ⟨y, hy, (codeL_code y).symm⟩

theorem reps_mem {r : P10} (hr : r ∈ A6Facts.autRepsP) : r ∈ A6Models.autA6 := by
  rw [A6Facts.autA6_eq]
  exact A6Facts.autReps_mem_closure r hr

theorem mem_la {lc rc la : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc)
    (hr : A6Facts.Core.autReps.map S.codeL = rc) (hla : la = prodL lc rc) {x : P10}
    (hx : x ∈ A6Models.autA6) : code x ∈ la := by
  obtain ⟨r, hr', hxr⟩ := (A6Facts.mem_autA6_iff_exists x).1 hx
  have e : code x = mul 10 (code (x * r⁻¹)) (code r) := by
    rw [code_mul h10, inv_mul_cancel_right]
  rw [hla, e, prodL_eq, List.mem_flatMap]
  refine ⟨_, (mem_lc hl _).2 hxr, List.mem_map_of_mem ?_⟩
  subst hr
  rw [← A6Facts.autRepsP_code, List.map_map, codeL_comp]
  exact List.mem_map_of_mem hr'

theorem of_mem_autL {c : List ℕ} (hc : c ∈ A6Facts.Core.autL) :
    ∃ b ∈ A6Models.autA6, A6Facts.code b = c := by
  unfold A6Facts.Core.autL at hc
  obtain ⟨y, hy, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨Y, hY, rfl⟩ := A6Facts.exists_psl29_of_code hy
  rw [← A6Facts.autRepsP_code] at hr
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hr
  exact ⟨Y * R, Subgroup.mul_mem _ (A6Facts.psl29_le_autA6 hY) (reps_mem hR),
    A6Facts.code_mul Y R⟩

theorem gc_eq {gc : List ℕ} (hg : A6Facts.Core.pslGenC.map S.codeL = gc) :
    gc = A6Facts.pslGens.map code := by
  subst hg
  rw [← A6Facts.pslGens_code, List.map_map, codeL_comp]

section Map

variable (φ : P10 ≃* P10)

theorem PC_map (u r : P10) : PC (φ u) (φ r) ↔ PC u r := by
  simp only [PC, ← map_pow, ← map_mul, MulEquiv.map_eq_one_iff, EmbeddingLike.apply_eq_iff_eq,
    ne_eq]

theorem DC_map (u d : P10) : DC (φ u) (φ d) ↔ DC u d := by
  simp only [DC, ← map_pow, ← map_mul, MulEquiv.map_eq_one_iff, ne_eq]

theorem pEltP_map (u r : P10) (i j : ℕ) : pEltP (φ u) (φ r) i j = φ (pEltP u r i j) := by
  simp only [pEltP, map_mul, map_pow]

theorem eOfP_map (u r : P10) : eOfP (φ u) (φ r) = φ (eOfP u r) := by
  simp only [eOfP, map_mul, map_pow]

theorem RelP_map (b d e : P10) : RelP (φ b) (φ d) (φ e) ↔ RelP b d e := by
  simp only [RelP, conjP, ← map_pow, ← map_mul, MulEquiv.map_eq_one_iff]

end Map

theorem conj_mem {g : P10} (H : Subgroup P10) (hg : g ∈ H) (x : P10) :
    MulAut.conj g x ∈ H ↔ x ∈ H := by
  rw [MulAut.conj_apply, Subgroup.mul_mem_cancel_right H (inv_mem hg),
    Subgroup.mul_mem_cancel_left H hg]

theorem bc_all {u b : P10} (hu : u ^ 4 = 1)
    (h : ∀ x ∈ A6Facts.pslGens, b ^ 2 * x = u ^ 2 * x * u ^ 2 * b ^ 2) :
    ∀ x ∈ A6Models.psl29, b ^ 2 * x = u ^ 2 * x * u ^ 2 * b ^ 2 := by
  have hu2 : (u ^ 2)⁻¹ = u ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_add]
    exact hu
  have key : ∀ x, b ^ 2 * x = u ^ 2 * x * u ^ 2 * b ^ 2 ↔
      (MulAut.conj (b ^ 2)).toMonoidHom x = (MulAut.conj (u ^ 2)).toMonoidHom x := by
    intro x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu2]
    rw [mul_inv_eq_iff_eq_mul]
  have hle : A6Models.psl29 ≤
      MonoidHom.eqLocus (MulAut.conj (b ^ 2)).toMonoidHom (MulAut.conj (u ^ 2)).toMonoidHom := by
    rw [A6Facts.psl29_eq, Subgroup.closure_le]
    exact fun x hx => (key x).1 (h x hx)
  exact fun x hx => (key x).2 (hle hx)

theorem pcK_iff (U r : P10) :
    pcK (code U) (code (U * U)) (code (U * U * U)) (code r) = true ↔ PC U r := by
  simp only [pcK, PC, letB_eq, andB_iff, notB_iff, beq_iff, I10_eq, code_mul h10,
    code_eq_iff h10, pow_succ, pow_zero, one_mul, mul_assoc, ne_eq]

theorem dcK_iff (U d : P10) : dcK (code U) (code d) = true ↔ DC U d := by
  simp only [dcK, DC, andB_iff, notB_iff, beq_iff, I10_eq, code_mul h10, code_eq_iff h10,
    pow_succ, pow_zero, one_mul, mul_assoc, ne_eq]

theorem cubeOne_iff (z : P10) : cubeOne (code z) = true ↔ z ^ 3 = 1 := by
  simp only [cubeOne, letB_eq, beq_iff, I10_eq, code_mul h10, code_eq_iff h10, pow_succ,
    pow_zero, one_mul]

@[expose] def nine (u r : P10) : List P10 :=
  [pEltP u r 0 0, pEltP u r 0 1, pEltP u r 0 2, pEltP u r 1 0, pEltP u r 1 1, pEltP u r 1 2,
    pEltP u r 2 0, pEltP u r 2 1, pEltP u r 2 2]

theorem withNine_code (U r : P10) (F : List ℕ → Bool) :
    withNine (code U) (code (U * U * U)) (code r) F = F ((nine U r).map code) := by
  simp only [withNine, letB_eq, code_mul h10, I10_eq]
  congr 1

theorem mem_nine {u r : P10} {i j : ℕ} (hi : i < 3) (hj : j < 3) : pEltP u r i j ∈ nine u r := by
  interval_cases i <;> interval_cases j <;> simp [nine]

theorem nine_map (φ : P10 ≃* P10) (u r : P10) : nine (φ u) (φ r) = (nine u r).map φ := by
  simp only [nine, pEltP_map, List.map_cons, List.map_nil]

theorem nine_eq (u r : P10) : ((List.range 3).flatMap fun i => (List.range 3).map fun j =>
    pElt (A6Facts.code u) (A6Facts.code r) i j) = (nine u r).map A6Facts.code := by
  simp only [pElt_code]
  rfl

theorem eOfK_code (U x : P10) : eOfK (code (U * U)) (code x) = code (eOfP U x) := by
  simp only [eOfK, eOfP, code_mul h10, pow_succ, pow_zero, one_mul]

theorem pow119 {b : P10} (h : b ^ 120 = 1) : b ^ 119 = b⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rwa [← pow_succ])

theorem relK_iff {b : P10} (hb : b ^ 120 = 1) (d e : P10) :
    relK (code b) (code d) (code e) = true ↔ RelP b d e := by
  simp only [RelP, conjP, pow119 hb, relK, letB_eq, code_inv h10, code_mul h10, I10_eq, beq_iff,
    code_eq_iff h10, pow_succ, pow_zero, one_mul, mul_assoc]

theorem bcK_of {gc : List ℕ} (hg : A6Facts.Core.pslGenC.map S.codeL = gc) {U d b : P10}
    (hbc : BC U d b) : bcK gc (code U) (code (U * U)) (code d) (code b) = true := by
  rw [gc_eq hg]
  obtain ⟨-, h2, h3⟩ := hbc
  simp only [bcK, letB_eq, andB_iff, beq_iff, allL_map, code_mul h10, code_eq_iff h10]
  refine ⟨by rw [h2], fun x hx => ?_⟩
  have := h3 x hx
  simp only [pow_succ, pow_zero, one_mul] at this
  exact this

theorem mul_pow_code (b : P10) (m n : ℕ) :
    mul 10 (code (b ^ m)) (code (b ^ n)) = code (b ^ (m + n)) := by
  rw [code_mul h10, pow_add]

theorem expB_iff (b : P10) : expB (code b) = true ↔ b ^ 120 = 1 := by
  have e : code b = code (b ^ 1) := by rw [pow_one]
  rw [e]
  simp only [expB, letB_eq, mul_pow_code, Nat.reduceAdd, I10_eq, beq_iff, code_eq_iff h10]

theorem exp_of {lc rc la : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc)
    (hr : A6Facts.Core.autReps.map S.codeL = rc) (hla : la = prodL lc rc)
    (hExp : cExp la = true) : ∀ b ∈ A6Models.autA6, b ^ 120 = 1 := fun b hb =>
  (expB_iff b).1 ((allL_iff _ _).1 hExp _ (mem_la hl hr hla hb))

theorem ord_of {lc gx : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc) {U : P10}
    (hOrd : cOrd lc gx (code U) = true) : ∀ x ∈ A6Models.psl29,
      (x ^ 6 = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1) ∧ (x ^ 8 = 1 → x ^ 4 = 1) ∧
        (Ord4 x → ∃ g ∈ A6Models.psl29, g * U = x * g) := by
  intro x hx
  obtain ⟨g, h⟩ := zipAll_mem hOrd _ ((mem_lc hl x).2 hx)
  have e : code x = code (x ^ 1) := by rw [pow_one]
  rw [e] at h
  simp only [ordRow, letB_eq, andB_iff, orB_iff, notB_iff, impB_iff, beq_iff, I10_eq,
    mul_pow_code, Nat.reduceAdd, code_eq_iff h10, S.memL_iff] at h
  obtain ⟨h6, h8, h4⟩ := h
  refine ⟨h6, h8, fun ⟨e4, e2⟩ => ?_⟩
  obtain ⟨hgm, hgu⟩ := h4 ⟨e4, e2⟩
  obtain ⟨G, hG, rfl⟩ := of_mem_lc hl hgm
  rw [code_mul h10, code_mul h10, code_eq_iff h10, pow_one] at hgu
  exact ⟨G, hG, hgu⟩

def Facts (U : P10) : Prop :=
  U ∈ A6Models.psl29 ∧ (∀ b ∈ A6Models.autA6, b ^ 120 = 1) ∧
    (∀ x ∈ A6Models.psl29, (x ^ 6 = 1 → x ^ 2 = 1 ∨ x ^ 3 = 1) ∧ (x ^ 8 = 1 → x ^ 4 = 1) ∧
      (Ord4 x → ∃ g ∈ A6Models.psl29, g * U = x * g)) ∧
    (∃ r ∈ A6Models.psl29, PC U r) ∧ (∀ r ∈ A6Models.psl29, PC U r → (nine U r).Nodup) ∧
    (∃ d ∈ A6Models.psl29, DC U d) ∧
    (∀ d ∈ A6Models.psl29, DC U d → ∀ r ∈ A6Models.psl29, PC U r →
      ∃ x ∈ nine U r, (d * eOfP U x) ^ 3 = 1) ∧
    (∀ b ∈ A6Models.autA6,
      (b ≠ 1 → b * U = U * b → ∀ r ∈ A6Models.psl29, PC U r → b * r ≠ r * b) ∧
      (b * U = U ^ 3 * b → ∀ d ∈ A6Models.psl29, DC U d → BC U d b → ∀ r ∈ A6Models.psl29,
        PC U r → ∀ x ∈ nine U r, (d * eOfP U x) ^ 3 = 1 →
          RelP b d (eOfP U x) ∨ RelP (U ^ 2 * b) d (eOfP U x)))

section Parts

variable {lc pcl dsl esl : List ℕ} {U : P10} (hl : A6Facts.Core.pslLit.map S.codeL = lc)

include hl in
theorem pc_of (hPc : cPc lc pcl (code U) (code (U * U)) (code (U * U * U)) = true) :
    (∃ r ∈ A6Models.psl29, PC U r) ∧ ∀ r ∈ A6Models.psl29, PC U r → code r ∈ pcl := by
  rw [cPc, andB_iff, S.eqLs_iff, nonEmpty_iff] at hPc
  obtain ⟨rfl, hne⟩ := hPc
  refine ⟨?_, fun r hr hpc => (S.mem_filtL _ _ _).2 ⟨(mem_lc hl r).2 hr, (pcK_iff U r).2 hpc⟩⟩
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hc1, hc2⟩ := (S.mem_filtL _ _ _).1 hc
  obtain ⟨r, hr, rfl⟩ := of_mem_lc hl hc1
  exact ⟨r, hr, (pcK_iff U r).1 hc2⟩

include hl in
theorem ds_of (hDs : cDs lc dsl (code U) = true) :
    (∃ d ∈ A6Models.psl29, DC U d) ∧ ∀ d ∈ A6Models.psl29, DC U d → code d ∈ dsl := by
  rw [cDs, andB_iff, S.eqLs_iff, nonEmpty_iff] at hDs
  obtain ⟨rfl, hne⟩ := hDs
  refine ⟨?_, fun d hd hdc => (S.mem_filtL _ _ _).2 ⟨(mem_lc hl d).2 hd, (dcK_iff U d).2 hdc⟩⟩
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hc1, hc2⟩ := (S.mem_filtL _ _ _).1 hc
  obtain ⟨d, hd, rfl⟩ := of_mem_lc hl hc1
  exact ⟨d, hd, (dcK_iff U d).1 hc2⟩

end Parts

theorem dist_of {pcl : List ℕ} {U : P10}
    (hpcl : ∀ r ∈ A6Models.psl29, PC U r → code r ∈ pcl)
    (hDist : cDist pcl (code U) (code (U * U * U)) = true) :
    ∀ r ∈ A6Models.psl29, PC U r → (nine U r).Nodup := by
  intro r hr hpc
  have h := (allL_iff _ _).1 hDist _ (hpcl r hr hpc)
  rwa [withNine_code, S.distinctL_map h10] at h

theorem es_of {pcl esl : List ℕ} {U : P10}
    (hpcl : ∀ r ∈ A6Models.psl29, PC U r → code r ∈ pcl)
    (hEs : cEs pcl esl (code U) (code (U * U)) (code (U * U * U)) = true) :
    ∀ r ∈ A6Models.psl29, PC U r → ∀ x ∈ nine U r, code (eOfP U x) ∈ esl := by
  intro r hr hpc x hx
  have h := (allL_iff _ _).1 hEs _ (hpcl r hr hpc)
  rw [withNine_code, allL_map] at h
  have := h x hx
  rwa [eOfK_code, S.memL_iff] at this

theorem relA_of {pcl dsl : List ℕ} {U : P10}
    (hpcl : ∀ r ∈ A6Models.psl29, PC U r → code r ∈ pcl)
    (hdsl : ∀ d ∈ A6Models.psl29, DC U d → code d ∈ dsl)
    (hRelA : cRelA pcl dsl (code U) (code (U * U)) (code (U * U * U)) = true) :
    ∀ d ∈ A6Models.psl29, DC U d → ∀ r ∈ A6Models.psl29, PC U r →
      ∃ x ∈ nine U r, (d * eOfP U x) ^ 3 = 1 := by
  intro d hd hdc r hr hpc
  have h := (allL_iff _ _).1 ((allL_iff _ _).1 hRelA _ (hdsl d hd hdc)) _ (hpcl r hr hpc)
  rw [withNine_code, anyL_map] at h
  obtain ⟨x, hx, h⟩ := h
  rw [eOfK_code, code_mul h10, cubeOne_iff] at h
  exact ⟨x, hx, h⟩

theorem fix_of {lc rc gc la pcl dsl esl : List ℕ} (hl : A6Facts.Core.pslLit.map S.codeL = lc)
    (hr : A6Facts.Core.autReps.map S.codeL = rc) (hg : A6Facts.Core.pslGenC.map S.codeL = gc)
    (hla : la = prodL lc rc) {U : P10} (hU0 : U ∈ A6Models.psl29)
    (F1 : ∀ b ∈ A6Models.autA6, b ^ 120 = 1)
    (hpcl : ∀ r ∈ A6Models.psl29, PC U r → code r ∈ pcl)
    (hdsl : ∀ d ∈ A6Models.psl29, DC U d → code d ∈ dsl)
    (F6 : ∀ r ∈ A6Models.psl29, PC U r → ∀ x ∈ nine U r, code (eOfP U x) ∈ esl)
    (hFix : cFix la pcl gc dsl esl (code U) (code (U * U)) (code (U * U * U)) = true) :
    ∀ b ∈ A6Models.autA6,
      (b ≠ 1 → b * U = U * b → ∀ r ∈ A6Models.psl29, PC U r → b * r ≠ r * b) ∧
      (b * U = U ^ 3 * b → ∀ d ∈ A6Models.psl29, DC U d → BC U d b → ∀ r ∈ A6Models.psl29,
        PC U r → ∀ x ∈ nine U r, (d * eOfP U x) ^ 3 = 1 →
          RelP b d (eOfP U x) ∨ RelP (U ^ 2 * b) d (eOfP U x)) := by
    intro b hb
    have h := (allL_iff _ _).1 hFix _ (mem_la hl hr hla hb)
    simp only [fixK, relBK, letB_eq, andB_iff, impB_iff, notB_iff, beq_iff, I10_eq,
      code_mul h10, code_eq_iff h10, allL_iff] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hb1 hbu r hr hpc e => ?_, fun hbu d hd hdc hbc r hr hpc x hx hde => ?_⟩
    · have := h1 ⟨hb1, hbu⟩ _ (hpcl r hr hpc)
      rw [code_mul h10, code_mul h10, code_eq_iff h10] at this
      exact this e
    · have hbu' : b * U = U * U * U * b := by
        rw [hbu, pow_succ, pow_succ, pow_one]
      have h3 := h2 hbu' _ (hdsl d hd hdc) (bcK_of hg hbc) _ (F6 r hr hpc x hx)
      rw [code_mul h10, cubeOne_iff, orB_iff] at h3
      have hub : U * U * b ∈ A6Models.autA6 :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (A6Facts.psl29_le_autA6 hU0)
          (A6Facts.psl29_le_autA6 hU0)) hb
      rw [relK_iff (F1 b hb), relK_iff (F1 _ hub), ← sq] at h3
      exact h3 hde

theorem facts_of_check {lc rc gc la gx pcl dsl esl : List ℕ} {u0 u2 u3 : ℕ}
    (hl : A6Facts.Core.pslLit.map S.codeL = lc) (hr : A6Facts.Core.autReps.map S.codeL = rc)
    (hg : A6Facts.Core.pslGenC.map S.codeL = gc) (hu : u0 ∈ lc)
    (hk : c6151 lc rc gc la gx pcl dsl esl u0 u2 u3 = true) : ∃ U, Facts U := by
  rw [c6151, S.allBs_cons, S.allBs_cons, S.allBs_cons, S.allBs_cons, S.allBs_cons,
    S.allBs_cons, S.allBs_cons, S.allBs_cons, S.allBs_cons, S.allBs_cons, S.allBs_nil] at hk
  simp only [andB_iff] at hk
  obtain ⟨hAut, hExp, hOrd, hU, hPc, hDist, hDs, hEs, hRelA, hFix, -⟩ := hk
  obtain ⟨U, hU0, rfl⟩ := of_mem_lc hl hu
  rw [cU, andB_iff, andB_iff, beq_iff, beq_iff, beq_iff] at hU
  obtain ⟨-, h2, h3⟩ := hU
  rw [code_mul h10] at h2
  rw [h2, code_mul h10] at h3
  rw [h2] at hPc hEs hRelA hFix
  rw [h3] at hPc hDist hEs hRelA hFix
  have hla : la = prodL lc rc := (S.eqLs_iff _ _).1 hAut
  have F1 := exp_of hl hr hla hExp
  obtain ⟨F3, hpcl⟩ := pc_of hl hPc
  obtain ⟨F5, hdsl⟩ := ds_of hl hDs
  exact ⟨U, hU0, F1, ord_of hl hOrd, F3, dist_of hpcl hDist, F5, relA_of hpcl hdsl hRelA,
    fix_of hl hr hg hla hU0 F1 hpcl hdsl (es_of hpcl hEs) hFix⟩

theorem mirror_of_facts {U : P10} (hF : Facts U) : a6MirrorCheck = true := by
  obtain ⟨-, F1, F2, F3, F4, F5, F7, F8⟩ := hF
  have hconj : ∀ x ∈ A6Models.psl29, Ord4 x → ∃ φ : P10 ≃* P10, φ U = x ∧
      (∀ y, φ y ∈ A6Models.psl29 ↔ y ∈ A6Models.psl29) ∧
      (∀ y, φ y ∈ A6Models.autA6 ↔ y ∈ A6Models.autA6) := by
    intro x hx h4
    obtain ⟨g, hg', hgU⟩ := (F2 x hx).2.2 h4
    refine ⟨MulAut.conj g, ?_, conj_mem _ hg', conj_mem _ (A6Facts.psl29_le_autA6 hg')⟩
    rw [MulAut.conj_apply, hgU, mul_inv_cancel_right]
  have hpre : ∀ φ : P10 ≃* P10, ∀ y : P10, ∃ y0, φ y0 = y :=
    fun φ y => ⟨φ.symm y, φ.apply_symm_apply y⟩
  simp only [a6MirrorCheck, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [a6ExpCheck, List.all_eq_true]
    intro c hc
    obtain ⟨b, hb, rfl⟩ := of_mem_autL hc
    rw [← A6Facts.code_pow, beq_code_cid]
    exact F1 b hb
  ·
    rw [a6OrdCheck, List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', ← A6Facts.code_pow,
      beq_code_cid, beq_code_cid_false]
    obtain ⟨h6, h8, -⟩ := F2 x hx
    refine ⟨?_, ?_⟩
    · by_cases e : x ^ 6 = 1
      · rcases h6 e with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · exact Or.inl (Or.inl e)
    · by_cases e : x ^ 8 = 1
      · exact Or.inr (h8 e)
      · exact Or.inl e
  ·
    rw [a6SylCheck, List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h4 : Ord4 x
    · right
      obtain ⟨φ, rfl, hφ, -⟩ := hconj x hx h4
      obtain ⟨r, hr, hpc⟩ := F3
      exact List.any_eq_true.2 ⟨_, (A6Facts.mem_psl29_iff _).1 ((hφ r).2 hr),
        (pCond_code _ _).2 ((PC_map φ U r).2 hpc)⟩
    · left
      rw [← Bool.not_eq_true, ord4_code]
      exact h4
  ·
    rw [a6DistCheck, List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h4 : Ord4 x
    · right
      obtain ⟨φ, rfl, hφ, -⟩ := hconj x hx h4
      rw [List.all_eq_true]
      intro c' hc'
      obtain ⟨r, hr, rfl⟩ := A6Facts.exists_psl29_of_code hc'
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hpc : PC (φ U) r
      · right
        obtain ⟨r0, rfl⟩ := hpre φ r
        rw [PC_map] at hpc
        rw [decide_eq_true_eq, nine_eq, nine_map]
        exact ((F4 r0 ((hφ r0).1 hr) hpc).map φ.injective).map A6Facts.code_injective
      · left
        rw [← Bool.not_eq_true, pCond_code]
        exact hpc
    · left
      rw [← Bool.not_eq_true, ord4_code]
      exact h4
  ·
    rw [a6InvCheck, List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h4 : Ord4 x
    · right
      obtain ⟨φ, rfl, hφ, -⟩ := hconj x hx h4
      obtain ⟨d, hd, hdc⟩ := F5
      exact List.any_eq_true.2 ⟨_, (A6Facts.mem_psl29_iff _).1 ((hφ d).2 hd),
        (dCond_code _ _).2 ((DC_map φ U d).2 hdc)⟩
    · left
      rw [← Bool.not_eq_true, ord4_code]
      exact h4
  ·
    rw [a6FixCheck, List.all_eq_true]
    intro c hc
    obtain ⟨b, hb, rfl⟩ := of_mem_autL hc
    rw [Bool.or_eq_true]
    by_cases hb1 : b = 1
    · left
      exact (beq_code_cid b).2 hb1
    right
    rw [List.all_eq_true]
    intro c' hc'
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc'
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hxb : Ord4 x ∧ b * x = x * b
    · right
      obtain ⟨φ, rfl, hφ, hφa⟩ := hconj x hx hxb.1
      obtain ⟨b0, rfl⟩ := hpre φ b
      rw [List.all_eq_true]
      intro c'' hc''
      obtain ⟨r, hr, rfl⟩ := A6Facts.exists_psl29_of_code hc''
      obtain ⟨r0, rfl⟩ := hpre φ r
      rw [Bool.not_eq_true', Bool.eq_false_iff, Ne, Bool.and_eq_true, pCond_code,
        ← A6Facts.code_mul, ← A6Facts.code_mul, OddStandard.ONanRec.A6C.beq_code, PC_map,
        ← map_mul, ← map_mul,
        EmbeddingLike.apply_eq_iff_eq]
      rintro ⟨hpc, hbr⟩
      have hbu := hxb.2
      rw [← map_mul, ← map_mul, EmbeddingLike.apply_eq_iff_eq] at hbu
      have hb01 : b0 ≠ 1 := fun e => hb1 (by rw [e, map_one])
      exact (F8 b0 ((hφa b0).1 hb)).1 hb01 hbu r0 ((hφ r0).1 hr) hpc hbr
    · left
      rw [Bool.eq_false_iff, Ne, Bool.and_eq_true, ord4_code, ← A6Facts.code_mul,
        ← A6Facts.code_mul, OddStandard.ONanRec.A6C.beq_code]
      exact hxb
  ·
    rw [a6RelCheck, List.all_eq_true]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := A6Facts.exists_psl29_of_code hc
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h4 : Ord4 x
    swap
    · left
      rw [← Bool.not_eq_true, ord4_code]
      exact h4
    right
    obtain ⟨φ, rfl, hφ, hφa⟩ := hconj x hx h4
    rw [List.all_eq_true]
    intro c' hc'
    obtain ⟨d, hd, rfl⟩ := A6Facts.exists_psl29_of_code hc'
    rw [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hdc : DC (φ U) d
    swap
    · left
      rw [← Bool.not_eq_true, dCond_code]
      exact hdc
    right
    obtain ⟨d0, rfl⟩ := hpre φ d
    rw [DC_map] at hdc
    have hd0 := (hφ d0).1 hd
    rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    constructor
    · intro c'' hc''
      obtain ⟨r, hr, rfl⟩ := A6Facts.exists_psl29_of_code hc''
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hpc : PC (φ U) r
      swap
      · left
        rw [← Bool.not_eq_true, pCond_code]
        exact hpc
      right
      obtain ⟨r0, rfl⟩ := hpre φ r
      rw [PC_map] at hpc
      obtain ⟨y, hy, hde⟩ := F7 d0 hd0 hdc r0 ((hφ r0).1 hr) hpc
      simp only [nine, List.mem_cons, List.not_mem_nil, or_false] at hy
      have key : ∀ i < 3, ∀ j < 3, y = pEltP U r0 i j →
          List.any (List.range 3) (fun i => List.any (List.range 3) fun j =>
            A6Facts.Core.cpow (A6Facts.Core.cmul (A6Facts.code (φ d0)) (eOf (A6Facts.code (φ U))
              (pElt (A6Facts.code (φ U)) (A6Facts.code (φ r0)) i j))) 3 ==
                A6Facts.Core.cid) = true := by
        intro i hi j hj hyij
        refine List.any_eq_true.2 ⟨i, List.mem_range.2 hi, List.any_eq_true.2
          ⟨j, List.mem_range.2 hj, ?_⟩⟩
        rw [pElt_code, eOf_code, ← A6Facts.code_mul, ← A6Facts.code_pow, beq_code_cid,
          pEltP_map, eOfP_map, ← map_mul, ← map_pow, MulEquiv.map_eq_one_iff, ← hyij]
        exact hde
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact key 0 (by norm_num) 0 (by norm_num) rfl
      · exact key 0 (by norm_num) 1 (by norm_num) rfl
      · exact key 0 (by norm_num) 2 (by norm_num) rfl
      · exact key 1 (by norm_num) 0 (by norm_num) rfl
      · exact key 1 (by norm_num) 1 (by norm_num) rfl
      · exact key 1 (by norm_num) 2 (by norm_num) rfl
      · exact key 2 (by norm_num) 0 (by norm_num) rfl
      · exact key 2 (by norm_num) 1 (by norm_num) rfl
      · exact key 2 (by norm_num) 2 (by norm_num) rfl
    · intro c'' hc''
      obtain ⟨b, hb, rfl⟩ := of_mem_autL hc''
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hbc : BC (φ U) (φ d0) b
      swap
      · left
        rw [← Bool.not_eq_true, bCond_code]
        exact hbc
      right
      obtain ⟨b0, rfl⟩ := hpre φ b
      have hb0 := (hφa b0).1 hb
      have hbc0 : BC U d0 b0 := by
        obtain ⟨h1, h2, h3⟩ := hbc
        have hall := bc_all h4.1 h3
        simp only [← map_pow, ← map_mul, EmbeddingLike.apply_eq_iff_eq] at h1 h2
        refine ⟨h1, h2, fun y hy => ?_⟩
        have hy' : y ∈ A6Models.psl29 := by
          rw [A6Facts.psl29_eq]
          exact Subgroup.subset_closure hy
        have := hall (φ y) ((hφ y).2 hy')
        simpa only [← map_pow, ← map_mul, EmbeddingLike.apply_eq_iff_eq] using this
      rw [List.all_eq_true]
      intro c3 hc3
      obtain ⟨r, hr, rfl⟩ := A6Facts.exists_psl29_of_code hc3
      rw [Bool.or_eq_true, Bool.not_eq_true']
      by_cases hpc : PC (φ U) r
      swap
      · left
        rw [← Bool.not_eq_true, pCond_code]
        exact hpc
      right
      obtain ⟨r0, rfl⟩ := hpre φ r
      rw [PC_map] at hpc
      have hr0 := (hφ r0).1 hr
      rw [List.all_eq_true]
      intro i hi
      rw [List.all_eq_true]
      intro j hj
      have hi' := List.mem_range.1 hi
      have hj' := List.mem_range.1 hj
      rw [Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true', pElt_code, eOf_code,
        ← A6Facts.code_mul, ← A6Facts.code_pow, beq_code_cid_false, ← A6Facts.code_pow,
        ← A6Facts.code_mul, relG_code, relG_code, pEltP_map, eOfP_map, ← map_mul, ← map_pow,
        ← map_pow, ← map_mul, RelP_map, RelP_map, Ne, MulEquiv.map_eq_one_iff]
      by_cases hde : (d0 * eOfP U (pEltP U r0 i j)) ^ 3 = 1
      · rcases (F8 b0 hb0).2 hbc0.1 d0 hd0 hdc hbc0 r0 hr0 hpc _ (mem_nine hi' hj') hde with
          h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · left
        left
        exact hde

theorem s6151 {lc rc gc la gx pcl dsl esl : List ℕ} {u0 u2 u3 : ℕ}
    (hl : A6Facts.Core.pslLit.map S.codeL = lc) (hr : A6Facts.Core.autReps.map S.codeL = rc)
    (hg : A6Facts.Core.pslGenC.map S.codeL = gc) (hu : u0 ∈ lc)
    (hk : c6151 lc rc gc la gx pcl dsl esl u0 u2 u3 = true) : a6MirrorCheck = true :=
  (facts_of_check hl hr hg hu hk).elim fun _ hF => mirror_of_facts hF

end CFSG.KC.ONanA6

end
