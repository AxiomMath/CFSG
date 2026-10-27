
module

public import CFSG.Certificates.Kernel.L34Cov.AlphaSound
public import CFSG.Certificates.Kernel.L34Cov.CodesSound
public import Certificates.Data.Kernel.L34Cov.Alpha

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.Fischer
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts
open Subgroup

theorem bindB_eq (y : ℕ) (k : ℕ → Bool) : bindB y k = k y := by cases y <;> rfl

noncomputable abbrev zc (v : ℕ) : Cover :=
  z₁ ^ (v % 4) * z₂ ^ (v / 4 % 4) * z₃ ^ (v / 16)

theorem zc_mem_center (v : ℕ) : zc v ∈ center Cover :=
  mul_mem (mul_mem (pow_mem z₁_mem_center _) (pow_mem z₂_mem_center _)) (pow_mem z₃_mem_center _)

theorem cv_of_zvOK {V : ℕ} {TA TB : ℕ → ℕ} (hV : vtOK V = true)
    (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1) {w : List (Fin 2 × Bool)} {v : ℕ}
    (h : zvOK V TA TB (w.map letterCode) v = true) : cv w = zc v :=
  cv_eq_of_cvIdOK hV hA hB h

theorem zc_eq_zHom (v : ℕ) :
    zc v = zHom (Multiplicative.ofAdd (v : ZMod 4), Multiplicative.ofAdd ((v / 4 : ℕ) : ZMod 4),
      Multiplicative.ofAdd ((v / 16 : ℕ) : ZMod 3)) := by
  rw [zHom_apply, zc, mul_assoc]
  simp only [toAdd_ofAdd, ZMod.val_natCast]
  rw [pow_eq_pow_mod (v / 16) z₃_pow]

theorem expOf_append (j : Fin 2) (u v : List (Fin 2 × Bool)) :
    expOf j (u ++ v) = expOf j u + expOf j v := by
  rw [expOf, expOf, expOf, List.map_append, List.sum_append]

theorem wpow_succ (u : List (Fin 2 × Bool)) (p : ℕ) : wpow u (p + 1) = wpow u p ++ u := by
  rw [wpow, wpow, List.replicate_succ', List.flatten_append, List.flatten_singleton]

theorem expOf_wpow (j : Fin 2) (u : List (Fin 2 × Bool)) (p : ℕ) :
    expOf j (wpow u p) = p * expOf j u := by
  induction p with
  | zero => simp [wpow, expOf]
  | succ p ih =>
    rw [wpow_succ, expOf_append, ih]
    push_cast
    ring

theorem eN_step (j : Fin 2) (l : Fin 2 × Bool) :
    ((cond (Nat.beq (letterCode l) (Nat.mul 2 j.val)) 1
      (cond (Nat.beq (letterCode l) (Nat.add (Nat.mul 2 j.val) 1)) 11 0) : ℕ) : ℤ) ≡
      (if l.1 = j then (if l.2 then (1 : ℤ) else -1) else 0) [ZMOD 12] := by
  obtain ⟨i, b⟩ := l
  fin_cases j <;> fin_cases i <;> cases b <;> decide

theorem foldl_modEq (j : Fin 2) (w : List (Fin 2 × Bool)) (acc : ℕ) :
    (((w.map letterCode).foldl (fun s c => Nat.add s (cond (Nat.beq c (Nat.mul 2 j.val)) 1
      (cond (Nat.beq c (Nat.add (Nat.mul 2 j.val) 1)) 11 0))) acc : ℕ) : ℤ) ≡
      acc + expOf j w [ZMOD 12] := by
  induction w generalizing acc with
  | nil => simp [expOf]
  | cons l w ih =>
    rw [List.map_cons, List.foldl_cons, expOf_cons]
    refine (ih _).trans ?_
    have := eN_step j l
    push_cast [Nat.add_eq]
    rw [← add_assoc]
    exact Int.ModEq.add_right _ (Int.ModEq.add_left _ this)

theorem eN_modEq (j : Fin 2) (w : List (Fin 2 × Bool)) :
    ((eN j.val (w.map letterCode) : ℕ) : ℤ) ≡ expOf j w [ZMOD 12] := by
  have h := foldl_modEq j w 0
  rw [Nat.cast_zero, zero_add] at h
  rw [eN]
  refine Int.ModEq.trans ?_ h
  push_cast
  exact Int.mod_modEq _ _

theorem comp_one {n : ℕ} (hn : n ∣ 12) {x y z eA eB p : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12])
    (h : n ∣ p * (x + eA * y + eB * z)) :
    (Multiplicative.ofAdd (x : ZMod n)) ^ p * (Multiplicative.ofAdd (y : ZMod n)) ^ ((p : ℤ) * E₀) *
      (Multiplicative.ofAdd (z : ZMod n)) ^ ((p : ℤ) * E₁) = 1 := by
  rw [← ofAdd_nsmul, ← ofAdd_zsmul, ← ofAdd_zsmul, ← ofAdd_add, ← ofAdd_add, ofAdd_eq_one,
    nsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
  obtain ⟨t, ht⟩ := Int.ModEq.dvd h₀
  obtain ⟨s, hs⟩ := Int.ModEq.dvd h₁
  obtain ⟨q, hq⟩ := hn
  have hz : ((((p : ℤ) * x + (p * E₀) * y + (p * E₁) * z) : ℤ) : ZMod n) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hN : (n : ℤ) ∣ (p : ℤ) * (x + eA * y + eB * z) := by exact_mod_cast h
    have e : (p : ℤ) * x + (p * E₀) * y + (p * E₁) * z =
        (p : ℤ) * (x + eA * y + eB * z) + n * (q * (p * t * y + p * s * z)) := by
      have h12 : (12 : ℤ) = n * q := by exact_mod_cast hq
      have eE₀ : E₀ = eA + 12 * t := by linarith
      have eE₁ : E₁ = eB + 12 * s := by linarith
      rw [eE₀, eE₁, h12]
      ring
    rw [e]
    exact dvd_add hN (dvd_mul_right _ _)
  push_cast at hz ⊢
  linear_combination hz

theorem extra_one {v vA vB eA eB p : ℕ} {E₀ E₁ : ℤ}
    (h₀ : (eA : ℤ) ≡ E₀ [ZMOD 12]) (h₁ : (eB : ℤ) ≡ E₁ [ZMOD 12])
    (hr : relZ v vA vB eA eB p = true) :
    zc v ^ p * zc vA ^ ((p : ℤ) * E₀) * zc vB ^ ((p : ℤ) * E₁) = 1 := by
  unfold relZ at hr
  simp only [andB_eq, Bool.and_eq_true] at hr
  obtain ⟨r1, r2, r3⟩ := hr
  have d1 : 4 ∣ p * (v % 4 + eA * (vA % 4) + eB * (vB % 4)) :=
    Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true r1)
  have d2 : 4 ∣ p * (v / 4 % 4 + eA * (vA / 4 % 4) + eB * (vB / 4 % 4)) :=
    Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true r2)
  have d3 : 3 ∣ p * (v / 16 + eA * (vA / 16) + eB * (vB / 16)) :=
    Nat.dvd_of_mod_eq_zero (Nat.eq_of_beq_eq_true r3)
  rw [zc_eq_zHom, zc_eq_zHom, zc_eq_zHom, ← map_pow, ← map_zpow, ← map_zpow, ← map_mul, ← map_mul]
  convert map_one zHom using 2
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have := comp_one (n := 4) (by norm_num) h₀ h₁ d1
    simpa [ZMod.natCast_mod] using this
  · have := comp_one (n := 4) (by norm_num) h₀ h₁ d2
    simpa [ZMod.natCast_mod] using this
  · have := comp_one (n := 3) (by norm_num) h₀ h₁ d3
    simpa using this

theorem substWord_append (hs : List (List (Fin 2 × Bool))) (u v : List (Fin 2 × Bool)) :
    substWord hs (u ++ v) = substWord hs u ++ substWord hs v := by
  rw [substWord, substWord, substWord, List.flatMap_append]

theorem substWord_wpow (hs : List (List (Fin 2 × Bool))) (u : List (Fin 2 × Bool)) (p : ℕ) :
    substWord hs (wpow u p) = wpow (substWord hs u) p := by
  induction p with
  | zero => rfl
  | succ p ih => rw [wpow_succ, wpow_succ, substWord_append, ih]

theorem wpow_one' (u : List (Fin 2 × Bool)) : wpow u 1 = u := by simp [wpow]

section Lift

variable {V : ℕ} {TA TB : ℕ → ℕ} (hV : vtOK V = true)
  (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1) {uA uB : List (Fin 2 × Bool)}

include hV hA hB in
theorem extra_of {b : List (Fin 2 × Bool)} {k p vA vB : ℕ}
    (hk : FW.getD k [] = b.map letterCode)
    (h : extraOK V TA TB FW [uA.map letterCode, uB.map letterCode] vA vB k p = true) :
    cv (substWord [uA, uB] (wpow b p)) * zc vA ^ expOf 0 (wpow b p) *
      zc vB ^ expOf 1 (wpow b p) = 1 := by
  unfold extraOK at h
  rw [bindB_eq] at h
  generalize zvC V TA TB _ = v at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hz, hr⟩ := h
  have hU : [uA.map letterCode, uB.map letterCode] = [uA, uB].map (List.map letterCode) := rfl
  rw [hk, hU, ← map_letterCode_substWord] at hz
  rw [hk] at hr
  have e0 := eN_modEq 0 b
  have e1 := eN_modEq 1 b
  rw [Fin.val_zero] at e0
  rw [Fin.val_one] at e1
  rw [substWord_wpow, cv_wpow, cv_of_zvOK hV hA hB hz, expOf_wpow, expOf_wpow]
  exact extra_one e0 e1 hr

theorem FW_getD (k : ℕ) : FW.getD k [] =
    ((([commWords (coverPairs 0), commWords (coverPairs 1)] ++ rels ++
      [bFive, zOne, zTwo, zThree]).getD k []).map letterCode) := by
  rw [FW, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (([commWords (coverPairs 0), commWords (coverPairs 1)] ++ rels ++
    [bFive, zOne, zTwo, zThree]))[k]? <;> rfl

include hV hA hB in
theorem alphaHom_of_alphaOK
    (h : alphaOK V TA TB FW (uA.map letterCode) (uB.map letterCode) = true) :
    ∃ α : Cover →* Cover, (∀ w, α (cv w) = cv (substWord (autWs uA uB) w)) ∧
      ∀ w, α (cv w) = cv (substWord [uA, uB] w) *
        ((cv uA)⁻¹ * cv ((autWs uA uB).getD 0 [])) ^ expOf 0 w *
        ((cv uB)⁻¹ * cv ((autWs uA uB).getD 1 [])) ^ expOf 1 w := by
  unfold alphaOK at h
  rw [bindB_eq, bindB_eq] at h
  generalize zvC V TA TB (invW (uA.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 0 [])) = vA at h
  generalize zvC V TA TB (invW (uB.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 1 [])) = vB at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hzA, hzB, hR, h9, h10, h11, h12⟩ := h
  have hU : [uA.map letterCode, uB.map letterCode] = [uA, uB].map (List.map letterCode) := rfl
  have eA : invW (uA.map letterCode) ++ substC [uA.map letterCode, uB.map letterCode]
      (FW.getD 0 []) = (FreeGroup.invRev uA ++ (autWs uA uB).getD 0 []).map letterCode := by
    rw [List.map_append, map_letterCode_invRev, FW_getD, hU, ← map_letterCode_substWord]
    rfl
  have eB : invW (uB.map letterCode) ++ substC [uA.map letterCode, uB.map letterCode]
      (FW.getD 1 []) = (FreeGroup.invRev uB ++ (autWs uA uB).getD 1 []).map letterCode := by
    rw [List.map_append, map_letterCode_invRev, FW_getD, hU, ← map_letterCode_substWord]
    rfl
  rw [eA] at hzA
  rw [eB] at hzB
  have zA := cv_of_zvOK hV hA hB hzA
  have zB := cv_of_zvOK hV hA hB hzB
  rw [cv_append, cv_invRev] at zA zB
  have hRel : ∀ r ∈ rels, cv (substWord [uA, uB] r) ∈ center Cover := by
    intro r hr
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
    have hj7 : j < 7 := by
      have : rels.length = 7 := rfl
      omega
    have hs := Mono.allR_spec hR (j + 2) (by omega) (by omega)
    unfold scalarOK at hs
    rw [bindB_eq] at hs
    have hk : FW.getD (j + 2) [] = rels[j].map letterCode := by
      rw [FW_getD]
      congr 1
      interval_cases j <;> rfl
    rw [hk, hU, ← map_letterCode_substWord] at hs
    exact mem_center_of_rowsOK hV hs
  obtain ⟨α, hα, hα'⟩ := exists_alphaHom uA uB (zA ▸ zc_mem_center vA) (zB ▸ zc_mem_center vB) hRel
    (by
      intro e he
      rw [zA, zB]
      simp only [extraWs, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he | he | he <;> rw [he]
      · rw [← wpow_one' bFive]
        exact extra_of hV hA hB rfl h9
      · exact extra_of hV hA hB rfl h10
      · exact extra_of hV hA hB rfl h11
      · exact extra_of hV hA hB rfl h12)
  exact ⟨α, hα, hα'⟩

end Lift

end CFSG.Certificates.L34Cov

end
