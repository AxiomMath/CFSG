module

public import Certificates.Data.Kernel.L34Cov.NfLift
public import CFSG.Certificates.Kernel.L34Cov.AlphaGenSound

public section

namespace CFSG.Certificates.L34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34
open CFSG.Certificates.CosetEnumeration CFSG.CosetTable CFSG.ComponentClassification.GrSLit.L34Facts
open Subgroup

section Rel

variable (zA zB : Cover)

def NfRel (p : List (Fin 2 × Bool) × Bool) (t : List (Fin 2 × Bool) × Bool × ℕ × ℕ) : Prop :=
  p.2 = t.2.1 ∧ ∃ A B : ℤ, (t.2.2.1 : ℤ) ≡ A [ZMOD 12] ∧ (t.2.2.2 : ℤ) ≡ B [ZMOD 12] ∧
    cv p.1 = cv t.1 * zA ^ A * zB ^ B

variable {zA zB} (hzA : zA ∈ center Cover) (hzB : zB ∈ center Cover)
  {U Aw : List (List (Fin 2 × Bool))}
  (hc : ∀ w, cv (substWord Aw w) = cv (substWord U w) * zA ^ expOf 0 w * zB ^ expOf 1 w)

include hzA hzB hc in
theorem addT_rel {w w' c : List (Fin 2 × Bool)} {e f e' : Bool} {a b : ℕ}
    (h : NfRel zA zB (w, e) (w', e, a, b)) :
    NfRel zA zB (w ++ (if f then substWord Aw c else c), e') (addT U w' f c e' a b) := by
  obtain ⟨-, A, B, ha, hb, hw⟩ := h
  cases f
  · refine ⟨rfl, A, B, ha, hb, ?_⟩
    change cv (w ++ c) = cv (w' ++ c) * zA ^ A * zB ^ B
    rw [cv_append, cv_append, hw]
    have := rearr hzA hzB (cv w') (cv c) A B 0 0
    simp only [zpow_zero, mul_one, add_zero] at this
    exact this
  · refine ⟨rfl, A + expOf 0 c, B + expOf 1 c, ?_, ?_, ?_⟩
    · have e0 := eN_modEq 0 c
      rw [Fin.val_zero] at e0
      change ((a + eN 0 (c.map letterCode) : ℕ) : ℤ) ≡ _ [ZMOD 12]
      push_cast
      exact Int.ModEq.add ha e0
    · have e1 := eN_modEq 1 c
      rw [Fin.val_one] at e1
      change ((b + eN 1 (c.map letterCode) : ℕ) : ℤ) ≡ _ [ZMOD 12]
      push_cast
      exact Int.ModEq.add hb e1
    · change cv (w ++ substWord Aw c) = cv (w' ++ substWord U c) * _ * _
      rw [cv_append, cv_append, hw, hc]
      exact rearr hzA hzB _ _ A B _ _

include hzA hzB hc in
theorem foldl_rel {m : ℕ} (g : ℕ → List (Fin 2 × Bool) × Bool) (l : List (Fin m × Bool))
    (p : List (Fin 2 × Bool) × Bool) (t : List (Fin 2 × Bool) × Bool × ℕ × ℕ)
    (h : NfRel zA zB p t) :
    NfRel zA zB (l.foldl (nfStepA (substWord Aw) g) p) (l.foldl (nfStepT U g) t) := by
  induction l generalizing p t with
  | nil => exact h
  | cons x l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    refine ih _ _ ?_
    obtain ⟨w, e⟩ := p
    obtain ⟨w', e', a, b⟩ := t
    obtain ⟨he, hr⟩ := h
    change e = e' at he
    subst he
    obtain ⟨i, s⟩ := x
    cases s
    · exact addT_rel hzA hzB hc (f := xor e (g i.val).2) ⟨rfl, hr⟩
    · exact addT_rel hzA hzB hc (f := e) ⟨rfl, hr⟩

end Rel

theorem nfLiftsOK_sound {V : ℕ} {TA TB : ℕ → ℕ}
    (hV : vtOK V = true) (hA : MonoModel TA 3 2) (hB : MonoModel TB 0 1)
    {uA uB : List (Fin 2 × Bool)} {m : ℕ} {g : ℕ → List (Fin 2 × Bool) × Bool}
    {L : List (List (Fin m × Bool) × List (Fin 2 × Bool) × ℕ)}
    (h : nfLiftsOK V TA TB FW uA uB g L = true)
    {l : List (Fin m × Bool)} {s : List (Fin 2 × Bool)} {e : ℕ} (hx : (l, s, e) ∈ L) :
    cv ((l.foldl (nfStepA (substWord (autWs uA uB)) g) ([], false)).1 ++ s) =
      z₁ ^ (e % 48 / 12) * z₂ ^ (e % 12 / 3) * z₃ ^ (e % 3) := by
  unfold nfLiftsOK at h
  rw [bindB_eq, bindB_eq] at h
  generalize zvC V TA TB (invW (uA.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 0 [])) = vA at h
  generalize zvC V TA TB (invW (uB.map letterCode) ++
    substC [uA.map letterCode, uB.map letterCode] (FW.getD 1 [])) = vB at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨hzA, hzB, hL⟩ := h
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
  have hc0 : (cv ([uA, uB].getD 0 []))⁻¹ * cv ((autWs uA uB).getD 0 []) = zc vA := zA
  have hc1 : (cv ([uA, uB].getD 1 []))⁻¹ * cv ((autWs uA uB).getD 1 []) = zc vB := zB
  have hl : ∀ w, cv (substWord (autWs uA uB) w) =
      cv (substWord [uA, uB] w) * zc vA ^ expOf 0 w * zc vB ^ expOf 1 w := by
    intro w
    rw [← lift_cv_getD (autWs uA uB) w, ← lift_cv_getD [uA, uB] w, ← hc0, ← hc1]
    exact lift_eq_corr _ _ (hc0 ▸ zc_mem_center vA) (hc1 ▸ zc_mem_center vB) w
  have h0 : NfRel (zc vA) (zc vB) ([], false) ([], false, 0, 0) :=
    ⟨rfl, 0, 0, Int.ModEq.refl _, Int.ModEq.refl _, by simp⟩
  obtain ⟨-, A, B, ha, hb, hw⟩ :=
    foldl_rel (zc_mem_center vA) (zc_mem_center vB) hl g l _ _ h0
  have hx' := List.all_eq_true.1 hL (l, s, e) hx
  unfold nfEntOK nfT at hx'
  dsimp only at hx'
  have hid := cv_of_zvOK hV hA hB hx'
  generalize l.foldl (nfStepT [uA, uB] g) ([], false, 0, 0) = t at ha hb hw hid
  obtain ⟨w', e', a, b⟩ := t
  change cv (w' ++ s) = zc (corrC e vA vB (a % 12) (b % 12)) at hid
  change (a : ℤ) ≡ A [ZMOD 12] at ha
  change (b : ℤ) ≡ B [ZMOD 12] at hb
  change cv _ = cv w' * zc vA ^ A * zc vB ^ B at hw
  have h₀ : ((a % 12 : ℕ) : ℤ) ≡ A [ZMOD 12] := by
    push_cast
    exact (Int.mod_modEq _ _).trans ha
  have h₁ : ((b % 12 : ℕ) : ℤ) ≡ B [ZMOD 12] := by
    push_cast
    exact (Int.mod_modEq _ _).trans hb
  have hcorr := corr_spec (e := e) (vA := vA) (vB := vB) h₀ h₁
    (Nat.le_of_lt (Nat.mod_lt _ (by norm_num))) (Nat.le_of_lt (Nat.mod_lt _ (by norm_num)))
  rw [cv_append, hw, ← hcorr, ← hid, cv_append]
  have := rearr (zc_mem_center vA) (zc_mem_center vB) (cv w') (cv s) A B 0 0
  simp only [zpow_zero, mul_one, add_zero] at this
  exact this

end CFSG.Certificates.L34Cov

end
