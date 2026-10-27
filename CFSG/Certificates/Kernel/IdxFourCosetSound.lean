
module

public import Certificates.Data.Kernel.IdxFourCosetK
public import CFSG.Certificates.Kernel.IdxFourChainCard

public section

namespace CFSG.KC.IF4M

open CFSG.GF2Type.Smith1979.GammaU CFSG.KC.IF4C

theorem IsP.of_mul_left {U V : V12 ≃ₗ[ZMod 2] V12} {g h : Nat} (hU : IsP U (mulP g h))
    (hV : IsP V g) : IsP (V⁻¹ * U) h := fun v => by
  have h1 : U v = V (linP h v) := by rw [hU, linP_mulP, hV]
  calc (V⁻¹ * U) v = V⁻¹ (V (linP h v)) := by rw [LinearEquiv.mul_apply, h1]
    _ = (V⁻¹ * V) (linP h v) := rfl
    _ = linP h v := by rw [inv_mul_cancel]; rfl

theorem exists_wordM {K : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {MT : Nat} {m : Nat}
    (hMT : ∀ e < m, ∃ U ∈ K, IsP U (look MT e)) :
    ∀ w : List Nat, (∀ e ∈ w, e < m) → ∃ U ∈ K, IsP U (wordM MT w)
  | [], _ => ⟨1, K.one_mem, IsP.one⟩
  | e :: w, hw => by
    obtain ⟨U, hU, hUP⟩ := hMT e (hw e List.mem_cons_self)
    obtain ⟨V, hV, hVP⟩ := exists_wordM hMT w fun e' h' => hw e' (List.mem_cons_of_mem _ h')
    exact ⟨U * V, K.mul_mem hU hV, hUP.mul hVP⟩

variable {SP SI : Nat} {T O PS B : List Nat} {TL WD : List (List Nat)}
  {TR R : List (List (List Nat))} {k j0 n : Nat}

namespace ChainHyp

open CFSG.KC.IF4C.ChainHyp

variable (hC : CFSG.KC.IF4C.ChainHyp SP SI T O PS B TL WD TR R k j0 n)
include hC

theorem path0 : ∀ (as : List Nat) (s : Nat), pathOK (O.drop s) as = true →
    ∃ P ∈ lvlGrp SP TL 0, IsP P (pathP (T.drop s) as)
  | [], s, _ => ⟨1, Subgroup.one_mem _, by rw [pathP_nil]; exact IsP.one⟩
  | a :: as, s, h => by
    by_cases hsk : s < k
    · have hO : s < O.length := by rw [hC.lenO]; exact hsk
      have hT : s < T.length := by rw [hC.lenT]; exact hsk
      rw [List.drop_eq_getElem_cons hO] at h
      change (Nat.blt a O[s] && pathOK (O.drop (s + 1)) as) = true at h
      rw [Bool.and_eq_true, Nat.blt_eq] at h
      obtain ⟨U, hU, hUP⟩ := hC.exists_tr hsk a (by rw [getD_of_lt _ hO]; exact h.1)
      obtain ⟨P, hP, hPP⟩ := path0 as (s + 1) h.2
      refine ⟨U * P, Subgroup.mul_mem _ hU hP, ?_⟩
      rw [List.drop_eq_getElem_cons hT]
      change IsP _ (mulP (look T[s] a) (pathP (T.drop (s + 1)) as))
      rw [← getD_of_lt 0 hT]
      exact hUP.mul hPP
    · rw [List.drop_eq_nil_of_le (by rw [hC.lenO]; omega)] at h
      exact absurd (h : false = true) Bool.false_ne_true

theorem not_mem_of_negRec {c : Nat} : ∀ (as : List Nat) (j : Nat) (r : Nat) (rs : List Nat)
    (U : V12 ≃ₗ[ZMod 2] V12), j ≤ k → U ∈ lvlGrp SP TL j → IsP U r →
      negRec T O PS B k c j as r rs = true → False
  | [], j, r, [], U, hjk, hU, hUP, h => by
    rw [negRec] at h
    split_ifs at h with hj
    · obtain ⟨x, hx, V, hV, g, hg, rfl⟩ := hC.surj hj hU
      have hgb := hC.fix (by omega) (by omega) hg (Nat.lt_succ_self j)
      have hb : (V * g) (vecOf (B.getD j 0)) = V (vecOf (B.getD j 0)) := by
        rw [LinearEquiv.mul_apply, hgb]
      rw [hUP.apply_code, hV.apply_code] at hb
      have heq := vecOf_inj (ap12_lt _ _) (ap12_lt _ _) hb
      have hp := posOK_spec T O PS B (hC.pos j hj) x hx
      rw [heq, hp] at h
      simp at h
    · simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
        decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hrc⟩, hc⟩ := h
      rw [hC.lvlGrp_eq_bot, Subgroup.mem_bot] at hU
      subst hU
      have h1 := hUP.apply_code c
      exact hrc (vecOf_inj (ap12_lt _ _) hc h1.symm)
  | [], _, _, _ :: _, _, _, _, _, h => by simp [negRec] at h
  | _ :: _, _, _, [], _, _, _, _, h => by simp [negRec] at h
  | a :: as, j, r, r' :: rs, U, hjk, hU, hUP, h => by
    rw [negRec] at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, hab⟩, hr⟩, hrec⟩ := h
    have hj : j < k := by
      by_contra hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hC.lenO]; omega)] at ha
      simp at ha
    obtain ⟨x, hx, V, hV, g, hg, rfl⟩ := hC.surj hj hU
    have hgb := hC.fix (by omega) (by omega) hg (Nat.lt_succ_self j)
    obtain ⟨W, -, hWP⟩ := hC.tr hj a ha
    have hb : (V * g) (vecOf (B.getD j 0)) = V (vecOf (B.getD j 0)) := by
      rw [LinearEquiv.mul_apply, hgb]
    have hVW : V (vecOf (B.getD j 0)) = W (vecOf (B.getD j 0)) := by
      rw [← hb, hUP.apply_code, hWP.apply_code, hab]
    have hxa := hC.idx_eq hj hx ha hV hWP hVW
    subst hxa
    rw [hr] at hUP
    have hg' := IsP.of_mul_left hUP hV
    rw [← mul_assoc, inv_mul_cancel, one_mul] at hg'
    exact not_mem_of_negRec as (j + 1) r' rs g (by omega) hg hg' hrec

end ChainHyp

end CFSG.KC.IF4M

end
