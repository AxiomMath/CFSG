module

public import CFSG.Certificates.Kernel.SmithEK.SpanSound
public import Certificates.Data.Kernel.SmithL6KS
public import CFSG.Certificates.Kernel.SmithL6CollSound
public import Certificates.Data.SmithL6Facts

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK
open CFSG.SmithE (applyCols spanData echelon gensOf)
open CFSG.SmithE.K (applyL gensL gensOf_toList applyL_comp applyL_zero)

theorem apK_eq_applyL (l : List Nat) (x : Nat) : apK l x = applyL l x := by
  rw [← CollK.applyCols_toArray, CFSG.SmithE.K.applyCols_toArray]

theorem apK_fun (l : List Nat) : apK l = applyL l := funext (apK_eq_applyL l)

theorem applyCols_toArray_fun (l : List Nat) : applyCols l.toArray = applyL l :=
  funext (CFSG.SmithE.K.applyCols_toArray l)

theorem mulK_getD (A B : List Nat) (m : Nat) :
    (mulK A B).getD m 0 = applyL A (B.getD m 0) := by
  have h := List.getD_map (l := B) (f := apK A) (n := m) (d := 0)
  rw [apK_eq_applyL A 0, applyL_zero] at h
  unfold mulK
  rw [h, apK_eq_applyL]

theorem mulK_apply (A B : List Nat) (c : Nat) :
    applyL (mulK A B) c = applyL A (applyL B c) := by
  unfold mulK
  rw [applyL_comp]
  congr 1
  exact List.map_congr_left fun x _ => apK_eq_applyL A x

theorem toArray_get_fun (l : List Nat) (m : Nat) : l.toArray[m]! = l.getD m 0 := toArray_get l m

theorem mfCommuteB_of {A B : List Nat} (h : (mulK A B == mulK B A) = true) :
    mfCommuteB A.toArray B.toArray = true := by
  have e := beq_iff_eq.mp h
  unfold mfCommuteB
  simp only [applyCols_toArray_fun, toArray_get_fun]
  refine List.all_eq_true.mpr fun m _ => beq_iff_eq.mpr ?_
  rw [← mulK_getD, ← mulK_getD, e]

theorem mfBraidB_of {A B : List Nat}
    (h : (mulK (mulK A B) A == mulK (mulK B A) B) = true) :
    mfBraidB A.toArray B.toArray = true := by
  have e := beq_iff_eq.mp h
  unfold mfBraidB
  simp only [applyCols_toArray_fun, toArray_get_fun]
  refine List.all_eq_true.mpr fun m _ => beq_iff_eq.mpr ?_
  rw [← mulK_apply, ← mulK_apply, ← mulK_getD, ← mulK_getD, e]

theorem mfDihB_of {A B : List Nat}
    (h : (mulK (mulK A B) (mulK A B) == mulK (mulK B A) (mulK B A)) = true) :
    mfDihB A.toArray B.toArray = true := by
  have e := beq_iff_eq.mp h
  unfold mfDihB
  simp only [applyCols_toArray_fun, toArray_get_fun]
  refine List.all_eq_true.mpr fun m _ => beq_iff_eq.mpr ?_
  rw [← mulK_getD B A, ← mulK_apply, ← mulK_getD A B, ← mulK_apply, ← mulK_getD, ← mulK_getD, e]

theorem pair_of {c0 c : Nat} {A B : List Nat} (h : sPairK c0 A (c, B) = true) :
    (match kindC c0 c with
      | 0 => mfCommuteB A.toArray B.toArray
      | 1 => mfBraidB A.toArray B.toArray
      | _ => mfDihB A.toArray B.toArray) = true := by
  unfold sPairK at h
  dsimp only at h
  generalize kindC c0 c = n at h ⊢
  rcases n with _ | _ | n
  · exact mfCommuteB_of h
  · exact mfBraidB_of h
  · exact mfDihB_of h

theorem spanData_basis {L : List Nat} (hL : L.length = 20) :
    (spanData L.toArray).basis = ((sEchL L).map (·.2)).toArray := by
  unfold spanData echelon sEchL
  rw [gensOf_toList hL]

theorem spanData_syn {L : List Nat} (hL : L.length = 20) :
    (spanData L.toArray).syn = (sSynL (sEchL L)).toArray := by
  unfold spanData echelon sEchL sSynL
  rw [gensOf_toList hL]
  apply Array.ext
  · simp
  · intro i _ _
    simp

theorem spanBody_of {T : Array Nat} (h : CFSG.SmithE.K.spanOKA T = true) :
    (let D := spanData T; let g := gensOf T
      D.basis.size == 6 && D.coef.size == 20 &&
      (List.range 20).all fun m => decide (D.coef[m]! < 64) &&
        applyCols D.basis D.coef[m]! == g[m]! && applyCols D.syn g[m]! == 0) = true := by
  unfold CFSG.SmithE.K.spanOKA at h
  exact h

theorem sSpanE_eq (L : List Nat) : sSpanE L (sEchL L) = CFSG.SmithE.K.spanOKL L := rfl

theorem sRowK_parts {A B0 : List Nat} {W c0 c : Nat} {L : List Nat}
    (h : sRowK A B0 W c0 (c, L) = true) :
    sPairK c0 A (c, L) = true ∧ CFSG.SmithE.K.spanOKL L = true ∧
      sInt0E B0 W c0 c (sEchL L) = true := by
  unfold sRowK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, (sSpanE_eq L).symm.trans h.1.2, h.2⟩

theorem int0_of {L0 L : List Nat} (h0 : L0.length = 20) (hL : L.length = 20) {isW : Nat → Bool}
    {W c0 c : Nat} (hW : ∀ v, W.testBit v = true → isW v = true)
    (h : sInt0E ((sEchL L0).map (·.2)) W c0 c (sEchL L) = true) :
    (let S := (spanData L0.toArray).basis.map (applyCols (spanData L.toArray).syn)
     let h0 := kindC c0 c == 0
     (List.range 64).all fun d => applyCols S d != 0 ||
       (let v := applyCols (spanData L0.toArray).basis d; v == 0 || (h0 && isW v))) = true := by
  dsimp only
  unfold sInt0E at h
  simp only [apK_fun] at h
  rw [spanData_basis h0, spanData_syn hL, List.map_toArray, applyCols_toArray_fun,
    applyCols_toArray_fun, applyCols_toArray_fun]
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
  intro d hd
  rcases h d hd with h1 | h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr ⟨h2, hW _ h3⟩)

end CFSG.SmithL6.K
