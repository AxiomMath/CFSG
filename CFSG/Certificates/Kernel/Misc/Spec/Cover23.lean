module

public import Certificates.Data.Kernel.Misc.G23
public import CFSG.Certificates.Kernel.Misc.Spec.Words
public import CFSG.Certificates.Kernel.Misc.Spec.F2Mat
public import CFSG.Certificates.Kernel.Misc.Spec.ArrMat

public section

namespace CFSG.KC.Misc.Spec

open CFSG.LieType.Multipliers
open CFSG.KC.Misc.G23 (commsW coverW letterM wordM)

theorem commsW_eq {m : ℕ} (ps : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    commsW (ps.map fun p => (encG p.1, encG p.2)) = encG (commWords ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨u, v⟩ := p
    show CFSG.KC.Misc.G24.appN (CFSG.KC.Misc.G24.commK (encG u) (encG v))
      (commsW (ps.map fun p => (encG p.1, encG p.2))) = _
    rw [appN_eq, ih, commK_enc]
    simp only [commWords, List.map_cons, List.flatten_cons, encG, List.map_append]

theorem appLL_eq (a b : List (List ℕ)) : coverW.appLL a b = a ++ b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    show x :: coverW.appLL a b = (x :: a) ++ b
    rw [ih]
    rfl

theorem coverW_eq (R : List (List (Fin 2 × Bool)))
    (P : Fin 2 → List (List (Fin 2 × Bool) × List (Fin 2 × Bool)))
    (Pc : List (List (List ℕ × List ℕ)))
    (hP : ∀ i : Fin 2, (P i).map (fun p => (encG p.1, encG p.2)) = CFSG.KC.Misc.G24.nthP Pc i) :
    coverW (R.map encG) Pc = (coverWords R fun i => commWords (P i)).map encG := by
  unfold coverW
  rw [listRec_map, listRec_map, appLL_eq, appLL_eq]
  have hf : List.finRange 2 = [⟨0, by omega⟩, ⟨1, by omega⟩] := rfl
  unfold coverWords
  rw [hf]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    List.map_append, List.cons_append, List.nil_append]
  have c1 : ∀ (i : Fin 2) (r : List (Fin 2 × Bool)),
      CFSG.KC.Misc.G24.commK [2 * i.val + 1] (encG r) = encG (commWord [(i, true)] r) :=
    fun i r => commK_enc [(i, true)] r
  have d0 : encG ((⟨0, by omega⟩, false) :: commWords (P ⟨0, by omega⟩)) =
      0 :: commsW (CFSG.KC.Misc.G24.nthP Pc 0) := by
    rw [← hP ⟨0, by omega⟩, commsW_eq]
    rfl
  have d1 : encG ((⟨1, by omega⟩, false) :: commWords (P ⟨1, by omega⟩)) =
      2 :: commsW (CFSG.KC.Misc.G24.nthP Pc 1) := by
    rw [← hP ⟨1, by omega⟩, commsW_eq]
    rfl
  rw [d0, d1]
  congr 2
  · rw [List.map_map, List.map_map]
    exact List.map_congr_left fun r _ => c1 ⟨0, by omega⟩ r
  · rw [List.map_map, List.map_map]
    exact List.map_congr_left fun r _ => c1 ⟨1, by omega⟩ r

theorem pkMat_wordM {A B Bi : ℕ} {M : Fin 2 × Bool → Matrix (Fin 54) (Fin 54) (ZMod 2)}
    (hA : ∀ b, pkMat 54 A = M (0, b)) (hB : pkMat 54 B = M (1, true))
    (hBi : pkMat 54 Bi = M (1, false)) (w : List (Fin 2 × Bool)) :
    pkMat 54 (wordM A B Bi (encG w)) = wordProd M w := by
  induction w with
  | nil =>
    show pkMat 54 (CFSG.KC.Misc.G24.oneF2 54) = 1
    exact pkMat_oneF2 54
  | cons l w ih =>
    have hl : pkMat 54 (letterM A B Bi (encL l)) = M l := by
      obtain ⟨⟨i, hi⟩, b⟩ := l
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · cases b
        · exact hA false
        · exact hA true
      · cases b
        · exact hBi
        · exact hB
    show pkMat 54 (CFSG.KC.Misc.G24.mulF2 54 (letterM A B Bi (encL l))
      (wordM A B Bi (encG w))) = M l * wordProd M w
    rw [pkMat_mulF2, hl, ih]

end CFSG.KC.Misc.Spec

end
