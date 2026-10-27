module

public import Certificates.Data.Kernel.B45Perm.GenW
public import Certificates.Data.SmithB45MatGen
public import CFSG.Certificates.Kernel.LocalQTSylProved

public section

namespace CFSG.KC.B45P

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.Syl.Pf
  CFSG.Quasithin.B45Mat

variable {n : ℕ} {H : Subgroup (Perm (Fin n))}

theorem genAt_cH (L : List H) (i : ℕ) : genAt n (L.map (cH H)) i = cH H (L.getD i 1) := by
  have h1 : L.map (cH H) = (L.map Subtype.val).map codeP := by
    simp only [List.map_map]
    rfl
  have h2 : (L.map Subtype.val).getD i 1 = ((L.getD i 1 : H) : Perm (Fin n)) :=
    List.getD_map (l := L) (n := i) (d := (1 : H)) Subtype.val
  rw [h1, genAt_map, h2]
  rfl

theorem evalWK_cH (hn : n ≤ 32) (L : List H) (w : List ℕ) :
    evalWK n (L.map (cH H)) w = cH H (prodWord L w) := by
  induction w with
  | nil => exact cH_one
  | cons i w ih =>
    change CFSG.KC.LQT.P.mul n (genAt n (L.map (cH H)) i) (evalWK n (L.map (cH H)) w) = _
    rw [genAt_cH, ih, cH_mul hn]
    simp [prodWord]

theorem conjGens_two (t c₁ c₂ : H) :
    conjGens [t] [c₁, c₂] = [t, c₁ * t * c₁⁻¹, c₂ * t * c₂⁻¹] := by
  simp [conjGens]

theorem genWE_sound (hn : n ≤ 32) (Rl : List H) (gA gB : H) {cA cB : ℕ}
    (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB)
    (e : ℕ × List (List ℤ) × List ℕ × List ℕ) (h : genWE n cA cB (Rl.map (cH H)) e = true) :
    (e.2.1.length == 2 &&
      prodWord (conjGens [Rl.getD e.1 1] (e.2.1.map (evalN H [gA, gB]))) e.2.2.1 == gA &&
      prodWord (conjGens [Rl.getD e.1 1] (e.2.1.map (evalN H [gA, gB]))) e.2.2.2 == gB) = true := by
  obtain ⟨i, ws, ua, ub⟩ := e
  unfold genWE at h
  rw [CFSG.KC.LQT.P.andB_iff] at h
  obtain ⟨hl, h⟩ := h
  have hl' : ws.length = 2 := by
    rw [lenK_eq] at hl
    exact Nat.eq_of_beq_eq_true hl
  match ws, hl' with
  | [w₁, w₂], _ =>
    simp only [CFSG.KC.LQT.P.letB_eq] at h
    rw [getK_H, getK_eq, getK_eq, zk_eq gA gB hn hA hB, zk_eq gA gB hn hA hB, cH_conj hn,
      cH_conj hn, CFSG.KC.LQT.P.andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    have g0 : [w₁, w₂].getD 0 [] = w₁ := rfl
    have g1 : [w₁, w₂].getD 1 [] = w₂ := rfl
    rw [g0, g1] at h1 h2
    have hr : [cH H (Rl.getD i 1), cH H (evalN H [gA, gB] w₁ * Rl.getD i 1 *
        (evalN H [gA, gB] w₁)⁻¹), cH H (evalN H [gA, gB] w₂ * Rl.getD i 1 *
        (evalN H [gA, gB] w₂)⁻¹)] = (conjGens [Rl.getD i 1]
          ([w₁, w₂].map (evalN H [gA, gB]))).map (cH H) := by
      rw [List.map_cons, List.map_cons, List.map_nil, conjGens_two]
      rfl
    have eA : cA = cH H gA := hA.symm
    have eB : cB = cH H gB := hB.symm
    rw [hr, evalWK_cH hn, eA, beq_cH hn] at h1
    rw [hr, evalWK_cH hn, eB, beq_cH hn] at h2
    simp only at h1 h2 ⊢
    rw [h1, h2]
    simp

theorem genWK_sound (hn : n ≤ 32) (Rl : List H) (gA gB : H) {cA cB : ℕ}
    (hA : codeP (gA : Perm (Fin n)) = cA) (hB : codeP (gB : Perm (Fin n)) = cB) :
    ∀ tab : List (ℕ × List (List ℤ) × List ℕ × List ℕ),
      genWK n cA cB (Rl.map (cH H)) tab = true → genWitOK H Rl gA gB tab = true
  | [] => fun _ => rfl
  | e :: tab => fun h => by
    change CFSG.KC.Ord.andB (genWE n cA cB (Rl.map (cH H)) e)
      (genWK n cA cB (Rl.map (cH H)) tab) = true at h
    rw [CFSG.KC.LQT.P.andB_iff] at h
    have ih := genWK_sound hn Rl gA gB hA hB tab h.2
    unfold genWitOK at ih ⊢
    rw [List.all_cons, genWE_sound hn Rl gA gB hA hB e h.1, ih]
    rfl

end CFSG.KC.B45P

end
