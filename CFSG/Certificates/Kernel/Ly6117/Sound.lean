module

public import Certificates.Data.Kernel.Ly6117.Check
public import CFSG.Certificates.Kernel.LyS0.Sound
public import CFSG.Sporadic.Recognition.LyonsFinalLyInputs
public import CFSG.Certificates.CosetTableShort

public section

namespace CFSG.KS.Ly6117K

open CFSG.KD.Ly6117 CFSG.KD.LyS0 CFSG.KS.LyS0K CFSG.KS.SporSch.LyM CFSG.Sporadic.He.Native
open CFSG.Sporadic.Recognition.LyonsSims.LyFinal

local notation "U" X:max => unpackL 111 12 1332 X

theorem beqU {X Y : Nat} (hX : vld X = true) (hY : vld Y = true) :
    (U X == U Y) = Nat.beq X Y := beq_eq CFSG.KD.OrdLy.consts (hv hX) (hv hY)

theorem wordK_cons (G GI : Nat → Nat) (l : Fin 6 × Bool) (w : List (Fin 6 × Bool)) :
    wordK G GI (l :: w) = mul (letK G GI l) (wordK G GI w) :=
  strictN_eq _ _

theorem wordK_eq {g gi : Fin 6 → Mat} {G GI : Nat → Nat}
    (hg : ∀ i : Fin 6, g i = U (G i.val) ∧ vld (G i.val) = true)
    (hgi : ∀ i : Fin 6, gi i = U (GI i.val) ∧ vld (GI i.val) = true) :
    ∀ w, wordM g gi w = U (wordK G GI w) ∧ vld (wordK G GI w) = true
  | [] => ⟨idE, vOne⟩
  | l :: w => by
    obtain ⟨e, v⟩ := wordK_eq hg hgi w
    have hl : letterM g gi l = U (letK G GI l) ∧ vld (letK G GI l) = true := by
      obtain ⟨i, s⟩ := l
      unfold letterM letK
      rw [nIf_eq]
      cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> first | exact hgi i | exact hg i
    have hw : wordM g gi (l :: w) = mulM 5 111 (letterM g gi l) (wordM g gi w) := by
      unfold wordM
      rw [List.foldr_cons]
    rw [hw, wordK_cons, e, hl.1, mulE hl.2 v]
    exact ⟨rfl, mulV hl.2 v⟩

theorem lyRelCheck_of {G GI : Nat → Nat} {A B : Nat} {R : List (List (Fin 6 × Bool))}
    (hg : ∀ i : Fin 6, genM i = U (G i.val) ∧ vld (G i.val) = true)
    (hgi : ∀ i : Fin 6, genInvM i = U (GI i.val) ∧ vld (GI i.val) = true)
    (hA : CFSG.Sporadic.Ly.Native.matA = U A) (hB : CFSG.Sporadic.Ly.Native.matB = U B)
    (vA : vld A = true) (vB : vld B = true)
    (h1 : (List.finRange 6).all (fun i => Nat.beq (mul (G i.val) (GI i.val))
      CFSG.KD.OrdLy.ONE) = true)
    (h2 : allK G GI R = true)
    (h3 : Nat.beq (wordK G GI wordA) A = true) (h4 : Nat.beq (wordK G GI wordB) B = true) :
    lyRelCheck R = true := by
  unfold lyRelCheck
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨fun i _ => ?_, fun r hr => ?_⟩, ?_⟩, ?_⟩
  · rw [(hg i).1, (hgi i).1, mulE (hg i).2 (hgi i).2, idE, beqU (mulV (hg i).2 (hgi i).2) vOne]
    exact List.all_eq_true.1 h1 i (List.mem_finRange i)
  · obtain ⟨e, v⟩ := wordK_eq hg hgi r
    rw [e, idE, beqU v vOne]
    exact List.all_eq_true.1 h2 r hr
  · obtain ⟨e, v⟩ := wordK_eq hg hgi wordA
    rw [e, hA, beqU v vA]
    exact h3
  · obtain ⟨e, v⟩ := wordK_eq hg hgi wordB
    rw [e, hB, beqU v vB]
    exact h4

end CFSG.KS.Ly6117K

end
