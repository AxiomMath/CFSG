module

public import Certificates.Data.Kernel.GHarrisA5Gen

public section

namespace CFSG.KC.GHarrisA5

open CFSG.ComponentClassification.GHarris GL42

theorem M4c.mul_assoc (A B C : M4c) : (A.mul B).mul C = A.mul (B.mul C) := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩, ⟨a12, a13, a14, a15⟩⟩ := A
  obtain ⟨⟨b0, b1, b2, b3⟩, ⟨b4, b5, b6, b7⟩, ⟨b8, b9, b10, b11⟩, ⟨b12, b13, b14, b15⟩⟩ := B
  obtain ⟨⟨c0, c1, c2, c3⟩, ⟨c4, c5, c6, c7⟩, ⟨c8, c9, c10, c11⟩, ⟨c12, c13, c14, c15⟩⟩ := C
  simp only [M4c.mul, M4c.transpose, M4c.mulVec, V4c.dot, M4c.mk.injEq, V4c.mk.injEq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> ring

theorem M4c.mul_one (A : M4c) : A.mul M4c.one = A := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩, ⟨a12, a13, a14, a15⟩⟩ := A
  simp only [M4c.mul, M4c.one, M4c.transpose, M4c.mulVec, V4c.dot, M4c.mk.injEq, V4c.mk.injEq]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;> ring

theorem homOK_of_gen {j : ℕ} (h1 : phiA5 j 1 = M4c.one) (hg : HomGen j) (hw : WordsGen) :
    ∀ p q : alternatingGroup (Fin 5), phiA5 j (p * q) = (phiA5 j p).mul (phiA5 j q) := by
  let P : alternatingGroup (Fin 5) → Prop := fun q => ∀ p, phiA5 j (p * q) = (phiA5 j p).mul (phiA5 j q)
  have hmul : ∀ a b, P a → P b → P (a * b) := fun a b ha hb p => by
    rw [← _root_.mul_assoc, hb, ha, M4c.mul_assoc, ← hb a]
  have hone : P 1 := fun p => by rw [_root_.mul_one, h1, M4c.mul_one]
  have hgen : ∀ i, P (gens.getD i 1) := by
    intro i
    rcases i with _ | _ | i
    · exact fun p => hg p _ (List.mem_cons_self ..)
    · exact fun p => hg p _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact hone
  have hword : ∀ (w : List ℕ) (a : alternatingGroup (Fin 5)), P a →
      P (w.foldl (fun a i => a * gens.getD i 1) a) := by
    intro w
    induction w with
    | nil => exact fun a ha => ha
    | cons i w ih => exact fun a ha => ih _ (hmul _ _ ha (hgen i))
  intro p q
  rw [← hw q]
  exact hword _ 1 hone p

end CFSG.KC.GHarrisA5

end
