module

public import CFSG.ClassicalInvolution.Asc77.AscIH8Small

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

@[expose] def Ih8Thm5 : Prop := ∀ n : ℕ, CITBelowU p f n → Thm5Below p f n

@[expose] def Ih8MuTable : Prop := ∀ n : ℕ, CITBelowU p f n → MuTableBelow p f n

@[expose] def Ih8Thm3 : Prop := ∀ n : ℕ, CITBelowU p f n → T3Typed.Thm3TypedBelowExact p f n

variable {p f}

theorem ih8Rest_of (h5 : Ih8Thm5 p f) (hMu : Ih8MuTable p f) (h3 : Ih8Thm3 p f)
    (hG : Ih8G2D4 p f) : IH8Rest p f :=
  fun _ hn => ⟨h5 _ hn, thm6TypedBelow_of (ih8SmallEdge p) hn, thm7TypedBelow_of hG hn,
    thm8TypedBelow_of hG hn, hMu _ hn, h3 _ hn⟩

theorem ih8All_of (h5 : ∀ e : ℕ, 5 ≤ p ^ e → Ih8Thm5 p e)
    (hMu : ∀ e : ℕ, 5 ≤ p ^ e → Ih8MuTable p e) (h3 : ∀ e : ℕ, 5 ≤ p ^ e → Ih8Thm3 p e)
    (hG : ∀ e : ℕ, 5 ≤ p ^ e → Ih8G2D4 p e) {n : ℕ} (hn : CITBelowAll p n) : IH8All p n :=
  ih8All_of_rest (fun e he => ih8Rest_of (h5 e he) (hMu e he) (h3 e he) (hG e he)) hn

end CFSG.ClassicalInvolution.Asc77
