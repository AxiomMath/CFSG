module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBSylData

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def aW : MB := w₁ * y * k

@[expose] def commL (p : ℕ × ℕ) (φ : List MB) : List ((MB × Bool × Bool) × List MB) :=
  (H4Zof p).filter fun e => compQ1 φ e.2 == compQ1 e.2 φ

@[expose] def nfix (φ : List MB) : ℕ := (E0L.filter fun e => applyQ1 φ e == e).length

@[expose] def Q1reps : List MB := (allBits 4).map (nfProd [w₂, w₁, v, t])

@[expose] def sqOK (φ : List MB) : Bool :=
  (Q1reps.filter fun f => f * f == 1).any fun f => compQ1 φ φ == conjQ1 f

@[expose] def σpB (j : ℕ) (a : Bool) (x : MB) : MB :=
  if a then applyMB (r2Classes.getD j ([], 1)).1 x else x

@[expose] def r2mul (j : ℕ) (x y : MB × Bool) : MB × Bool :=
  (x.1 * σpB j x.2 y.1 * (if x.2 && y.2 then (r2Classes.getD j ([], 1)).2 else 1), xor x.2 y.2)

@[expose] def b4OK (j : ℕ) (s : MB) (a : Bool) : Bool :=
  E0L.all fun e => !(r2mul j (s * e, a) (s * e, a) == (1, false)) ||
    (decide (64 ≤ (Finset.univ.filter fun s' : MB =>
      r2mul j (s', false) (s * e, a) = r2mul j (s * e, a) (s', false)).card) &&
     decide (0 < (Finset.univ.filter fun s' : MB =>
      r2mul j (s', true) (s * e, a) = r2mul j (s * e, a) (s', true)).card))

@[expose] def trCheck (p : ℕ × ℕ) (e : (MB × Bool × Bool) × List MB) : Bool :=
  !(applyQ1 e.2 aW == aW) || innerT e.1 || !(compQ1 e.2 e.2 == gensQ1) ||
    decide (8 * nfix e.2 < (commL p e.2).length) ||
    (decide (8 * nfix e.2 ≤ (commL p e.2).length) && (commL p e.2).all fun e' => sqOK e'.2) ||
    (!e.1.2.2 && b4OK p.1 e.1.1 e.1.2.1)

theorem aW_mem_Z2L : aW ∈ Z2L := by decide +kernel

theorem t_conj_aW : t * aW * t⁻¹ = aW * z := by decide +kernel

theorem inQC_of_comm_aW : ∀ x : MB, inQ1 x = true → x * aW = aW * x → inQC x = true := by
  decide +kernel

theorem w₂_conj_v : w₂ * v * w₂⁻¹ = v * y := by decide +kernel

theorem AL_spec : ∀ a : MB, inQC a = true → a ∈ AL := by decide +kernel

theorem E0L_σ : ∀ j < 4, ∀ e ∈ E0L, applyMB (r2Classes.getD j ([], 1)).1 e ∈ E0L := by
  decide +kernel

end MB

end Sec8

end CFSG.ComponentClassification.HSFLit
