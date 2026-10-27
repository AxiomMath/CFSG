module

public import CFSG.LocalAnalysis.ComponentInitial.MonE7Trace

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.MonE7

open CFSG.YGroups (wordFG)
open CFSG.Certificates.CosetEnumeration (evalWord evalWord_nil evalWord_cons)
open Classical

namespace TraceState

variable (s : TraceState)

variable {s}

section Labelling

variable {Q : Type*} (act : Q → ℕ → Q)

@[expose] def actWord (q : Q) (w : List ℕ) : Q := w.foldl act q

variable {act}

@[simp] theorem actWord_nil (q : Q) : actWord act q [] = q := rfl

@[simp] theorem actWord_cons (q : Q) (a : ℕ) (w : List ℕ) :
    actWord act q (a :: w) = actWord act (act q a) w := rfl

variable (hinv : ∀ q i, act (act q i) i = q) {c : ℕ → Q}

end Labelling

end TraceState

section Cosets

variable {G : Type*} [Group G] (H : Subgroup G)

@[expose] def rmul (q : Quotient (QuotientGroup.rightRel H)) (g : G) :
    Quotient (QuotientGroup.rightRel H) :=
  Quotient.map (· * g) (fun a b hab => QuotientGroup.rightRel_apply.2 (by
    have h := QuotientGroup.rightRel_apply.1 hab
    rw [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    exact h)) q

variable {H}

@[simp] theorem rmul_mk (a g : G) :
    rmul H (Quotient.mk _ a) g = Quotient.mk (QuotientGroup.rightRel H) (a * g) := rfl

end Cosets

end CFSG.LocalAnalysis.ComponentInitial.MonE7
