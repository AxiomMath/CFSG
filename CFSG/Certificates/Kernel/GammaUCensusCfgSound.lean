
module

public import Certificates.Data.Kernel.GammaUCensusCK
public import CFSG.Certificates.Kernel.IdxFourChainSound

public section

namespace CFSG.KC.GUC

open CFSG.KC.IF4C CFSG.KC.IF4R

theorem tbOK_spec {CG TB : Nat} (h : tbOK CG TB = true) :
    ∀ c < 32, ∀ m < 32, look TB (32 * c + m) = subP (five CG c) m := by
  intro c hc m hm
  unfold tbOK at h
  have := (allBelow_iff _ _).1 ((allBelow_iff _ _).1 h c hc) m hm
  simpa only [Nat.beq_eq, Nat.mul_eq, Nat.add_eq] using this

theorem pairOK_spec {SPL : List Nat} {S0 TE TEi DT DTi TB FT FC N IX n j : Nat}
    (h : pairOK SPL S0 TE TEi DT DTi TB FT FC N IX n j = true)
    (ha : ap12 (mulP (look DTi j) (look TEi n)) 3072 ∈ SPL) :
    ∀ c < 32, (∀ m < 32, look TB (32 * c + m) ≠
        mulP (mulP (look DTi j) (look TEi n)) (mulP S0 (mulP (look TE n) (look DT j)))) ∨
      (cellX IX n j c < N ∧ look FT (cellX IX n j c) = mulP (look TE n) (look DT j) ∧
        fld FC (cellX IX n j c) = c) := by
  intro c hc
  unfold pairOK pairAt at h
  rw [Bool.or_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, memN_iff] at h
  have h2 := h.resolve_left (not_not.2 ha)
  unfold cellsOK at h2
  have h3 := (allBelow_iff _ _).1 h2 c hc
  unfold cellOK at h3
  simp only [Bool.or_eq_true, Bool.and_eq_true, allBelow_iff, Bool.not_eq_true', Nat.blt_eq,
    Nat.beq_eq] at h3
  rcases h3 with h3 | h3
  · refine Or.inl fun m hm e => ?_
    have := h3 m hm
    rw [Nat.mul_eq, Nat.add_eq, e] at this
    simp at this
  · exact Or.inr ⟨h3.1.1, h3.1.2, h3.2⟩

end CFSG.KC.GUC

end
