module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55CrossParts

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

@[expose] def E1Type (Fd : ℕ → (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (r : ℕ) (Y : Type) [Group Y] [Finite Y], r.Prime → r ≠ 2 → Fd r Y → ∀ b : MulAut Y, b ≠ 1 →
    ¬ r ∣ orderOf b →
      (∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → ∀ x ∈ E, b x = x) →
      ∀ E : Subgroup Y, IsPGroup r ↥E → (∀ x ∈ E, b x ∈ E) → E = ⊥

structure E1Types : Prop where
  l2 : E1Type FL2d
  l3 : E1Type FL3d
  u3 : E1Type FU3d
  sp4 : E1Type FSp4d
  g2 : E1Type FG2d
  d4 : E1Type FD4d
  l4 : E1Type FL4d
  u4 : E1Type FU4d
  ree : E1Type FReed

theorem crossE1_of_types (h : E1Types) : CrossE1 := by
  intro r Y _ _ hY b hb1 hbr hHH E hE hinv
  obtain ⟨hr, hr2, hT⟩ := hY
  rcases hT with hT | hT | hT | hT | hT | hT | hT | hT | hT
  · exact h.l2 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.l3 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.u3 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.sp4 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.g2 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.d4 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.l4 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.u4 r Y hr hr2 hT b hb1 hbr hHH E hE hinv
  · exact h.ree r Y hr hr2 hT b hb1 hbr hHH E hE hinv

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
