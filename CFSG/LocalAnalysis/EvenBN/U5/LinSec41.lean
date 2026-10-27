module

public import CFSG.LocalAnalysis.EvenBN.U5.LinParts
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofThirteenA

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ABGLocalTools (IsSylowOf)
open scoped MatrixGroups

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec41_of_hyp (hl : d.LinCtx) (k : d.Know12) (c : d.CaseBData)
    (hz : Nat.card (CFSG.centerIn (d.Uc c.S c.X)) ≤ (2 ^ f) ^ 4) : c.Sec41 := by
  have hp : d.CaseHyp := hl.toCaseHyp
  have hk := c.card_k
  have hcen : CFSG.centerIn (d.Uc c.S c.X) =
      d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) :=
    s313a_centerIn_Uc hp k c.S_syl c.P_le_S c.ψ hk
  obtain ⟨P', hP'X, hsup, hinf, ⟨θ, hθ, hθr⟩, ⟨θ', hθ', hθ'r⟩⟩ :=
    s313a_pair hp k c.S_syl c.P_le_S c.ψ hk hz
  refine ⟨hcen, ?_, ⟨P', hP'X, hsup, hinf, ⟨θ, hθ, hθr⟩, ⟨θ', hθ', hθ'r⟩⟩, ?_⟩
  ·
    rw [hcen]
    have h1 : Nat.card (Set.range θ) =
        Nat.card (d.F ⊓ centralizer ((c.X ⊓ c.S : Subgroup G) : Set G) : Subgroup G) := by
      change Nat.card (Set.range θ) = Nat.card (d.F ⊓ centralizer
        ((Common.prodFactorOne c.ψ ⊓ c.S : Subgroup G) : Set G) : Subgroup G)
      rw [hθr]
      rfl
    rw [← h1, Nat.card_range_of_injective hθ.injective, Nat.card_fun,
      Nat.card_eq_fintype_card (α := c.k), hk]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  · intro y hy hodd hy1 z hz' hfix
    exact s313a_free hp k c.S_syl c.P_le_S c.ψ hk hz hy hodd hy1 hz' hfix

end Data

end CFSG.LocalAnalysis.EvenBN.U5
