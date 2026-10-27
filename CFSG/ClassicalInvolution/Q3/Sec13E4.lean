module

public import CFSG.ClassicalInvolution.Q3.Sec13E4U34
public import CFSG.ClassicalInvolution.Q3.Sec13E4A5Iso

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin
open scoped MatrixGroups


theorem nonempty_mulEquiv_alternating_of_psl4 {X : Type} [Group X]
    (e : X ≃* PSL(2, GaloisField 2 2)) : Nonempty (X ≃* alternatingGroup (Fin 5)) := by
  have hcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  obtain ⟨eA⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl hcard)
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _)).trans
    eA⟩

theorem E4Hyp.nonempty_aeIdent_five {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {W : Subgroup G} (h : E4Hyp Ω W) : Nonempty (AEIdent Ω 5) := by
  obtain ⟨K, J, hp⟩ := h.exists_paired
  obtain ⟨hcases, -⟩ := h.quot_cases hp.1
  rcases hcases with ⟨⟨e⟩⟩ | hU
  · obtain ⟨a⟩ := nonempty_mulEquiv_alternating_of_psl4 e
    exact h.nonempty_aeIdent a
  · exact absurd hU (h.not_psu34 hp.1)

theorem dLeafE4_three (IH : ℕ → Prop) : DLeafE4 3 IH := by
  intro G _ _ Ω hc hZ _ W hW hE
  have h : E4Hyp Ω W := ⟨hc.toThmDHyp, hZ, hW, hE⟩
  obtain ⟨I⟩ := h.nonempty_aeIdent_five
  exact hc.not (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨5, le_rfl, ⟨I⟩⟩)))))

end CFSG.ClassicalInvolution.Q3.Sec13
