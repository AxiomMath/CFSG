module

public import CFSG.GH74.Uniqueness.Section6Lemma62
public import CFSG.GH74.Uniqueness.Section6ZJ

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Prop78

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem T4Max.card_ne_zNumShare (S : ZDSetup X Z M) (h72 : Prop72Stmt Z M)
    (hC64 : Cor64Stmt Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Max Z M z p W) :
    Nat.card (CFSG.OddInversion.invertedSet W z) ≠ zNumShare Z M p := by
  intro hcard
  have hcand := hW.cand
  have : Fact p.Prime := ⟨hcand.prime⟩
  obtain ⟨β, hβ, hβM, hθ⟩ := h72 z p W hW
  obtain ⟨Q, hQ, hzQ⟩ := (S.lemma62 z p W hW β hβ hβM).mpr hcard
  have hzθ : z ∈ normalizer ((oPrimePrime p (M ⊓ β) : Subgroup X) : Set X) := by
    rw [hθ, Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top z
  obtain ⟨-, hnorm⟩ := hC64 z p W hcand β hβ hβM hzθ
  have hSyl : ∃ Q' : Subgroup X, ABGLocalTools.IsSylowOf p Q' (pPrimeCoreIn (M ⊓ β)) ∧ Q' ≤ Q :=
    ⟨Q ⊓ pPrimeCoreIn (M ⊓ β),
      hQ.inf_of_le_normalizer (pPrimeCoreIn_le _) (pPrimeCoreIn_normalizes _), inf_le_left⟩
  exact hnorm Q hQ.le hQ.isPGroup hSyl
    (normalizer_le_normalizer_zjSubgroup p hcand.prime Q hzQ)

theorem ZDSetup.prop79 (S : ZDSetup X Z M) (h72 : Prop72Stmt Z M) (hC64 : Cor64Stmt Z M) :
    Prop79Stmt Z M := fun _ _ _ hW =>
  lt_of_le_of_ne (hW.cand.card_invertedSet_le S.invariant S.prodDisc)
    (T4Max.card_ne_zNumShare S h72 hC64 hW)

theorem ZDSetup.prop78 (S : ZDSetup X Z M) (hC57 : Cor57Stmt Z M) (h72 : Prop72Stmt Z M)
    (hC64 : Cor64Stmt Z M) : Prop78Stmt Z M := by
  intro z p W hW
  by_contra hnot
  exact T4Max.card_ne_zNumShare S h72 hC64 hW
    (T4Max.card_eq_zNumShare_of_not_doublyTransitive S hC57 hW hnot)

end Prop78

end CFSG.GH74.Uniqueness
