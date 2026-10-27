module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.BProg.Vocab

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

@[expose] def ListedK (J : Type) [Group J] : Prop := QShapeNS J

@[expose] def ListedRankOne (J : Type) [Group J] : Prop :=
  CFSG.pRank 2 J ≤ 1 ∧ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel (J ⧸ center J) .PSL 2 p f

theorem mem_conjugate_iff_aux {Y : Type*} [Group Y] {L : Subgroup Y} {d x : Y} :
    x ∈ conjugate L d ↔ d * x * d⁻¹ ∈ L := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 : d * (MulEquiv.toMonoidHom (MulAut.conj d⁻¹)) y * d⁻¹ = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
    rw [h1]; exact hy
  · intro hx
    refine ⟨d * x * d⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_normalizer_of_conjugate_eq {Y : Type*} [Group Y] {L : Subgroup Y} {d : Y}
    (h : conjugate L d = L) : d ∈ normalizer (L : Set Y) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff_aux, h]

@[expose] def ListedPair (J : Type) [Group J] : Prop :=
  IsSimpleGroup J ∧ (QShape3 J ∨ QShape4 J ∨ QShape5 J)

@[expose] def RankOneRecog : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → CFSG.pRank 2 J ≤ 1 →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel (J ⧸ center J) .PSL 2 p f) ∨
      (Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∧ center J ≠ ⊥)

end CFSG.GH74.Generic.BProg.B2
