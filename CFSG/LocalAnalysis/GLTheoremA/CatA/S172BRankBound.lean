module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCType
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

open QuadraticMap Module CFSG.GroupTheory.WeirSylow CFSG.Open CFSG.RankThree.Classical2
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem isFrame_length_lt_of_isPlusType_odd {n : ℕ} {l : List (V × V)} (hl : IsFrame Q l)
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : IsPlusType Q) (hodd : Odd n) : l.length < n := by
  have hle : 2 * l.length ≤ 2 * n := by
    rw [← hdim, ← hl.finrank_Wspan]
    exact Submodule.finrank_le _
  by_contra hlt
  have hlen : l.length = n := by omega
  have htop : Wspan l = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hl.finrank_Wspan, hdim, hlen]
  let e : (Q.comp (Wspan l).subtype).IsometryEquiv Q :=
    { toLinearEquiv := LinearEquiv.ofTop _ htop
      map_app' := fun x => rfl }
  have h := (isPlusType_Wspan_iff hl).1 ((isPlusType_congr e).2 hplus)
  rw [hlen] at h
  exact (Nat.not_even_iff_odd.2 hodd) h

theorem card_le_three_pow_pred_of_isElemAbelian (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : IsPlusType Q) (hodd : Odd n)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEO : E ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ (n - 1) := by
  obtain ⟨l, hl, hEl⟩ := exists_frame_top hQ hEO hE
  have hlt := isFrame_length_lt_of_isPlusType_odd hl hdim hplus hodd
  calc Nat.card E ≤ Nat.card (torus Q l) := Subgroup.card_le_of_le hEl
    _ = 3 ^ l.length := card_torus hl
    _ ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem card_le_three_pow_pred_orthDerived (hQ : (polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hplus : IsPlusType Q) (hodd : Odd n)
    (E : Subgroup ↥(orthDerived Q)) (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ (n - 1) := by
  have hcard : Nat.card (E.map (orthDerived Q).subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (orthDerived Q).subtype_injective
  have hle : E.map (orthDerived Q).subtype ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.map_subtype_le E).trans (Subgroup.commutator_le_self _)
  rw [← hcard]
  exact card_le_three_pow_pred_of_isElemAbelian hQ hdim hplus hodd hle
    (CFSG.SectionRank.isElemAbelian_map hE _)

end CFSG.LocalAnalysis.GLTheoremA.S172B.Rank

end
