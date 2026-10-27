module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

theorem I294Cfg.le_of_outer_inputs (hK : KDOutDerived) (hO : I294OuterDiag) {p : ℕ} {Y : Type}
    [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y} {D : Subgroup Y}
    (h : I294Cfg p L z g D) : D ≤ L := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  by_cases hAut : AutCommInner ↥L
  · exact le_of_autCommInner h.cent hAut h.odd h.elem h.card h.mem h.ne_one h.diag
  by_contra hDL
  obtain ⟨d, hdD, hdL⟩ := SetLike.not_le_iff_exists.1 hDL
  obtain ⟨d', -, hdd⟩ :=
    exists_commutator_of_isPlaneDiagonal_odd h.odd h.elem h.card h.mem h.ne_one h.diag d hdD
  have hinj := i294_conjNormal_injective (L := L) h.cent
  have hαp : (MulAut.conjNormal (H := L) d) ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, h.elem.2 d hdD, map_one]
  have hαc : MulAut.conjNormal (H := L) d ∈
      commutator (MulAut ↥L) ⊔ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    refine Subgroup.mem_sup_left ?_
    have hcomm : MulAut.conjNormal (H := L) d =
        ⁅MulAut.conjNormal (H := L) (d'⁻¹), MulAut.conjNormal (H := L) g⁆ := by
      rw [hdd, commutatorElement_def]
      simp only [map_mul, map_inv, inv_inv]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hαi : MulAut.conjNormal (H := L) d ∉ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro ⟨l, hl⟩
    apply hdL
    have h2 : MulAut.conjNormal (H := L) (l : Y) = MulAut.conjNormal (H := L) d := by
      rw [MulAut.conjNormal_val]
      exact hl
    have h3 : (l : Y) = d := hinj h2
    rw [← h3]
    exact l.2
  rcases hK p h.prime h.odd ↥L h.simple h.nonab h.catalog hAut _ ⟨1, hαp⟩ hαc hαi with
    hlin | ⟨hp3, hr⟩
  · exact hdL (hO p Y L z g D h hlin hdD)
  · subst hp3
    have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) :=
      CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) L.subtype L.subtype_injective
    have h2 := h.rank
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
