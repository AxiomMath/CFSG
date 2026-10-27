module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

namespace Ivk93WSp4

variable {F : Type} [Field F] [Finite F]

theorem false_of_u2 (hodd : Odd (Nat.card F)) {q : ℕ}
    {B : Subgroup (StatedProj (StatedSp 2 F))} (h : Ivk93W (u2 F) q B) : False := by
  obtain ⟨hB, h5⟩ := pComponent_centralizer_u2 hodd h.le h.comp.2
  subst hB
  have hsimp : IsSimpleGroup ↥(Lsub F) := isSimpleGroup_Lsub (by omega)
  have hz : (⟨u2 F, h.mem⟩ : ↥(Lsub F)) ∈ Subgroup.center ↥(Lsub F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (h.le g.2))
  rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(Lsub F)) with hc | hc
  · rw [hc, Subgroup.mem_bot] at hz
    exact h.ne_one (congrArg Subtype.val hz)
  · apply h.not_solvable
    refine Group.isSolvable_of_comm fun a b => ?_
    have hb : b ∈ Subgroup.center ↥(Lsub F) := by rw [hc]; exact Subgroup.mem_top _
    exact Subgroup.mem_center_iff.mp hb a

theorem false_of_u1 (hodd : Odd (Nat.card F)) {q : ℕ}
    {B : Subgroup (StatedProj (StatedSp 2 F))} (h : Ivk93W (u1 F) q B) : False := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨-, h5⟩ := pComponent_centralizer_u1 hodd h.le h.comp.2
  have h4 : 4 ≤ Nat.card F := by omega
  have e1 : E1 F = B := h.uniq _ ⟨E1_le_centralizer_u1 h2, isPComponent_E1 h2 h4⟩
  have e2 : E2 F = B := h.uniq _ ⟨E2_le_centralizer_u1 h2, isPComponent_E2 h2 h4⟩
  have e12 : E1 F = E2 F := e1.trans e2.symm
  exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple (isQuasisimple_E1 h2 h4)
    (Group.isSolvable_of_comm fun a b => Subtype.ext (commute_E1_E2 a.2 (e12 ▸ b.2)))

end Ivk93WSp4

theorem ivk93w_sp4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f →
    Ivk93WEmpty (fun X _ => LieModel X .PSp 2 p f) := by
  intro p f hp hp2 hf J _ _ hJ x q B h _
  obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hJ
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h1 := h.of_equiv e
  obtain ⟨g, hg⟩ := exists_conj_of_orderOf_eq_two hodd h1.ord
  set φ : StatedProj (StatedSp 2 F) ≃* StatedProj (StatedSp 2 F) := MulAut.conj g⁻¹ with hφ
  have h2 := h1.of_equiv φ
  have hφx : φ (e x) = g⁻¹ * e x * g := by simp [hφ]
  rcases hg with hg | hg
  · rw [hφx, hg] at h2
    exact Ivk93WSp4.false_of_u1 hodd h2
  · rw [hφx, hg] at h2
    exact Ivk93WSp4.false_of_u2 hodd h2

end CFSG.GH74.GLS.IVK.Proofs2
