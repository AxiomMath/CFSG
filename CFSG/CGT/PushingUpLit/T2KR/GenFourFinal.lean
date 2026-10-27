module

public import CFSG.CGT.PushingUpLit.T2KR.GenFour
public import CFSG.CGT.PushingUpLit.T2KR.Assemble

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75 CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement
open MData (QM)

variable {G : Type} [Group G] [Finite G]

theorem sectionalTwoRankLE_four_of_QV {L M T : Subgroup G} {n : ℕ} (H : MData G L M n)
    (hn : n = 2) (hQV : QM L M = blockU L) (hTM : T ≤ M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) : CFSG.GH74.SectionalTwoRankLE G 4 := by
  classical
  intro P hP
  obtain ⟨k, -, hk⟩ := exists_conj_le_of_isPGroup hT hP le_top
  have hS2 : IsPGroup 2 (P.map (MulAut.conj k).toMonoidHom) := by
    intro x
    obtain ⟨y, hy, hyx⟩ := x.2
    obtain ⟨m, hm⟩ := hP ⟨y, hy⟩
    refine ⟨m, Subtype.ext ?_⟩
    have := congrArg (fun z : ↥P => (z : G)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hyx]
    show (MulAut.conj k y) ^ 2 ^ m = 1
    rw [← map_pow, this, map_one]
  obtain ⟨s, hsc, hs⟩ := H.exists_card_le_four hn hQV (hk.trans hTM) hS2
  refine ⟨s.image (MulAut.conj k⁻¹), Finset.card_image_le.trans hsc, ?_⟩
  rw [Finset.coe_image]
  change Subgroup.closure ((MulAut.conj k⁻¹).toMonoidHom '' (s : Set G)) = P
  rw [← MonoidHom.map_closure, hs, Subgroup.map_map]
  have : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj k).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply]
    group
  rw [this, Subgroup.map_id]

omit [Finite G] in
theorem le_of_isSylowOf {T K : Subgroup G} (h : CFSG.ABGLocalTools.IsSylowOf 2 T K) : T ≤ K := by
  obtain ⟨Q, rfl⟩ := h
  exact Subgroup.map_subtype_le _

theorem print611Gen4 : Print611Gen4 := by
  intro G _ _ L M T n D g hE1 hs hP hD
  have hD0 : D ≠ ⊥ := by
    rintro rfl
    simp at hD
  rcases hP.step66 with hBLQ | ⟨hD', -⟩
  · have hQV := hP.QM_eq_blockU_of_card_two hBLQ hD
    obtain ⟨-, -, hn⟩ := hP.step610 hBLQ
    exact hs.sec6.sec4.noG4 (sectionalTwoRankLE_four_of_QV (MData.ofSec6 hE1 hs.sec6) hn hQV
      (le_of_isSylowOf hs.sec6.sec4.sylow) hs.sec6.sec4.sylowG)
  · exact hD0 hD'

end CFSG.CGT.PushingUpLit.T2KR
