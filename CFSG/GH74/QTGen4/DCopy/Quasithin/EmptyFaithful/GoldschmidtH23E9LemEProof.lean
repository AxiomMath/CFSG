module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9LemEDef
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.GoldschmidtH23E9Types
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9GrpSeven
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9LemEProofAux
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9Struct

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem lemma15121E9_of_F4 (hSt : Struct15121E9) (hT : Lemma15120TypesInput_F4)
    (h15 : StageLemma1515CE) (h19s : StageLemma1519) (h14 : StageLemma15114)
    (h113 : StageLemma15113) : Lemma15121E9_F4 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hE h17 h18 h19 hL hLc hant
  exfalso
  have hC := hE.ctx
  have hq := hC.qtfe
  have hM := hC.mf
  have hCE := hC.ce
  have hS := hC.setting
  obtain ⟨hVe, -⟩ := hE.pre.data
  obtain ⟨Y', hYMG, hYJ, hYp, hSY, hVY, hYV, hSV, hVS⟩ := hE.y5
  have h197 := h19.seven L hL.comp hL.quasi hL.not_le
  have hV2N : V₂ ≤ Subgroup.normalizer (L : Set G) := le_sup_right.trans h197.1
  have hYL : Y' ≤ Subgroup.normalizer (L : Set G) :=
    (lemE_le_oTwoUpper hYp hYMG).trans (le_sup_left.trans h197.1)
  have hV16 : Nat.card V₂ = 16 := (hS.ranks_six ⟨5, Or.inr rfl, hE.pre.h5⟩).2.1
  have hV2e : IsElemAbelian 2 V₂ := lemE_isElemAbelian_of_le hVe hS.v2_le
  have h20 := hT G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL
  rcases hSt G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h20 hant with ⟨H, hHB, hHP⟩ | hb | hN
  ·
    obtain ⟨-, hHodd, hHR⟩ := hHP
    have hrel := index_dvd_three_of_odd hq hM hCE hE.pre (h15 G T Mc M hq hM hCE)
      (h19s G T Mc M hq hM hCE) (h14 G T Mc M hq hM hCE) (h113 G T Mc M hq hM hCE).four hHB hHodd
    obtain ⟨hEa, hEb⟩ := hHR _ inf_le_left hrel
    have hH₀V : ∀ h ∈ H ⊓ Subgroup.centralizer (V154 T Mc M : Set G), ∀ v ∈ V₂, v * h = h * v :=
      fun h hh v hv => Subgroup.mem_centralizer_iff.1 hh.2 v (hS.v2_le hv)
    rcases lemE_inf_eq_bot_or_le hV16 hYp hYV hVY hYL with hbot | hVL
    ·
      refine h197.2 (Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun l hl => ?_)
      refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
      exact hEa v (hVS hv) (hV2N hv)
        (fun x hx => lemE_comm_of_inf_eq_bot hSV hV2N hbot hv hx.1 hx.2)
        (fun h hh => hH₀V h hh v hv) l hl
    ·
      obtain ⟨x, hxV, hx1, hxC⟩ := lemE_exists_ne_one (P := s1516 T Z₁ ⊓ L) hV16
        (h18.four.2.1.to_le inf_le_left) (fun y hy w hw => lemE_conj_mem (hSV hy.1) hw)
      have hxc : x ∈ centerOf (s1516 T Z₁ ⊓ L) :=
        show x ∈ (s1516 T Z₁ ⊓ L) ⊓ Subgroup.centralizer ((s1516 T Z₁ ⊓ L : Subgroup G) : Set G)
          from ⟨⟨hVS hxV, hVL hxV⟩, hxC⟩
      have hxL : x ∈ centerOf L := hEb x hxc (fun h hh => hH₀V h hh x hxV)
      have hbot := lemE_inf_center_eq_bot hV16 hYp hYV hVY hYL h197.2
      exact hx1 ((Subgroup.eq_bot_iff_forall _).1 hbot x ⟨hxV, hxL⟩)
  ·
    have hLY : ⁅L, Y'⁆ = ⊥ := hb Y' hYMG (by rw [h17.jS]; exact hYJ) hYp hSY hVY
    have h1 : ⁅⁅Y', L⁆, V₂⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Y' L, hLY, Subgroup.commutator_bot_left]
    have h2 : ⁅⁅L, V₂⁆, Y'⁆ = ⊥ := by
      have hle : ⁅L, V₂⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hV2N
      exact le_bot_iff.1 ((Subgroup.commutator_mono hle le_rfl).trans hLY.le)
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hVY] at h3
    exact h197.2 (by rw [Subgroup.commutator_comm]; exact h3)
  ·
    exact hN V₂ Y' hVS hV2N hV2e hV16 hYL hYV hYp hVY h197.2

end CFSG.Quasithin.E9
