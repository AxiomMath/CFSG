module

public import CFSG.GH74.AS16.E2.Leaves
public import CFSG.GH74.AS16.E2.ShapeCards
public import CFSG.GH74.E2.Terminal

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.Blueprint
open CFSG.GH74.E2 hiding Hyp

theorem s_alss3121E2_of_leaves
    (hCL : ComponentList) (hP : PumpUpData) (hl : E2Leaves) :
    S_ALSS3121E2 := by
  intro G _ _ hH he
  by_contra hnot
  obtain ⟨T, z, L, hp⟩ := exists_pair (hyp_of_e2 hH he hnot).e1 hnot
  have hcfg : Cfg G T z L :=
    ⟨hH, he, hp, fun y hy K hK => (hCL G hH y hy K hK).1,
      fun y hy K K' hK hK' => ((hCL G hH y hy K hK).2 K' hK').symm⟩
  have hshape : K0Shape ↥L := (hCL G hH z hp.orderOf_eq L hp.isComp).1
  have hterm : ∀ (h60 : Nat.card ↥L ≠ 60) (h120 : Nat.card ↥L ≠ 120),
      GLS.IsTerminalPair 2 z L := fun h60 h120 =>
    isTerminalPair_of_card hCL hP hH hp.orderOf_eq hp.isComp h60 h120
  rcases hshape with h | h | h | h | h | h | h | h | h | h | h
  ·
    by_cases ht : Terminal L
    · obtain ⟨-, hc, -⟩ := hH.restrictedEven.2.2.1 z L (hcfg.isTerminalPair ht) 5 1
        Nat.prime_five (by norm_num) (lieModel_of_shapeA5 h)
      exact hc hcfg.isCentralInvolution
    · exact hl.a5nt G T z L hcfg h ht
  · exact no_component_L27 hCL hP hH hp.orderOf_eq hp.isComp h
  · obtain ⟨-, hc, -⟩ := a6_terminal_facts hCL hP hH hp.orderOf_eq hp.isComp h
    exact hc hcfg.isCentralInvolution
  · exact no_component_L217 hCL hP hH hp.orderOf_eq hp.isComp h
  · have hc := card_of_shapeL28 h
    exact hl.l28 G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shapeL33 h
    exact hl.l33 G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shapeU33 h
    exact hl.u33 G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shapeSz8 h
    exact hl.sz8 G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shapeM11 h
    exact hl.m11 G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shape2M12 h
    exact hl.m12c G T z L hcfg (hterm (by omega) (by omega)) h
  · have hc := card_of_shape2Sz8 h
    exact hl.sz8c G T z L hcfg (hterm (by omega) (by omega)) h

end CFSG.GH74.AS16.E2
