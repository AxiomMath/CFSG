module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Kappa
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Main

public section

namespace CFSG.EvenSmallLie.OmegaEight.Child8

open Subgroup Weyl

namespace Bridge

variable (h : WeylPackage)
include h

theorem card_inf_cent (c : wE8) :
    Nat.card ((ιE1 h).range ⊓ centralizer ({c} : Set wE8) : Subgroup wE8) =
      Nat.card (e1Sub ⊓ centralizer {(c : Equiv.Perm (Fin 240))} :
        Subgroup (Equiv.Perm (Fin 240))) := by
  have heq : (ιE1 h).range ⊓ centralizer ({c} : Set wE8) =
      (e1Sub ⊓ centralizer {(c : Equiv.Perm (Fin 240))}).subgroupOf wE8 := by
    ext y
    rw [Subgroup.mem_inf, mem_subgroupOf, Subgroup.mem_inf, mem_range_ιE1,
      mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => ⟨fun h' => congrArg Subtype.val h', fun h' => Subtype.ext h'⟩
  rw [heq, card_subgroupOf_of_le (inf_le_left.trans h.coords.e1Sub_le)]

theorem coe_s₁s₂ : (((⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩ : wE8) *
    ⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩ : wE8) : Equiv.Perm (Fin 240)) =
      signPerm (vec2 0 2 + vec2 4 6) :=
  S02_mul_S46 h

@[expose] noncomputable def toChild8Weyl : Child8Weyl wE8 where
  Wp := wPlus.subgroupOf wE8
  z := ⟨zPerm, zPerm_mem_wE8 h⟩
  s := ⟨sZero, h.model.sZero_mem⟩
  T := tSub.subgroupOf wE8
  ιE := ιE h
  ιE1 := ιE1 h
  x₀ := ⟨xPlane, xPlane_mem_wE8 h⟩
  s₁ := ⟨signPerm (vec2 0 2), signPerm_mem_wE8 h v02_mem⟩
  s₂ := ⟨signPerm (vec2 4 6), signPerm_mem_wE8 h v46_mem⟩
  normal := normal_wPlus
  perfect := perfect_wPlus h
  card_center := card_center_wPlus h
  lieModel := lieModel_wPlus h
  aut := aut_wPlus h
  fours := fours_wPlus h
  z_mem := mem_subgroupOf.2 h.model.zPerm_mem
  z_comm w := Subtype.ext (h.model.zPerm_comm w w.2)
  z_ne_one hz := h.model.zPerm_ne_one (congrArg Subtype.val hz)
  s_not_mem hs := h.model.sZero_not_mem (mem_subgroupOf.1 hs)
  s_mul_self := Subtype.ext h.model.sZero_sq
  mem_or_mul_mem := mem_or_mul_mem_wPlus h
  mul_self_ne := mul_self_ne_wPlus h
  card_W := card_wE8 h
  card_T := card_tSubW h
  card_Tp := card_tPlusW h
  center_T := center_tSubW h
  center_Tp := center_tPlusW h
  ιE_injective := ιE_injective h
  ιE_evenZ := ιE_evenZ h
  ιE_mem := ιE_mem h
  E_up := E_up h
  E_down := E_down h
  centralizer_E := centralizer_E h
  ιE1_injective := ιE1_injective h
  ιE1_frameZ := ιE1_frameZ h
  ιE1_mem_T := ιE1_mem_T h
  ιE1_mem_iff := ιE1_mem_iff h
  s_mem := s_mem h
  frame_gens := frame_gens h
  frame_up := frame_up h
  centralizer_E1p := centralizer_E1p h
  reps_mem := reps_mem h
  not_conj := not_conj h
  elem_Tp := elem_Tp h
  elem_T := elem_T h
  inv_Wp := inv_Wp h
  inv_W := inv_W h
  x₀_eq := Subtype.ext h.involutions.xPlane_eq
  normal_four := normal_four h
  card_C := card_CW h
  center_C := center_CW h
  s₁_mem := (mem_CW h).2 (S_mem_C h v02_mem)
  s₂_mem := (mem_CW h).2 (S_mem_C h v46_mem)
  zc_s₁ := zc_S h v02_mem S02_mem_sup
  zc_s₂ := zc_S h v46_mem S46_mem_sup
  zc := zc h
  s₁_not_mem := s₁_not_mem h
  s₂_not_mem := s₂_not_mem h
  inv_mul_not_mem := inv_mul_not_mem h
  card_ne₁ := by
    rw [card_inf_cent h, card_inf_cent h, coe_s₁s₂ h]
    exact card_ne_S02 h
  card_ne₂ := by
    rw [card_inf_cent h, card_inf_cent h, coe_s₁s₂ h]
    exact card_ne_S46 h
  comm_eq := comm_eq h
  comm_ne := comm_ne h

end Bridge

theorem childO8PlusCover_of_inputs
    (h : WeylPackage) : ChildO8PlusCover :=
  childO8PlusCover_of_child8Weyl (Bridge.toChild8Weyl h)

end CFSG.EvenSmallLie.OmegaEight.Child8
