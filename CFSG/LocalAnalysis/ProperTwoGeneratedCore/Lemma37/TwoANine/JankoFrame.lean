module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoNormalizerE
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPTwoThreeSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoStatementsFrame
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFEF

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

namespace Janko

variable {G : Type} [Group G] {z : G}

noncomputable def frame (hz : orderOf z = 2) (hH : IsTwoANine (centralizer ({z} : Set G)))
    (e : centralizer ({z} : Set G) ⧸ center (centralizer ({z} : Set G)) ≃*
      alternatingGroup (Fin 9)) : JankoFrame G z where
  s₁ := s₁ e
  s₂ := s₂ e
  s₃ := s₃ e
  t := t e
  ℓ := ℓ e
  P₁ := zpowers (s₁ e)
  P₂ := zpowers (s₂ e)
  P₃ := zpowers (s₃ e)
  E := E e
  F := F e
  EF := E e ⊓ F e
  F₁ := F e ⊓ centralizer ({t e} : Set G)
  S₁ := S₁ e
  P := P e
  K := K e
  L := closure {ℓ e, t e}
  L₁ := zpowers (ℓ e)
  Q := closure {ℓ e ^ 2, t e * ℓ e}
  D := closure {t e, ℓ e ^ 2}
  V := closure {t e, z}
  P₁_eq := rfl
  P₂_eq := rfl
  P₃_eq := rfl
  EF_eq := rfl
  F₁_eq := rfl
  L_eq := rfl
  L₁_eq := rfl
  Q_eq := rfl
  D_eq := rfl
  V_eq := rfl
  orderOf_s₁ := orderOf_s₁ hH e
  orderOf_s₂ := orderOf_s₂ hH e
  orderOf_s₃ := orderOf_s₃ hH e
  orderOf_t := orderOf_t hH e
  t_mem := t_mem e
  t_ne := t_ne e
  orderOf_ℓ := orderOf_ℓ hz hH e
  ℓ_pow_four := ℓ_pow_four hz hH e
  t_mul_ℓ := t_mul_ℓ hH e
  t_mul_s₁ := t_mul_s₁ hH e
  ℓ_mem_F := ℓ_mem_F e
  card_centralizer_s₁ := card_centralizer_s₁ hH e
  card_centralizer_s₂ := card_centralizer_s₂ hH e
  card_centralizer_s₃ := card_centralizer_s₃ hH e
  exists_conj := exists_conj hH e
  exists_invert := exists_invert hH e
  F_le := F_le e
  F_le_centralizer := F_le_centralizer hH e
  P₁_inf_F := P₁_inf_F hH e
  centralizer_P₁ := centralizer_P₁ hH e
  card_F := card_F hH e
  z_mem_F := z_mem_F e
  eq_z_of_mem_F := eq_z_of_mem_F hz hH e
  z_mem_of_normal := z_mem_of_normal hz hH e
  card_le_of_odd := card_le_of_odd hH e
  S₁_le := S₁_le e
  S₁_quaternion := S₁_quaternion hz hH e
  card_EF := card_EF hH e
  centralizer_EF := centralizer_EF hz hH e
  normalizer_EF := normalizer_EF hz hH e
  exists_even_card := exists_even_card hz hH e
  t_mem_normalizer_F := t_mem_normalizer_F e
  card_F₁ := card_F₁ hH e
  P₂_le_F₁ := P₂_le_F₁ hH e
  not_le_normalizer_P₂ := not_le_normalizer_P₂ hH e
  E_le := E_le e
  card_E := card_E hH e
  E_comm := E_comm hH e
  E_pow_three := E_pow_three hH e
  E_eq_closure := E_eq_closure hH e
  s₃_mem_E := s₃_mem_E hH e
  E_inf_centralizer_t := E_inf_centralizer_t hH e
  centralizer_E := centralizer_E hH e hz
  centralizer_P₂ := centralizer_P₂ hH e hz
  D_le_normalizer := D_le_normalizer hH e
  card_normalizer_P₂ := card_normalizer_P₂ hH e
  card_D := card_D hH e
  D_center := D_center hH e hz
  D_inf_centralizer := D_inf_centralizer hH e hz
  card_type_s₃_E := card_type_s₃_E hH e
  exists_ne_type_s₃ := exists_ne_type_s₃ hH e
  K_le := K_le e
  card_K := card_K hz hH e
  K_le_normalizer := K_le_normalizer hH e
  E_inf_K := E_inf_K hH e
  normalizer_E := normalizer_E hz hH e
  card_ne_three := card_ne_three hz hH e
  L_le_K := L_le_K e
  normalizer_E_inf_P₁ := normalizer_E_inf_P₁ hz hH e
  card_L := card_L hz hH e
  L_inf_centralizer := L_inf_centralizer hz hH e
  mul_s₁_of_not_mem := mul_s₁_of_not_mem hz hH e
  eq_of_le_L := eq_of_le_L hz hH e
  Q_quaternion := Q_quaternion hz hH e
  eq_z_of_mem_Q := eq_z_of_mem_Q hz hH e
  P_le := P_le e
  card_P := card_P hH e
  centralizer_P₃ := centralizer_P₃ hH e hz
  exists_orderOf_nine := exists_orderOf_nine hH
  exists_ne_comm := exists_ne_comm hH
  card_eq_of_odd := card_eq_of_odd hH
  card_centralizer_inv := card_centralizer_inv hH
  card_centralizer_involution := card_centralizer_involution hH hz
  type_s₂_of_involution := type_s₂_of_involution hH hz
  type_s₃_of_conj := type_s₃_of_conj hH
  le_normalizer_E := le_normalizer_E hH e

end Janko

theorem jankoFrameExists : JankoFrameExists := by
  intro G _ _ z hz hH
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  exact ⟨Janko.frame hz hH e⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
