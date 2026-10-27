module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN5a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN3a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem subgroupOf_T_eq_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) (a : ↥(HH T)) (haV : (a : G) ∈ V)
    (haC : (a : G) ∉ CHU T L V) :
    T.subgroupOf (HH T) = (Subgroup.zpowers (P.ψ a)).comap P.ψ := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  constructor
  · intro hx
    rcases P.psi_eq_of_mem_M_F4 h h629 a haV haC x (h.T_le hx) with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · rw [h1]
      exact Subgroup.mem_zpowers _
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcomm : P.ψ x * P.ψ a = P.ψ a * P.ψ x := by
      rw [← hk]
      exact ((Commute.refl (P.ψ a)).zpow_left k).eq
    have hxN : (x : G) ∈ Subgroup.normalizer (V : Set G) := ((P.swap_norm a haV haC).2 x).mpr hcomm
    have hxHM : (x : G) ∈ HH T ⊓ M := by
      rw [(h629 G T M L V h).1]
      exact ⟨x.2, hxN⟩
    rw [P.HH_inf_M_eq_T_F4 h hZ h629 h6210 h6212] at hxHM
    exact hxHM

include P h in

theorem card_T_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h629 : Stmt6_2_9_F4)
    (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) : Nat.card ↥T = 2 * Nat.card ↥(CHU T L V) := by
  obtain ⟨a, haV, haC⟩ := exists_a_F4 h hZ h6210
  have hτ : (P.ψ a).IsSwap := (P.swap_norm a haV haC).1
  have hidx : (T.subgroupOf (HH T)).index = 3 := by
    rw [P.subgroupOf_T_eq_F4 h hZ h629 h6210 h6212 a haV haC,
      Subgroup.index_comap_of_surjective _ P.surj]
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers (P.ψ a))
    rw [Nat.card_zpowers, hτ.orderOf, card_perm_fin_three] at h1
    omega
  have h2 := Subgroup.relIndex_mul_card (H := T) (K := HH T)
  rw [inf_eq_left.mpr (T_le_HH T), Subgroup.relIndex, hidx, P.card_HH] at h2
  omega

end PsiData

end CFSG.Quasithin.H13.GM22
