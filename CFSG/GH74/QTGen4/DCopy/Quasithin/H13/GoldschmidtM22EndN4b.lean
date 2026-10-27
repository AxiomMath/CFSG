module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN4b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.GoldschmidtM22EndN4a

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V : Subgroup G}

namespace PsiData

variable (P : PsiData T L V 3) (h : Hyp6Sec2 G T M L V)

include P h in

theorem oTwoUpper_normalizer_eq_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
    (h621 : Stmt6_2_1_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) :
    oTwoUpper (Subgroup.normalizer (V : Set G)) = L := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hLO : L = oTwoUpper L := by
    refine (h.faithful.2.1 (oTwoUpper L) (oTwoUpper_le L) ?_ fun x hx => ?_).symm
    · exact Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper L)
    · exact exists_pow_mem_oTwoUpper L hx
  rw [P.normalizer_eq_sup_F4 h hZ h621 h629 h6210 h6212]
  refine (eq_oTwoUpper_of_pow_mem le_sup_left (fun x hx => ?_) hLO).symm
  obtain ⟨l, hl, t, ht, rfl⟩ := exists_mul_of_mem_sup hTL hx
  obtain ⟨m, hm⟩ := h.sylow.1 ⟨t, ht⟩
  have hm' : t ^ 2 ^ m = 1 := congrArg Subtype.val hm
  obtain ⟨x', hx', hxx⟩ := A4.exists_pow_mul_eq hl (hTL ht) (2 ^ m)
  exact ⟨m, by rw [hxx, hm', mul_one]; exact hx'⟩

include P h in

theorem pCoreOf_normalizer_eq_F4 (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
    (h621 : Stmt6_2_1_F4) (h629 : Stmt6_2_9_F4) (h6210 : Stmt6_2_10_F4) (h6212 : Stmt6_2_12_F4) :
    pCoreOf 2 (Subgroup.normalizer (V : Set G)) = Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.normalizer (V : Set G) with hN
  have hQT := P.centralizer_le_T_F4 h hZ h621 h629 h6210 h6212
  have hQp : IsPGroup 2 (Subgroup.centralizer (V : Set G)) := h.sylow.1.to_le hQT
  have hQN : Subgroup.centralizer (V : Set G) ≤ N := Subgroup.centralizer_le_normalizer _
  have hNQ : N ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
    intro n hn
    rw [← conjSubgroup_eq_iff_mem_normalizer, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.mpr hn]
  refine le_antisymm ?_ (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQN hNQ hQp)
  set O := pCoreOf 2 N with hO
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian
  have hVO : V ≤ O :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hV2
  have hON : O ≤ Subgroup.normalizer (V : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hOb : O ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  obtain ⟨w, hwV, hw1, hwc⟩ := exists_fixed_mod hOp hVO
    (bot_lt_iff_ne_bot.mpr h.toHyp611.ne_bot) hON hOb
  have hwC : w ∈ Subgroup.centralizer (O : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun o ho => ?_
    have h1 := mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hwc o ho))
    exact (mul_inv_eq_iff_eq_mul.mp h1)
  have hLW : L ≤ Subgroup.normalizer ((V ⊓ Subgroup.centralizer (O : Set G) : Subgroup G) :
      Set G) := by
    intro l hl
    have hlN : l ∈ N := h.toHyp611.L_le_normalizer hl
    have h1 := Subgroup.mem_normalizer_iff.mp hlN
    have hlO : l ∈ Subgroup.normalizer (O : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N hlN
    have h2 : l ∈ Subgroup.normalizer (Subgroup.centralizer (O : Set G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer, CFSG.QuasithinUnique.C5.conjSubgroup_centralizer,
        conjSubgroup_eq_iff_mem_normalizer.mpr hlO]
    have h3 := Subgroup.mem_normalizer_iff.mp h2
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_inf]
    rw [h1 y, h3 y]
  have hW : V ⊓ Subgroup.centralizer (O : Set G) = V := by
    rcases h.natural.irreducible _ inf_le_left hLW with h0 | h1
    · exfalso
      have : w ∈ V ⊓ Subgroup.centralizer (O : Set G) := ⟨hwV, hwC⟩
      rw [h0] at this
      exact hw1 this
    · exact h1
  intro o ho
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hv' : v ∈ V ⊓ Subgroup.centralizer (O : Set G) := hW.symm ▸ hv
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv').2 o ho).symm

end PsiData

end CFSG.Quasithin.H13.GM22
