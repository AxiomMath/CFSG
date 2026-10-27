module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem517A5Phi
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem517A5G

public section

namespace CFSG.Quasithin.H13.A5Push

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin Equiv

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting_F4
open CFSG.Quasithin.H13.A5Push.Setting_F4

variable {T M L W : Subgroup G} {F : S5Frame (L ⊔ T) W} {n : ℕ}

theorem sqSub_Q_le_F4 (hs : Setting_F4 T M L W F n) :
    sqSub (baum T ⊓ Subgroup.centralizer (W : Set G)) ≤
      sqSub (baum T ⊓ Subgroup.centralizer (L : Set G)) := by
  rw [sqSub, Subgroup.closure_le]
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨w, hw, c, hc, rfl⟩ := hs.mem_decomp_F4 hq
  have hwc : Commute w c := Subgroup.mem_centralizer_iff.mp hc.2 w (hs.W_le_L_F4 hw)
  have hww : w * w = 1 := by rw [← pow_two]; exact hs.hB.el.2 w hw
  have e : w * c * (w * c) = c * c := by
    rw [hwc.symm.mul_mul_mul_comm w c, hww, one_mul]
  show w * c * (w * c) ∈ sqSub (baum T ⊓ Subgroup.centralizer (L : Set G))
  rw [e]
  exact mul_self_mem_sqSub hc

theorem sqSub_QC_eq_bot_F4 (hs : Setting_F4 T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hkW : ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    sqSub (baum T ⊓ Subgroup.centralizer (L : Set G)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := sqSub (baum T ⊓ Subgroup.centralizer (L : Set G)) with hD

  have hle : D.map (MulAut.conj k).toMonoidHom ≤ D := by
    refine (sqSub_conj_le_sqSub _ k).trans ?_
    refine le_trans ?_ hs.sqSub_Q_le_F4
    rw [sqSub, sqSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_self_mem_sqSub (hs.QC_conj_le_F4 hk hkW hx)
  have heq : D.map (MulAut.conj k).toMonoidHom = D :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj k).injective).ge
  have hkD : k ∈ Subgroup.normalizer (D : Set G) := by
    refine mem_normalizer_of_conj (fun x hx => ?_) fun x hx => ?_
    · rw [← heq]
      exact conj_mem_conj_map hx
    · rw [← heq, mem_conj_map] at hx
      exact hx
  by_contra hne

  have hLD : L ≤ Subgroup.normalizer (D : Set G) := by
    intro l hl
    have hc : ∀ x ∈ D, l * x * l⁻¹ = x := by
      intro x hx
      have hx' := (sqSub_le _ hx).2
      rw [Subgroup.mem_centralizer_iff.mp hx' l hl, mul_inv_cancel_right]
    refine mem_normalizer_of_conj (fun x hx => by rw [hc x hx]; exact hx) fun x hx => ?_
    have h1 : l⁻¹ * x * l = x := by
      calc l⁻¹ * x * l = l⁻¹ * (l * x * l⁻¹) * l := by rw [hc x hx]
        _ = x := by group
    rw [h1]
    exact hx
  have hD2 : IsPGroup 2 D :=
    hs.hyp.sylow.1.to_le ((sqSub_le _).trans (inf_le_left.trans (Setting.S_le_T T)))
  have hkM : k ∈ M := hs.hyp.normalizer_le_of_le_F4 hs.h432 hne hD2 hLD hkD
  apply hkW
  rw [conj_map_le_iff]
  intro w hw
  exact hs.W_le_Q_F4 ((Subgroup.mem_normalizer_iff.mp (hs.M_le_normalizer_F4 hkM) w).mp hw)

theorem isElemAbelian_QC_F4 (hs : Setting_F4 T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hkW : ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (L : Set G)) := by
  refine isElemAbelian_of_mul_self fun x hx => ?_
  have h1 := mul_self_mem_sqSub hx
  rw [hs.sqSub_QC_eq_bot_F4 hk hkW, Subgroup.mem_bot] at h1
  exact h1

theorem isElemAbelian_Q_F4 (hs : Setting_F4 T M L W F n) {k : G}
    (hk : k ∈ Subgroup.normalizer (baum T : Set G))
    (hkW : ¬ W.map (MulAut.conj k).toMonoidHom ≤ baum T ⊓ Subgroup.centralizer (W : Set G)) :
    IsElemAbelian 2 (baum T ⊓ Subgroup.centralizer (W : Set G)) := by
  have hQC := hs.isElemAbelian_QC_F4 hk hkW
  refine isElemAbelian_of_mul_self fun q hq => ?_
  obtain ⟨w, hw, c, hc, rfl⟩ := hs.mem_decomp_F4 hq
  have hwc : Commute w c := Subgroup.mem_centralizer_iff.mp hc.2 w (hs.W_le_L_F4 hw)
  have hww : w * w = 1 := by rw [← pow_two]; exact hs.hB.el.2 w hw
  have hcc : c * c = 1 := by rw [← pow_two]; exact hQC.2 c hc
  rw [hwc.symm.mul_mul_mul_comm w c, hww, hcc, one_mul]

end Setting_F4

end CFSG.Quasithin.H13.A5Push
