module

public import CFSG.GH74.GLS.Stage2.Final.ModelIVKGen

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup CFSG.GH74.GLS
  CFSG.GH74.GLS.Stage1.Thm3.Sec7

variable {F : Type} [Field F]

theorem lin410 [Finite F] (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ Nat.card F) (hq4 : Nat.card F % 4 = 3)
    (hpgl : PglStmt (ModelData.lin F) (Nat.card F) (dP _ (dRefl F) (Subgroup.mem_top _))) :
    ∃ S : Sylow 2 (PG (ModelData.lin F)),
      CenterIs (S : Subgroup (PG (ModelData.lin F))) (yP _) ∧
      Dat410 (Nat.card F) (yP _) (S : Subgroup (PG (ModelData.lin F))) (tP _)
        (dP _ (dRefl F) (Subgroup.mem_top _)) (K1 _) (K2 _) := by
  have hG := goodModel_lin h2 h5
  have hZ := zsTwo_lin hq4
  have hF := luFacts_lin h2
  have hC := clsFacts_lin h2 h5 hq4
  have hd : dRefl F ∈ (ModelData.lin F).U2 := Subgroup.mem_top _
  have hq : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have hU : Nat.card ↥(ModelData.lin F).U2 =
      Nat.card ↥(ModelData.lin F).H2 * (Nat.card F - 1) := card_U2_lin
  have hidx := index_E_Cg_eq (ModelData.lin F) (card_Cg_eq hG hZ hU)
  obtain ⟨k, hk⟩ : ∃ k, Nat.card F = 4 * k + 3 := ⟨Nat.card F / 4, by omega⟩
  have hN : ∀ l m : Fˣ, diagGL (sc2 l) (sc2 m) ∈ (ModelData.lin F).K4 →
      l ^ (Nat.card F - 1) = 1 ∧ m ^ (Nat.card F - 1) = 1 :=
    fun l m _ => ⟨pow_card_sub_one_lin l, pow_card_sub_one_lin m⟩
  obtain ⟨S, -, hsyl, hdec⟩ := exists_luSylow hG hF hd dRefl_pow_four (hdet_zs h2 hZ) hd
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega)
    (hcs_gen _ (N := Nat.card F - 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  refine ⟨S, (centerIs_iff _ _).1 hsyl.z_cen, ?_⟩
  exact dat410_generic hG hZ hC hq (hasSL2Model_H2_lin F) (J0_mem_H2_lin F) (jj_conj_lin h2)
    hsyl.t_mem hsyl.u_mem (Or.inr hsyl.u_ord) (dP_mem_C0 _ hd) hsyl.u_norm
    (Or.inr (dP_not_mem_E _ hd (hdet_zs h2 hZ))) hsyl.ut.symm hdec hsyl.t_conj (fun _ => hpgl)
    (fun _ => ⟨tP_mul_dP_conj_y hC hd, fun x hx hxw =>
      E_mul_w_conj_y hG hZ hC hd dRefl_mul_self det_dRefl hx.2 hxw⟩)

theorem uni410 [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1)
    (hpgl : PglStmt (ModelData.uni hF) (p ^ f) (dP _ (dRefl F) dRefl_mem_uni)) :
    ∃ S : Sylow 2 (PG (ModelData.uni hF)),
      CenterIs (S : Subgroup (PG (ModelData.uni hF))) (yP _) ∧
      Dat410 (p ^ f) (yP _) (S : Subgroup (PG (ModelData.uni hF))) (tP _)
        (dP _ (dRefl F) dRefl_mem_uni) (K1 _) (K2 _) := by
  have hG := goodModel_uni hF hp2 h5
  have hZ := zsTwo_uni hF hq4
  have hFu := luFacts_uni hF hp2
  have hC := clsFacts_uni hF hp2 h5 hq4
  have hd : dRefl F ∈ (ModelData.uni hF).U2 := dRefl_mem_uni
  have hq : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
  have hU := card_U2_uni hF hp2
  have hidx := index_E_Cg_eq (ModelData.uni hF) (card_Cg_eq hG hZ hU)
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = 4 * k + 1 := ⟨p ^ f / 4, by omega⟩
  have hN := hN_uni hF
  obtain ⟨S, -, hsyl, hdec⟩ := exists_luSylow hG hFu hd dRefl_pow_four (hdet_zs hG.two_ne_zero hZ) hd
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (o := 2 * k + 1) ⟨k, rfl⟩
    (by rw [hidx]; omega)
    (hcs_gen _ (N := p ^ f + 1) (by omega) (fun l m hlm => (hN l m hlm).1))
  refine ⟨S, (centerIs_iff _ _).1 hsyl.z_cen, ?_⟩
  exact dat410_generic hG hZ hC hq (hasSL2Model_H2_uni hF) (J0_mem_H2_uni hF)
    (jj_conj_uni hF hG.two_ne_zero hq4) hsyl.t_mem hsyl.u_mem (Or.inr hsyl.u_ord)
    (dP_mem_C0 _ hd) hsyl.u_norm (Or.inr (dP_not_mem_E _ hd (hdet_zs hG.two_ne_zero hZ)))
    hsyl.ut.symm hdec hsyl.t_conj (fun _ => hpgl)
    (fun _ => ⟨tP_mul_dP_conj_y hC hd, fun x hx hxw =>
      E_mul_w_conj_y hG hZ hC hd dRefl_mul_self det_dRefl hx.2 hxw⟩)

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
