module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCHat
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BCFalse

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E (Vec lin wmap papply toVec toVec_papply toVec_xor
  exists_toVec toVec_injOn toVec_zero wmap_cons papply_lt)
open CFSG.Quasithin.B45Alt7 (gen7 eval7 indBlk closure_gen7)
open scoped Pointwise

theorem stmt5_1_13_bc_hat_of_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51) : Stmt5_1_13_bc_hat_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 _ hX hnZ hA7 _ hZK hKb
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hX hnZ hA7
  have hT2 : IsPGroup 2 T := m.hyp.toHyp5_0_1.sylow.1
  exact BCHat.card_le_of_block hT2 rfl hc5.1 pk
    (BCHat.inf_centralizer_eq_bot hT2 pk.T_le_K hZK) hKb

theorem stmt5_1_13_four_block_bc_of_inputs_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51)
    (h510 : Stmt5_1_10_F4) : Stmt5_1_13_four_block_bc_F4 :=
  stmt5_1_13_four_block_bc_of_hat_F4 h5171 h51 h510 (stmt5_1_13_bc_hat_of_F4 h5171 h51)

end CFSG.Quasithin.H13
