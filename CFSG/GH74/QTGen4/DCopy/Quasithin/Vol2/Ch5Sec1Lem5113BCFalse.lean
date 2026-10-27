module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113BCFalse
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BCSmall
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113BlockBC
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Lem5113Pos

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open Equiv Equiv.Perm
open CFSG.QuasithinUnique.Setup.X3E (Vec lin wmap wapp toVec toVec_wapp exists_toVec toVec_injOn
  toVec_zero)
open CFSG.Quasithin.B45Alt7 (gen7 eval7 indBlk)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt5_1_13_bc_false_of_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51) (h510 : Stmt5_1_10_F4) :
    Stmt5_1_13_bc_false_F4 := by
  intro G _ _ T M L V H B D K₁ X Kh₁ n m hc5 hty hX hnZ hA7 hZL hZK V' hV' _ hnat hT
  obtain ⟨e, pk⟩ := m.exists_a7Pack_F4 h5171 h51 hc5 hX hnZ hA7
  obtain ⟨hOU, hO16⟩ := stmt5_1_13_bc_small_of_F4 h5171 h51 G T M L V H B D K₁ X Kh₁ n m hc5 hty
    hX hnZ hA7 hZL hZK hT
  obtain ⟨D₃, hD₃, h3, hD₃K, hDK, -⟩ := hty.2.2
  obtain ⟨hstab, d₀, hd₀, hd₀0⟩ :=
    m.d3_stab_zero_five_six_F4 h510 hc5 pk.r0 pk.p0 hD₃ h3 hD₃K hDK
  exact m.hyp.toHyp5_0_1.false_of_card_le m.nota.2.1 hZL hV' hnat pk hOU hO16 hT hD₃ h3 hd₀
    (hstab d₀ hd₀) hd₀0

theorem stmt5_1_13_four_block_bc_of_hat_F4 (h5171 : A5.Stmt5_1_7_one_F4) (h51 : AsB51)
    (h510 : Stmt5_1_10_F4) (hhat : Stmt5_1_13_bc_hat_F4) : Stmt5_1_13_four_block_bc_F4 :=
  stmt5_1_13_four_block_bc_of_F4 hhat stmt5_1_13_bc_order_holds
    (stmt5_1_13_bc_false_of_F4 h5171 h51 h510)

end CFSG.Quasithin.H13
