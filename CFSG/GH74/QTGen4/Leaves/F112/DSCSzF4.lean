module

public import CFSG.GH74.QTGen4.Leaves.F112.FDBigF4
public import CFSG.GH74.QTGen4.Leaves.F112.VU3twoF4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsDS
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs

public section

namespace CFSG.GH74.QTGen4.Leaves.F112

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem dsC_F4_holds : CFSG.Quasithin.H13.DSCStatement_F4 := by
  intro G _ _ L1 L2 S hyp hq hS hns hD
  have h : F112Hyp L2 L1 S := F112Hyp.symm ⟨hyp, hq, hS⟩
  exact CFSG.Quasithin.f112_fd_big_false_finite4 G L2 L1 S h hD (vBig_of_not_isSolvable hns)

theorem dsSz_F4_holds : CFSG.Quasithin.H13.DSSzStatement_F4 := by
  intro G _ _ L1 L2 S hyp hq hS hSz _
  exfalso
  obtain ⟨a, ha, ⟨e⟩⟩ := hSz
  obtain ⟨ψ, hψ⟩ := exists_injective_oTwoQuot_to_GL4
    (CFSG.GH74.QTGen4.Finite4.gen4 (G := G)) hyp.h1
  have hdvd := CFSG.GH74.QTGen4.U42.VertexGen4B.card_dvd_GL4 (ψ.comp e.symm.toMonoidHom)
    (hψ.comp e.symm.injective)
  rw [CFSG.GH74.QTGen4.U42.VertexGen4B.card_sz_formula ha] at hdvd
  have hq8 : 8 ≤ 2 ^ (2 * a + 1) := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  exact absurd hle (not_le.mpr (CFSG.GH74.QTGen4.U42.VertexGen4B.sz_card_gt hq8))

end CFSG.GH74.QTGen4.Leaves.F112
