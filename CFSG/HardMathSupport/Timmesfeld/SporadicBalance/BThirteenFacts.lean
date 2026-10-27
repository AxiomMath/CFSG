module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenInputs
public import CFSG.Monster.B.Final.SeedUnit
public import Certificates.Certificate17150

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

section Elements


@[expose] noncomputable def b13Reg (k : ℕ) : NativeSporadic.B := runG (b13Prog ()) bA₁ bA₂ k

@[expose] noncomputable def xB13 : NativeSporadic.B := b13Reg 31

@[expose] noncomputable def t1B13 : NativeSporadic.B := b13Reg 32

@[expose] noncomputable def t2B13 : NativeSporadic.B := b13Reg 44

@[expose] noncomputable def t4B13 : NativeSporadic.B := b13Reg 45

@[expose] noncomputable def t5B13 : NativeSporadic.B := b13Reg 46

@[expose] noncomputable def gB13 : NativeSporadic.B := b13Reg 81

end Elements

structure B13Parts (x t1 t2 t4 t5 g : NativeSporadic.B) : Prop where
  order_x : orderOf x = 13
  mul_self_t1 : t1 * t1 = 1
  ne_one_t1 : t1 ≠ 1
  rank_t1 : Matrix.rank (bMat t1 - 1) = 1860
  comm_t1 : t1 * x = x * t1
  mul_self_t2 : t2 * t2 = 1
  ne_one_t2 : t2 ≠ 1
  rank_t2 : Matrix.rank (bMat t2 - 1) = 1860
  comm_t2 : t2 * x = x * t2
  mul_self_t4 : t4 * t4 = 1
  ne_one_t4 : t4 ≠ 1
  rank_t4 : Matrix.rank (bMat t4 - 1) = 1860
  comm_t4 : t4 * x = x * t4
  mul_self_t5 : t5 * t5 = 1
  ne_one_t5 : t5 ≠ 1
  rank_t5 : Matrix.rank (bMat t5 - 1) = 1860
  comm_t5 : t5 * x = x * t5
  comm_t1_t5 : t1 * t5 = t5 * t1
  ne_t5_t1 : t5 ≠ t1
  order_t1_t2 : orderOf (t1 * t2) = 3
  conj_g : g * x * g⁻¹ = x ^ 6
  comm_g_t1 : g * t1 = t1 * g
  comm_g_t2 : g * t2 = t2 * g
  comm_g_t5 : g * t5 = t5 * g
  w12 : t4 * t2 * t1 * t4 ≠ t1 * t2
  w14 : t2 * t4 * t1 * t2 ≠ t1 * t4
  w15 : t2 * t5 * t1 * t2 ≠ t1 * t5
  w24 : t1 * t4 * t2 * t1 ≠ t2 * t4
  w25 : t1 * t5 * t2 * t1 ≠ t2 * t5
  w45 : t1 * t5 * t4 * t1 ≠ t4 * t5

theorem b13_parts :
    B13Parts xB13 t1B13 t2B13 t4B13 t5B13 gB13 := by
  obtain ⟨hA, hB, hregs, h⟩ := Certificates.certificate17150
  have hR := bMat_runG_of_regsOK hA hB hregs
  have vX : bMat xB13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.X := hR 0 (by norm_num)
  have vT1 : bMat t1B13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.S := hR 1 (by norm_num)
  have vT2 : bMat t2B13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.T2 := hR 2 (by norm_num)
  have vT4 : bMat t4B13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.T4 := hR 3 (by norm_num)
  have vT5 : bMat t5B13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.T5 := hR 4 (by norm_num)
  have vG : bMat gB13 = CFSG.KC.BM.stripMat CFSG.KC.BM.BThirteen.G := hR 5 (by norm_num)
  obtain ⟨hx13, hx1, ⟨hs1, hn1, hr1, hc1⟩, ⟨hs2, hn2, hr2, hc2⟩, ⟨hs4, hn4, hr4, hc4⟩,
    ⟨hs5, hn5, hr5, hc5⟩, h15, hne15, h12, hne12, hgx, hg1, hg2, hg5, hw12, hw14, hw15, hw24,
    hw25, hw45⟩ := h
  have hg6 : gB13 * xB13 = xB13 ^ 6 * gB13 :=
    bMat_injective (by rw [map_mul, map_mul, map_pow, vG, vX]; exact hgx)
  exact
    { order_x := orderOf_of_bMat (by norm_num) (by rw [vX]; exact hx13) (by rw [vX]; exact hx1)
      mul_self_t1 := mul_self_of_bMat (by rw [vT1]; exact hs1)
      ne_one_t1 := ne_one_of_bMat (by rw [vT1]; exact hn1)
      rank_t1 := by rw [vT1]; exact hr1
      comm_t1 := comm_of_bMat (by rw [vT1, vX]; exact hc1)
      mul_self_t2 := mul_self_of_bMat (by rw [vT2]; exact hs2)
      ne_one_t2 := ne_one_of_bMat (by rw [vT2]; exact hn2)
      rank_t2 := by rw [vT2]; exact hr2
      comm_t2 := comm_of_bMat (by rw [vT2, vX]; exact hc2)
      mul_self_t4 := mul_self_of_bMat (by rw [vT4]; exact hs4)
      ne_one_t4 := ne_one_of_bMat (by rw [vT4]; exact hn4)
      rank_t4 := by rw [vT4]; exact hr4
      comm_t4 := comm_of_bMat (by rw [vT4, vX]; exact hc4)
      mul_self_t5 := mul_self_of_bMat (by rw [vT5]; exact hs5)
      ne_one_t5 := ne_one_of_bMat (by rw [vT5]; exact hn5)
      rank_t5 := by rw [vT5]; exact hr5
      comm_t5 := comm_of_bMat (by rw [vT5, vX]; exact hc5)
      comm_t1_t5 := comm_of_bMat (by rw [vT1, vT5]; exact h15)
      ne_t5_t1 := ne_of_bMat (by rw [vT5, vT1]; exact hne15)
      order_t1_t2 := orderOf_of_bMat (by norm_num) (by rw [map_mul, vT1, vT2]; exact h12)
        (by rw [map_mul, vT1, vT2]; exact hne12)
      conj_g := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hg6
      comm_g_t1 := comm_of_bMat (by rw [vG, vT1]; exact hg1)
      comm_g_t2 := comm_of_bMat (by rw [vG, vT2]; exact hg2)
      comm_g_t5 := comm_of_bMat (by rw [vG, vT5]; exact hg5)
      w12 := ne_of_bMat (by simp only [map_mul, vT1, vT2, vT4]; exact hw12)
      w14 := ne_of_bMat (by simp only [map_mul, vT1, vT2, vT4]; exact hw14)
      w15 := ne_of_bMat (by simp only [map_mul, vT1, vT2, vT5]; exact hw15)
      w24 := ne_of_bMat (by simp only [map_mul, vT1, vT2, vT4]; exact hw24)
      w25 := ne_of_bMat (by simp only [map_mul, vT1, vT2, vT5]; exact hw25)
      w45 := ne_of_bMat (by simp only [map_mul, vT1, vT4, vT5]; exact hw45) }

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
