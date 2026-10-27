module

public import Certificates.Data.Kernel.LyOmega.Chart
public import Certificates.Data.Kernel.LyOmega.Small
public import CFSG.Certificates.Kernel.LyOmega.Defs
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LyOmega.TreeCoreMul
import all CFSG.Certificates.Kernel.LyOmega.SoundMulCore
import all CFSG.Certificates.Kernel.LyOmega.SoundB1
import all CFSG.Certificates.Kernel.LyOmega.SoundC1
import CFSG.Certificates.Kernel.Spor.PackFld

public section

namespace CFSG.KS.LyOm.SpanC

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KS.Ord CFSG.KS.PackFld CFSG.KS.LyOm.TreeCore CFSG.KS.LyOm.MC

theorem bMul7_last_sound {C : BConsts} (hC : bConstsOK C = true) {N Y : ℕ}
    (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y) :
    LCanon 12 7 111 (bMul7 C (last7 C Y) N) ∧
      blkM (bMul7 C (last7 C Y) N) = lastCols (blkM Y) * blkM N := by
  obtain ⟨-, -, -, -, hM, -⟩ := bc_facts hC
  obtain ⟨y, hye, hy, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hY le_rfl
  obtain ⟨n, hne, hn, -⟩ := lc_lanes (n := 111 * 7) (by norm_num) hN le_rfl
  have hl : last7 C Y = (Y >>> (12 * 104)) &&& C.MASK7 := rfl
  rw [hl, hye, hne, hM, cols7_pk hy le_rfl,
    bMul7_pk hC (fun t ht => by split <;> [exact hy _ (by omega); norm_num]) hn]
  refine ⟨lc_of_pk (by norm_num) (fun t _ => Nat.mod_lt _ (by norm_num))
    (fun t h1 h2 => absurd h2 (by omega)) le_rfl, ?_⟩
  ext i l
  simp only [blkM, lastCols, Matrix.mul_apply]
  have e := ent_prod (w := 12) (c := 111) (h := 7) (d := 7) (S := 1332)
    (a := fun s => if s % 111 < 7 then y (s + 104) else 0) (b := n) (by norm_num) (by norm_num)
    i.isLt l.isLt
  beta_reduce at e
  rw [e, ← sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (111 * i.val + k.val) % 111 < 7 := by rw [(dm_eq (by omega)).2]; exact k.isLt
  rw [if_pos hk, ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hy t ht) (by norm_num))
      (show 111 * i.val + (104 + k.val) < 111 * 7 by omega),
    ent_pk (by norm_num) (fun t ht => lt_of_lt_of_le (hn t ht) (by norm_num)) (idx k.isLt l.isLt),
    show 111 * i.val + k.val + 104 = 111 * i.val + (104 + k.val) by ring]

theorem sCountRange_sound {C : SConsts} {KX CT : ℕ → ℕ} {n b₀ c : ℕ}
    (h : sCountRange C KX CT n b₀ c = true) :
    ∀ j < c, sCountLeaf C KX n (b₀ + j) = getRec CT 64 (b₀ + j) := by
  intro j hj
  have := CFSG.KS.LyOm.SB1.allBelow_spec h (by
    rw [CFSG.KS.LyOm.SB1.shr6']
    change c ≤ 64 * (c / 64 + 1)
    omega) j hj
  exact Nat.eq_of_beq_eq_true this

theorem sumBelow_eq (m hi : ℕ) (f : ℕ → ℕ) (hm : m ≤ 64 * hi) :
    sumBelow m hi f = ∑ i ∈ Finset.range m, f i :=
  CFSG.KS.LyOm.SC1.sumBelow_eq' m hi f hm

theorem sCountSum_eq (CT : ℕ → ℕ) (nl : ℕ) :
    sCountSum CT nl = ∑ b ∈ Finset.range nl, getRec CT 64 b := by
  unfold sCountSum
  rw [CFSG.KS.LyOm.SB1.shr6']
  exact CFSG.KS.LyOm.SC1.sumBelow_eq' nl _ _ (by change nl ≤ 64 * (nl / 64 + 1); omega)

end CFSG.KS.LyOm.SpanC

end
