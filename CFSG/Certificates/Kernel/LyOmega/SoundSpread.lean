module

public import CFSG.Certificates.Kernel.LyOmega.TreeSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
import all CFSG.Certificates.Kernel.LyOmega.SoundMulCore
import all CFSG.Certificates.Kernel.LyOmega.TreeSound
import CFSG.Certificates.Kernel.LyOmega.TreeCoreSpread

public section

namespace CFSG.KS.LyOm.SSp

open CFSG.KC.LyOm CFSG.KC.Ord CFSG.KC.LL CFSG.KC.Loop
open CFSG.KS.Ord CFSG.KS.LyOm.MC CFSG.KS.LyOm.TreeCore

private theorem spread_key {MS : List ℕ} (hMS : spMasksOK MS = true) {k : ℕ} (hk : k < 2 ^ 2331) :
    spreadB MS k = pk 12 777 (fun e => k / 2 ^ (3 * e) % 8) := by
  have h2 : k < 2 ^ 196608 :=
    lt_of_lt_of_le hk (Nat.pow_le_pow_right (n := 2) (by norm_num) (show 2331 ≤ 196608 by norm_num))
  rw [spreadB_eq hMS h2]
  change pk 12 65536 (fun e => k / 2 ^ (3 * e) % 8) = _
  refine pk_trunc (by norm_num) fun t ht _ => ?_
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega)))]

theorem spreadB_sound {C : Consts} (hC : constsOK C = true) {k : ℕ} (hk : k < 2 ^ 2331)
    (hf : ∀ e < 777, k / 2 ^ (3 * e) % 8 < 5) :
    LCanon 12 7 111 (spreadB C.MS k) ∧ blkM (spreadB C.MS k) = keyM k := by
  obtain ⟨hMS, -, -⟩ := TreePf.consts3 hC
  rw [spread_key hMS hk]
  refine ⟨lc_of_pk (n := 777) (by norm_num) hf (fun t ht ht' => absurd ht' (by omega)) le_rfl, ?_⟩
  ext i j
  unfold blkM keyM
  rw [ent_pk (c := 111) (by norm_num)
    (fun t ht => lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)) (by omega)]

end CFSG.KS.LyOm.SSp

end
