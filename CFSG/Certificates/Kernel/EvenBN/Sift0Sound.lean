module

public import CFSG.Certificates.Kernel.Spor.RawDefs
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

namespace CFSG.KS.Raw.Orb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.KS.Raw

theorem siftA_false_of_out {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hnb : 0 < nb) (hz : g[base[0]!]! < n)
    (h : Nat.ble (rcnt (LR 0)) (rpos w (mask w) (n * w) (LR 0) g[base[0]!]!) = true) :
    siftA n (rawLevels n S base) base 0 g = false := by
  have hbl := base_lt_of_levels hb hl
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have A := (agree_levelK hb hp hbl hnb (hl 0 hnb)).1
  have hls : 0 < (rawLevels n S base).size := by rw [chainLevels_size]; omega
  rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
  left
  intro hk
  have h1 := (A.pos _ hz).2 hk
  have h2 := Nat.le_of_ble_eq_true h
  omega

end CFSG.KS.Raw.Orb

end
