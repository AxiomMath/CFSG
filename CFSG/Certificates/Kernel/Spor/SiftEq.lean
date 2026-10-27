module

public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Spor.SiftKComplete

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem siftK_eq {n w kS nb BP : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {base : Array Nat} {g : Array Nat} {G : Nat}
    (hb : Binds n w PS kS nb BP S base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hg : g = unpack n w G) (hG : Nat.shiftRight G (n * w) = 0)
    (hr : allN n (fun i => Nat.blt (pg w (mask w) G i) n) = true) :
    siftA n (rawLevels n S base) base 0 g = siftK n w (mask w) (n * w) (pidn n w) LR TRI BP nb 0 G :=
  Bool.eq_iff_iff.2 ⟨Orb.siftK_of_siftA hb hp hl hg hG hr, siftK_soundR hb hp hl hg hG hr⟩

end CFSG.KS.Raw

end
