module

public import CFSG.Certificates.Kernel.SporSch.Co1VOrbProved

public section

namespace CFSG.KS.SporSch.VOrb

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw

theorem vorbK_sound {A B v₀ n NS L : Nat} {T S C : Nat → Nat}
    (hr : ptK T 0 = v₀) (hn0 : 0 < n) (hn : n < 131072) (hL : n ≤ NS * L)
    (hc0 : C 0 = 1) (hcN : C NS = n)
    (hb : ∀ s < NS, bfsSl A B T n (s * L) L (C s) (C (s + 1)) = true)
    (hp : ∀ s < NS, permSl S T n (s * L) L = true) :
    enumOK (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B)) v₀ n
        (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B))
          v₀ n) = true ∧
      (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A)) (transposeRows 24 (unpack 24 24 B))
          v₀ n).pts.size = n ∧
      (∀ i < n, (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A))
          (transposeRows 24 (unpack 24 24 B)) v₀ n).pts[i]! = ptK T i) ∧
      ∀ v, ((List.range n).any fun i => (vOrbitBFS 24 (transposeRows 24 (unpack 24 24 A))
          (transposeRows 24 (unpack 24 24 B)) v₀ n).pts[i]! == v) = memK T S n v :=
  vorbK_sound_proved hr hn0 hn hL hc0 hcN hb hp

end CFSG.KS.SporSch.VOrb

end
