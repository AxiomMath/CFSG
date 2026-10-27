module

public import Certificates.Data.Kernel.SurjK
public import Certificates.Data.CFSGNative.Bridge.SurjD
import CFSG.Certificates.Kernel.SurjKSeedCore

public section

namespace CFSG.KC.SurjK

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.SmallF2.Native
open CFSG.KS (lget)

theorem seedLetter_sound {D : VecData} {S : Spec} {csA csB : List Char} {A B AI BI : Nat}
    {Ims ImsI : List Nat} {Li Ls : List (List Int)} {PT PA LB AP BP SO SOI : Nat → Nat}
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (hA : m1Bind csA D.d A = true) (hB : m1Bind csB D.d B = true)
    (hAI : mulF D.d A AI = idF D.d) (hBI : mulF D.d B BI = idF D.d)
    (hn : 0 < D.n) (hn32 : D.n < 4294967295) (hd : 0 < D.d)
    (horb : ∀ k < D.n, orbStep D.d D.n A B D.v0 PT PA LB AP BP SO SOI k = true)
    (hm : S.m = Ims.length) (hmI : ImsI.length = Ims.length)
    (hi : S.imgWords = Li.toArray) (hs : S.surjWords = Ls.toArray) (hli : Li.length = S.m)
    (hls : Ls.length = 2)
    (hbase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z < 4)) = true)
    (himg : ∀ k < S.m, matW D.d (baseF A AI B BI) (Li.getD k []) = lget Ims k)
    (hinv : ∀ k < S.m, mulF D.d (lget Ims k) (lget ImsI k) = idF D.d)
    (hrel : S.rels.all (fun r => r.all (fun l => decide (l.1 < S.m)) &&
      Nat.beq (matW D.d (imgF Ims ImsI) (r.map letterOf)) (idF D.d)) = true)
    (hsl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ S.m)) = true)
    (hsA' : matW D.d (imgF Ims ImsI) (Ls.getD 0 []) = A)
    (hsB' : matW D.d (imgF Ims ImsI) (Ls.getD 1 []) = B) :
    seedLetterChecks D S = true := by
  exact CFSG.KC.SurjSeed.seed_checks hsA hsB hA hB hAI hBI hn hn32 horb hm hi hs hli hls hbase himg
    hinv hrel hsl hsA' hsB'

end CFSG.KC.SurjK

end
