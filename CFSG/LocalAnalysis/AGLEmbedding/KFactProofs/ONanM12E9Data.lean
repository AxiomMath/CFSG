module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12CoverData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanHeisList
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanM12HeisData

public section

namespace CFSG.AGLEmbedding.KFactProofs.M12Cover

open CFSG.AGLEmbedding.KFactProofs.M12Z2 CFSG.CGT.PushingUpLit.CGT6M CFSG.Sporadic.Bridge

@[expose] def m12E9II : List (Equiv.Perm (Fin 12)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun k => m12HeisA ^ i * m12HeisC ^ k

@[expose] def m12E9I : List (Equiv.Perm (Fin 12)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun k =>
    (m12HeisA * m12HeisB) ^ i * m12HeisC ^ k

@[expose] def m12E9III : List (Equiv.Perm (Fin 12)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun k => m12HeisB ^ i * m12HeisC ^ k

@[expose] def m12E9IIIp : List (Equiv.Perm (Fin 12)) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun k =>
    (m12HeisA * m12HeisB ^ 2) ^ i * m12HeisC ^ k

@[expose] def m12E9SetEq (L S : List (Equiv.Perm (Fin 12))) : Bool :=
  L.all (fun z => decide (z ∈ S)) && S.all (fun z => decide (z ∈ L))

@[expose] def m12E9Cent (x : Equiv.Perm (Fin 12)) : List (Equiv.Perm (Fin 12)) :=
  (heisList m12HeisA m12HeisB m12HeisC).filter fun z => decide (z * x = x * z)

@[expose] def m12E9ClassOK : Bool :=
  (heisList m12HeisA m12HeisB m12HeisC).all fun x =>
    decide (x ∈ [1, m12HeisC, m12HeisC * m12HeisC]) ||
      (decide (m12E9Cent x).Nodup && decide ((m12E9Cent x).length = 9) &&
        (m12E9SetEq (m12E9Cent x) m12E9II || m12E9SetEq (m12E9Cent x) m12E9I ||
          m12E9SetEq (m12E9Cent x) m12E9III || m12E9SetEq (m12E9Cent x) m12E9IIIp))

@[expose] def m12E9AutOK (S : List (Equiv.Perm (Fin 12))) (n : Equiv.Perm (Fin 12)) : Bool :=
  S.all (fun s => decide (n * s * n⁻¹ ∈ S) && decide (n⁻¹ * s * n ∈ S)) &&
    S.any (fun s => decide (n ^ 6 * s * (n ^ 6)⁻¹ ≠ s))

@[expose] def m12E9NII : Equiv.Perm (Fin 12) := cycPerm [[0,5,4,10,1,9,2,11],[3,8]]

@[expose] def m12E9NI : Equiv.Perm (Fin 12) := cycPerm [[0,1,8,6],[2,3,5,4,10,7,9,11]]

@[expose] def m12E9N0 : Equiv.Perm (Fin 12) := cycPerm [[0,6],[2,10],[4,5],[9,11]]

@[expose] def m12E9WordII : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def m12E9WordI : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
   (0, true), (1, false), (0, true), (1, true), (0, true), (1, true)]

@[expose] def m12E9Word0 : List (ℕ × Bool) :=
  [(1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)]

@[expose] def m12E9Facts : Bool :=
  m12E9ClassOK && m12E9AutOK m12E9II m12E9NII && m12E9AutOK m12E9I m12E9NI &&
    decide (m12E9N0⁻¹ * m12CoverU * m12E9N0 ∈ m12E9IIIp) &&
    decide (m12E9N0⁻¹ * m12CoverV * m12E9N0 ∈ m12E9IIIp) &&
    decide (m12CoverU ∈ m12E9III) && decide (m12CoverV ∈ m12E9III) &&
    decide (wordProd m12Gen m12E9WordII = m12E9NII) &&
    decide (wordProd m12Gen m12E9WordI = m12E9NI) &&
    decide (wordProd m12Gen m12E9Word0 = m12E9N0)

end CFSG.AGLEmbedding.KFactProofs.M12Cover
