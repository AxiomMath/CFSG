module

public import CFSG.LieType.Steinberg.Adjoint.CertE8
public import CFSG.Blueprint.ChevalleyPinned
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

namespace AdjData

variable {τ : Tag} (D : AdjData τ)

@[expose] def walk : List ℕ → ℕ × ℤ → ℕ × ℤ
  | [], p => p
  | i :: w, (k, s) => walk w (D.img k (τ.idx i), s * D.weylSign k (τ.idx i))

@[expose] def checkPinned : Bool :=
  ((List.range τ.witnesses.roots.length).all fun a =>
    let α := decodeVec (τ := τ) (τ.witnesses.roots.getD a 0)
    ((List.finRange τ.rank).any fun j =>
        List.ofFn α == List.ofFn (Pi.single j 1 : Fin τ.rank → ℤ) ||
          List.ofFn α == List.ofFn (-Pi.single j 1 : Fin τ.rank → ℤ)) ||
      (let p := D.walk (decodeWord (τ.witnesses.words.getD a 0))
          ((τ.idx (τ.witnesses.seeds.getD a 0) : ℕ), 1)
       decide (p.1 < τ.rootCertificate.roots.length) &&
         (List.ofFn (τ.rootCertificate.root p.1) == List.ofFn α) && (p.2 == 1))) &&
  ((List.finRange τ.rank).all fun j => D.weylSign j j == -1) &&
  (τ.witnesses.roots.length == τ.rootCertificate.roots.length)

end AdjData

end CFSG.LieType.Steinberg.Adjoint
