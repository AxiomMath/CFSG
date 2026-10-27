module

public import Certificates.Data.Kernel.J4NP.Elab7851
public import CFSG.Sporadic.J4.QTRankNative

public section

namespace CFSG.KC.J4NP

open CFSG.Sporadic.J4.QT CFSG.KC.J4Loc

@[expose] noncomputable def ivt (KK i : Nat) : List Nat := (List.range 11).map fun j => fld 11 (lnS 121 KK i) j

@[expose] noncomputable def entL (ENT : List (List (List (List Nat)))) (i : Nat) : List Nat :=
  rowL (blkL (blk4 ENT (i / 32)) (i % 32)) 0

structure Facts7851 (KK CMK PRK FMK MK : Nat) (ENT : List (List (List (List Nat)))) : Prop where
  len : ∀ i < 191, lenOK (ivt KK i) = true
  inj : ∀ i < 191, ∀ j < 191, ivt KK i = ivt KK j → i = j
  inv : ∀ t ∈ tabL, t ≠ idT → compT t t = idT → ∃ i < 191, ivt KK i = t
  comm : ∀ a < 191, ∀ x < 191, a ≠ x → compT (ivt KK a) (ivt KK x) = compT (ivt KK x) (ivt KK a) →
    (lnS 191 CMK a).testBit x = true
  prod : ∀ a < 191, ∀ x < 191, a ≠ x → (lnS 191 CMK a).testBit x = true →
    fld 8 (lnS 1528 PRK a) x < 191 ∧
      ivt KK (fld 8 (lnS 1528 PRK a) x) = compT (ivt KK a) (ivt KK x)
  fix : ∀ a < 191, ∀ c < 2048, (lnS 2048 FMK a).testBit c = true ↔ actT (ivt KK a) c = c
  fix128 : ∀ a < 191, ∃ F : List Nat, F.length ≤ 128 ∧ ∀ c < 2048, actT (ivt KK a) c = c → c ∈ F
  root : lnS 191 MK 0 = 0
  ent : ∀ i < 7507, (∀ p, (lnS 191 MK i).testBit p = true ↔ p ∈ entL ENT i) ∧ (entL ENT i).Nodup
  child : ∀ i < 7507, ∀ x < 191, (∀ a ∈ entL ENT i, a < x ∧ (lnS 191 CMK a).testBit x = true) →
    ∃ j < 7507, ∀ p, (lnS 191 MK j).testBit p = true ↔
      (p ∈ entL ENT i ∨ p = x ∨ ∃ a ∈ entL ENT i, fld 8 (lnS 1528 PRK x) a = p)
  bound : ∀ i < 7507, entL ENT i ≠ [] → (entL ENT i).length ≤ 7 ∨
    ∃ G F : List Nat, (∀ g ∈ G, g ∈ entL ENT i ∧ g < 191) ∧
      (∀ c < 2048, (∀ g ∈ G, (lnS 2048 FMK g).testBit c = true) → c ∈ F) ∧
      F.length * ((entL ENT i).length + 1) ≤ 1024

end CFSG.KC.J4NP

end
