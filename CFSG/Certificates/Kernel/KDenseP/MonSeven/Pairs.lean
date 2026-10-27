module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.InvData

public section

namespace CFSG.KC.KDenseP.MonSeven

open CFSG.Monster.AxisCount CFSG.YGroups.Y443 CFSG.YGroups.Y443Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenData
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks _root_.Timmesfeld.Mon7

abbrev Prs := List (List Native.Gen × List Native.Gen)

@[expose] def tri (eqs nes : Prs) : Prs := eqs ++ eqs ++ eqs ++ nes

@[expose] def decL (n : Nat) : Native.Gen :=
  if n % 4 = 0 then .rho ((n / 4) % 2 == 1, (n / 8) % 65536, (n / 524288) % 65536)
  else if n % 4 = 1 then .perm ((List.range 24).map fun k => (n / 4 / 32 ^ k) % 32).toArray
  else if n % 4 = 2 then .xi
  else .tau

@[expose] noncomputable def invC : Nat → List Nat
  | 0 => CFSG.KD.M7I.inv0
  | 1 => CFSG.KD.M7I.inv1
  | 2 => CFSG.KD.M7I.inv2
  | 3 => CFSG.KD.M7I.inv3
  | 4 => CFSG.KD.M7I.inv4
  | _ => CFSG.KD.M7I.inv5

@[expose] noncomputable def invW (k : Nat) : List Native.Gen := (invC k).map decL

@[expose] def WrhoBOf (iw : Nat → List Native.Gen) (v : Array Nat) : List Native.Gen :=
  (List.range 6).reverse.flatMap fun k =>
    if v[k]! ≤ 3 then powL v[k]! wq[k]! else powL (7 - v[k]!) (iw k)

@[expose] def pcOf (iw : Nat → List Native.Gen) : Prs :=
  (List.range 6).map (fun i => (powL 7 wq[i]!, ([] : List Native.Gen))) ++
    ((List.range 6).flatMap fun i => (List.range 6).filterMap fun j =>
      if i < j then some (wq[j]! ++ wq[i]!, wq[i]! ++ WrhoBOf iw cw7[i * 6 + j]!) else none) ++
    (List.range 6).map (fun i => (wq[i]! ++ iw i, ([] : List Native.Gen)))

@[expose] def autOf (iw : Nat → List Native.Gen) : Prs :=
  (List.range 2).flatMap fun a => (List.range 6).map fun i =>
    (wq[i]! ++ autW[a]!, autW[a]! ++ WrhoBOf iw (alphaVecs[a]!)[i]!)

@[expose] def orbOf (iw : Nat → List Native.Gen) (lo hi : Nat) : Prs :=
  (List.range' lo (hi - lo)).map fun k =>
    (WrhoBOf iw orbVec[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!)

@[expose] noncomputable def e13695pc : Prs := pcOf invW
@[expose] noncomputable def e13695aut : Prs := autOf invW
@[expose] def e13695rat : Prs := ratPairs
@[expose] noncomputable def e136300 : Prs := orbOf invW 0 11
@[expose] noncomputable def e136301 : Prs := orbOf invW 11 22

end CFSG.KC.KDenseP.MonSeven

end
