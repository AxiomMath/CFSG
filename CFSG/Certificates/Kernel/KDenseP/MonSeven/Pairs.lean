module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterSevenChecks
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.InvData
public import CFSG.Certificates.Kernel.KDenseP.MonSeven.PowData

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

@[expose] def pieceW (iw : Nat → List Native.Gen) (k e : Nat) : List Native.Gen :=
  if e ≤ 3 then powL e wq[k]! else powL (7 - e) (iw k)

@[expose] noncomputable def pieceR (iw : Nat → List Native.Gen) : Nat → Nat → List Native.Gen
  | 1, 2 => CFSG.KD.M7Q.P1_2.map decL
  | 1, 5 => CFSG.KD.M7Q.P1_5.map decL
  | 3, 4 => CFSG.KD.M7Q.P3_4.map decL
  | 4, 2 => CFSG.KD.M7Q.P4_2.map decL
  | 4, 4 => CFSG.KD.M7Q.P4_4.map decL
  | k, e => pieceW iw k e

@[expose] noncomputable def powPrs (iw : Nat → List Native.Gen) : Prs :=
  [(1, 2), (1, 5), (3, 4), (4, 2), (4, 4)].map fun p => (pieceR iw p.1 p.2, pieceW iw p.1 p.2)

@[expose] def WrhoBOf (pw : Nat → Nat → List Native.Gen) (v : Array Nat) : List Native.Gen :=
  (List.range 6).reverse.flatMap fun k => pw k v[k]!

@[expose] def pcOf (iw : Nat → List Native.Gen) : Prs :=
  [0, 1, 5].map (fun i => (powL 7 wq[i]!, ([] : List Native.Gen))) ++
    ((List.range 6).flatMap fun i => (List.range 6).filterMap fun j =>
      if i < j ∧ (j < 5 ∨ i = 2 ∨ i = 3) then
        some (wq[j]! ++ wq[i]!, wq[i]! ++ WrhoBOf (pieceW iw) cw7[i * 6 + j]!) else none) ++
    (List.range 6).map (fun i => (wq[i]! ++ iw i, ([] : List Native.Gen)))

@[expose] def autGOf (pw : Nat → Nat → List Native.Gen) : Prs :=
  (List.range 2).flatMap fun a => (List.range 2).map fun i =>
    (wq[i]! ++ autW[a]!, autW[a]! ++ WrhoBOf pw (alphaVecs[a]!)[i]!)

@[expose] def orbOf (pw : Nat → Nat → List Native.Gen) (lo hi : Nat) : Prs :=
  (List.range' lo (hi - lo)).map fun k =>
    (WrhoBOf pw orbVec[k]! ++ orbT[k]!, orbT[k]! ++ targetW orbKind[k]!)

@[expose] def orbSplitPr (pw : Nat → Nat → List Native.Gen) (k s : Nat) :
    List Native.Gen × List Native.Gen :=
  ((List.range s).reverse.flatMap (fun j => pw j (orbVec[k]!)[j]!) ++ orbT[k]!,
    (List.range' s (6 - s)).flatMap (fun j => pw j (7 - (orbVec[k]!)[j]!)) ++ orbT[k]! ++
      targetW orbKind[k]!)

@[expose] noncomputable def e13695pc : Prs := pcOf invW
@[expose] noncomputable def e13695autG : Prs := autGOf (pieceR invW)
@[expose] def e13695rat : Prs := ratPairs
@[expose] noncomputable def e136300 : Prs :=
  (List.range 11).map fun k => orbSplitPr (pieceR invW) k #[6, 6, 6, 4, 4, 4, 6, 4, 4, 6, 4][k]!
@[expose] noncomputable def e136301 : Prs :=
  (([11, 12, 13, 14, 15, 16, 17].map fun k => orbSplitPr (pieceR invW) k 4) ++
    [18, 19, 20, 21].map fun k => orbSplitPr (pieceR invW) k 1) ++ powPrs invW

end CFSG.KC.KDenseP.MonSeven

end
