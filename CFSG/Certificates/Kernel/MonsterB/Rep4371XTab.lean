module

public import Certificates.Data.Kernel.MonsterB.Rep4371X
public import CFSG.Monster.B.Rep4371.Model

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.Monster.B

@[expose] noncomputable def oddP (a : Nat) : Bool := Nat.beq (bitN (wordT a) 0) (bitN (wordT a) 1)

@[expose] noncomputable def octP (a : Nat) : Bool :=
  Nat.beq (popc24 (wordT a)) 8 && Nat.beq (Nat.land (wordT a) 3) 3

theorem odd_filter :
    ((List.range 2048).map (2 * ·)).filter oddP = (List.range 1024).map oddT := by decide +kernel

theorem oct_perm : ((List.range 4096).filter octP).Perm ((List.range 77).map octT) := by
  decide +kernel

theorem oct_sorted : ((List.range 77).map octT).Pairwise (fun a b => wordT a < wordT b) := by
  decide +kernel

theorem mentry_tab : ∀ i < 16, ∀ j < 16, Model.Mentry i j = sgI (mbit i j) 1 := by decide +kernel

theorem localPairs_tab :
    ∀ r < 16, (Model.localPairs[r]!).1 = lp1 r ∧ (Model.localPairs[r]!).2 = lp2 r := by
  decide +kernel

theorem gT_tab : ∀ x < 64, gT x 0 = Model.xiGammaN x false ∧ gT x 1 = Model.xiGammaN x true := by
  decide +kernel

theorem par6_tab : ∀ x < 64, par6 x = (Model.parN 6 x).toNat := by decide +kernel

theorem qgT_tab : ∀ x < 64, qgT x = (Model.qGN x).toNat := by decide +kernel

end CFSG.KC.Rep4371X

end
