
module

public import Certificates.Data.Kernel.OpsF2KQ
public import CFSG.Certificates.Kernel.OpsF2KFusQSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.F2BfsRec (mulF2_eq_mulF)

theorem commQ_eq : commQ = commK := by
  funext d X Y
  simp only [commQ, commK, mulF2_eq_mulF]

theorem conjQ_eq : conjQ = conjK := by
  funext d X Y W
  simp only [conjQ, conjK, mulF2_eq_mulF]

theorem commsModQ_eq (d T : Nat) : ∀ xs : List Nat, commsModQ d T xs = commsModK d T xs
  | [] => rfl
  | X :: xs => by simp only [commsModQ, commsModK, mulF2_eq_mulF, commsModQ_eq d T xs]

theorem commsQ_eq (d : Nat) : ∀ xs : List Nat, commsQ d xs = commsK d xs
  | [] => rfl
  | X :: xs => by simp only [commsQ, commsK, commQ_eq, commsQ_eq d xs]

theorem pqK_getR {d : Nat} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d)) {e : Nat}
    (he : e < 2 ^ 16) (i : Nat) : pqK d (getR d R i) e = powK d (getR d R i) e :=
  pqK_eq_powK (getR_lt hR i) he

theorem secQ_eq (d A B : Nat) (D : SecData) : secQ d A B D = secK d A B D := by
  cases hs : seedsOK d A B
  · simp only [secQ, secK, hs, Bool.false_and]
  cases he : D.prog.all expOK
  · simp only [secQ, secK, hs, he, Bool.true_and, Bool.false_and]
  simp only [secQ, secK, (runQ_eq (n := D.nregs) hs he).1, commsModQ_eq, mulF2_eq_mulF]

theorem secK_of_Q {d A B : Nat} {D : SecData} (h : secQ d A B D = true) : secK d A B D = true := by
  rwa [← secQ_eq]

theorem w4Q_eq (d A B : Nat) (D : Data) (inv : Nat) : w4Q d A B D inv = w4K d A B D inv := by
  cases hs : seedsOK d A B
  · simp only [w4Q, w4K, hs, Bool.false_and]
  cases he : D.prog.all expOK
  · simp only [w4Q, w4K, hs, he, Bool.true_and, Bool.false_and]
  simp only [w4Q, w4K, (runQ_eq (n := D.nregs) hs he).1, commsQ_eq, commQ_eq, mulF2_eq_mulF]

theorem w4K_of_Q {d A B : Nat} {D : Data} {inv : Nat} (h : w4Q d A B D inv = true) :
    w4K d A B D inv = true := by
  rwa [← w4Q_eq]

theorem normQ_eq {d n : Nat} {N : Cub2NormData} {R : List Nat} (hR : ∀ x ∈ R, x < 2 ^ (d * d))
    {X Y Z : Nat} (hX : X < 2 ^ (d * d)) (hY : Y < 2 ^ (d * d)) (hZ : Z < 2 ^ (d * d)) :
    normQ d N n R X Y Z = normK d N n R X Y Z := by
  cases hb : [N.oh, N.a, N.b, N.c, N.d, N.k, N.l].all (decide <| · < 65536)
  · simp only [normQ, normK, hb, Bool.and_false, Bool.false_and]
  have hb' : ∀ x ∈ [N.oh, N.a, N.b, N.c, N.d, N.k, N.l], x < 2 ^ 16 := fun x hx => by
    have := of_decide_eq_true (List.all_eq_true.1 hb x hx)
    omega
  simp only [normQ, normK, conjQ_eq, mulF2_eq_mulF, pqK_getR hR (hb' N.oh (by simp)),
    pqK_eq_powK hX (hb' N.a (by simp)), pqK_eq_powK hY (hb' N.b (by simp)),
    pqK_eq_powK hZ (hb' N.k (by simp)), pqK_eq_powK hX (hb' N.c (by simp)),
    pqK_eq_powK hY (hb' N.d (by simp)), pqK_eq_powK hZ (hb' N.l (by simp))]

theorem cub2Q_eq (d A B : Nat) (D : Cub2Data) : cub2Q d A B D = cub2K d A B D := by
  cases hs : seedsOK d A B
  · simp only [cub2Q, cub2K, hs, Bool.false_and]
  cases he : D.prog.all expOK
  · simp only [cub2Q, cub2K, hs, he, Bool.true_and, Bool.false_and]
  obtain ⟨hR, hbd⟩ := runQ_eq (n := D.nregs) hs he
  cases hr : decide (D.r < 65536)
  · simp only [cub2Q, cub2K, hr, Bool.and_false, Bool.false_and]
  have hr' : D.r < 2 ^ 16 := by
    have := of_decide_eq_true hr
    omega
  have hr1 : D.r - 1 < 2 ^ 16 := by omega
  have hX := getR_lt hbd D.rx
  have hY := getR_lt hbd D.ry
  have hcomm : commMQ d D.r (getR d (runK d A B D.nregs D.prog) D.rx)
      (getR d (runK d A B D.nregs D.prog) D.ry) =
      commMK d D.r (getR d (runK d A B D.nregs D.prog) D.rx)
        (getR d (runK d A B D.nregs D.prog) D.ry) := by
    simp only [commMQ, commMK, mulF2_eq_mulF, pqK_eq_powK hX hr1, pqK_eq_powK hY hr1]
  have hZ : commMK d D.r (getR d (runK d A B D.nregs D.prog) D.rx)
      (getR d (runK d A B D.nregs D.prog) D.ry) < 2 ^ (d * d) := by
    unfold commMK
    exact CFSG.KC.F2BfsRec.mulF_lt _ _ _
  simp only [cub2Q, cub2K, hR, hcomm, commQ_eq, pqK_eq_powK hX hr', pqK_eq_powK hY hr',
    normQ_eq hbd hX hY hZ]

theorem cub2K_of_Q {d A B : Nat} {D : Cub2Data} (h : cub2Q d A B D = true) :
    cub2K d A B D = true := by
  rwa [← cub2Q_eq]

end CFSG.KC.OpsF2K

end
