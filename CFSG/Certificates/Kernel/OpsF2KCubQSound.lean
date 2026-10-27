
module

public import Certificates.Data.Kernel.OpsF2KCubQ
public import CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Misc.F2BfsRec2Sound
public import CFSG.Certificates.Kernel.OpsF2KFusQSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native
open CFSG.KC.Misc.G24 (mulF2)
open CFSG.KC.F2BfsRec (mulF2_eq_mulF mulF_lt)

theorem stepK_eq_cubStepK (d : Nat) : stepK d = CFSG.KC.LocalComp.Cub.stepK d := by
  funext R op
  cases op <;> rfl

theorem expOK_eq_cubExpOK : expOK = CFSG.KC.LocalComp.Cub.expOK := by
  funext op
  cases op <;> rfl

theorem runK_eq_cubFoldl (d A B n : Nat) (prog : List Op) :
    runK d A B n prog =
      prog.foldl (CFSG.KC.LocalComp.Cub.stepK d) (CFSG.KC.LocalComp.Cub.initK d A B n) := by
  unfold runK
  rw [stepK_eq_cubStepK]
  rfl

theorem getR_eq_cubGetR (d : Nat) (R : List Nat) (i : Nat) :
    getR d R i = CFSG.KC.LocalComp.Cub.getR d R i := rfl

theorem powK_eq_cubPowK (d X e : Nat) : powK d X e = CFSG.KC.LocalComp.Cub.powK d X e := rfl

theorem appK_eq_cubAppK (d X : Nat) : ∀ n v : Nat, appK d X n v = CFSG.KC.LocalComp.Cub.appK d X n v
  | 0, _ => rfl
  | n + 1, v => by
    change appK d X n (vmF d X v) = CFSG.KC.LocalComp.Cub.appK d X n (vmF d X v)
    exact appK_eq_cubAppK d X n (vmF d X v)

theorem appBaseK_eq_cubAppBaseK (d b : Nat) : ∀ (xs : List Nat) (n v : Nat),
    appBaseK d b xs n v = CFSG.KC.LocalComp.Cub.appBaseK d b xs n v
  | [], _, _ => rfl
  | X :: xs, n, v => by
    change appBaseK d b xs (n / b) (appK d X (n % b) v) =
      CFSG.KC.LocalComp.Cub.appBaseK d b xs (n / b) (CFSG.KC.LocalComp.Cub.appK d X (n % b) v)
    rw [appK_eq_cubAppK]
    exact appBaseK_eq_cubAppBaseK d b xs (n / b) _

theorem distinctK_eq_allDistinct : ∀ L : List Nat,
    distinctK L = CFSG.KC.LocalComp.Cub.allDistinct L
  | [] => rfl
  | x :: xs => by
    change (xs.all (fun y => !(Nat.beq x y)) && distinctK xs) =
      (xs.all (fun y => !(Nat.beq x y)) && CFSG.KC.LocalComp.Cub.allDistinct xs)
    rw [distinctK_eq_allDistinct xs]

theorem cubicQ_eq {d A B : Nat} {D : CubData} (hs : seedsOK d A B = true)
    (he : D.prog.all expOK = true) : cubicQ d A B D = CFSG.KC.LocalComp.Cub.cubicK d A B D := by
  obtain ⟨hR, hbd⟩ := runQ_eq (n := D.nregs) hs he
  rw [runK_eq_cubFoldl] at hR hbd
  cases hb : [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ].all (decide <| · < 65536)
  · simp only [cubicQ, CFSG.KC.LocalComp.Cub.cubicK, hb, Bool.and_false, Bool.false_and]
  have hb' : ∀ x ∈ [D.r, D.oh, D.a, D.b, D.c, D.d, D.k, D.l, D.μ], x < 2 ^ 16 := fun x hx => by
    have := of_decide_eq_true (List.all_eq_true.1 hb x hx)
    omega
  have hrm1 : D.r - 1 < 2 ^ 16 := by
    have := hb' D.r (by simp)
    omega
  simp only [cubicQ, CFSG.KC.LocalComp.Cub.cubicK, CFSG.KC.LocalComp.Cub.conjK, seedsOK, hR,
    commMQ, commQ, conjQ, mulF2_eq_mulF, expOK_eq_cubExpOK, getR_eq_cubGetR,
    appBaseK_eq_cubAppBaseK, distinctK_eq_allDistinct]
  generalize D.prog.foldl (CFSG.KC.LocalComp.Cub.stepK d)
    (CFSG.KC.LocalComp.Cub.initK d A B D.nregs) = Rl at hbd ⊢
  have hX : ∀ i, CFSG.KC.LocalComp.Cub.getR d Rl i < 2 ^ (d * d) := fun i => getR_lt hbd i
  have hZ : mulF d (mulF d (mulF d (CFSG.KC.LocalComp.Cub.getR d Rl D.rx)
      (CFSG.KC.LocalComp.Cub.getR d Rl D.ry))
      (CFSG.KC.LocalComp.Cub.powK d (CFSG.KC.LocalComp.Cub.getR d Rl D.rx) (D.r - 1)))
      (CFSG.KC.LocalComp.Cub.powK d (CFSG.KC.LocalComp.Cub.getR d Rl D.ry) (D.r - 1)) <
      2 ^ (d * d) := mulF_lt _ _ _
  simp only [pqK_eq_powK (hX D.rx) (hb' D.r (by simp)), pqK_eq_powK (hX D.ry) (hb' D.r (by simp)),
    pqK_eq_powK (hX D.rh) (hb' D.oh (by simp)), pqK_eq_powK (hX D.rx) hrm1,
    pqK_eq_powK (hX D.ry) hrm1, pqK_eq_powK (hX D.rx) (hb' D.a (by simp)),
    pqK_eq_powK (hX D.ry) (hb' D.b (by simp)), pqK_eq_powK (hX D.rx) (hb' D.c (by simp)),
    pqK_eq_powK (hX D.ry) (hb' D.d (by simp)), pqK_eq_powK hZ (hb' D.k (by simp)),
    pqK_eq_powK hZ (hb' D.l (by simp)), pqK_eq_powK hZ (hb' D.μ (by simp)), powK_eq_cubPowK]

theorem cubicK_of_Q {d A B : Nat} {D : CubData} (h : cubicQ d A B D = true) :
    CFSG.KC.LocalComp.Cub.cubicK d A B D = true := by
  have h' := h
  simp only [cubicQ, Bool.and_eq_true, and_assoc] at h'
  rwa [← cubicQ_eq h'.1 h'.2.2.1]

theorem cubicCheck_of_Q {d A B : Nat} {csA csB : List Char} {D : CubData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : cubicQ d A B D = true) : (ops2 d).cubicCheck D = true :=
  CFSG.KC.LocalComp.Cub.cubicCheck_of_K hA hB hsA hsB (cubicK_of_Q h)

end CFSG.KC.OpsF2K

end
