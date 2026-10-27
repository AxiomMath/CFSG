module

public import Certificates.Data.Kernel.OpsF2KSq
public import Certificates.Data.CFSGNative.SectionRank.F2
import all CFSG.Certificates.Kernel.OpsF2KSound
import all CFSG.Certificates.Kernel.LocalCompCubSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.KLie.CT
open CFSG.KC.Co1F2 (unpackR)

private theorem distinctK_eq : ∀ L : List Nat, distinctK L = CFSG.KC.LocalComp.Cub.allDistinct L
  | [] => rfl
  | x :: xs => by
    change (xs.all (fun y => !(Nat.beq x y)) && distinctK xs) =
      (xs.all (fun y => !(Nat.beq x y)) && CFSG.KC.LocalComp.Cub.allDistinct xs)
    rw [distinctK_eq xs]

private theorem normalFormOK2_of_K {d r t X Y : Nat} (ht : t < d)
    (h : distinctK ((List.range (r ^ 2)).map fun n => appBaseK d r [X, Y] n (pw2 t)) = true) :
    (ops2 d).normalFormOK r [unpackR d X, unpackR d Y] t = true := by
  rw [distinctK_eq] at h
  have hu : pw2 t < 2 ^ d := pw2_lt ht
  let vs : Array Nat := Array.ofFn (n := r ^ 2) fun n =>
    (ops2 d).appBase r [unpackR d X, unpackR d Y] n.val ((ops2 d).unit t)
  unfold Ops.normalFormOK
  change (ops2 d).distinctOK vs = true
  unfold Ops.distinctOK
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  have hvs : vs.size = r ^ 2 := by simp [vs]
  have hiN : i < r ^ 2 := by
    have := List.mem_range.1 hi
    rw [hvs] at this
    exact this
  have hjI : j < i := by simpa using hj
  have hjN : j < r ^ 2 := by omega
  have hpair := CFSG.KC.LocalComp.Cub.allDistinct_map_range h i hiN j hjN (by omega)
  have hvi : vs[i]! = appBaseK d r [X, Y] i (pw2 t) := by
    dsimp only [vs]
    rw [getElem!_pos _ i (by simpa using hiN), Array.getElem_ofFn]
    exact appBase_unpackR d r [X, Y] i (pw2 t)
  have hvj : vs[j]! = appBaseK d r [X, Y] j (pw2 t) := by
    dsimp only [vs]
    rw [getElem!_pos _ j (by simpa using hjN), Array.getElem_ofFn]
    exact appBase_unpackR d r [X, Y] j (pw2 t)
  rw [hvi, hvj]
  refine vne_of_beq (appBaseK_lt d r [X, Y] i _ hu) (appBaseK_lt d r [X, Y] j _ hu) ?_
  rw [CFSG.KC.LocalComp.Cub.nat_beq_false.mpr hpair]
  rfl

private theorem lt16 {e : Nat} (h : e < 65536) : e < 2 ^ 16 := h.trans_eq (by norm_num)

theorem squareCheck_of_K {d A B : Nat} {csA csB : List Char} {D : SqData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : sqK d A B D = true) : (ops2 d).squareCheck D = true := by
  simp only [sqK, seedsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, ht, hr16, hoh16, ha16, hb16, hc16, hd16, hn, hprog, hrx, hry, hrh, hr0,
    hoh0, hX, hY, hH, hXY, hcX, hcY, hdist⟩ := h
  have hreg : ∀ r < D.nregs, ((ops2 d).run D.prog ((ops2 d).initRegs ((ops2 d).decode D.seedA)
      ((ops2 d).decode D.seedB) D.nregs))[r]! =
        unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  unfold Ops.squareCheck Ops.regsOf
  dsimp only
  rw [hreg _ hrx, hreg _ hry, hreg _ hrh]
  generalize getR d (runK d A B D.nregs D.prog) D.rx = X at *
  generalize getR d (runK d A B D.nregs D.prog) D.ry = Y at *
  generalize getR d (runK d A B D.nregs D.prog) D.rh = H at *
  have e1 : (ops2 d).eq ((ops2 d).pow (unpackR d X) D.r) (ops2 d).one = true := by
    rw [← unpackR_powK (lt16 hr16), ← unpackR_idF_eq_one]
    exact eq_of_beq hX
  have e2 : (ops2 d).eq ((ops2 d).pow (unpackR d Y) D.r) (ops2 d).one = true := by
    rw [← unpackR_powK (lt16 hr16), ← unpackR_idF_eq_one]
    exact eq_of_beq hY
  have e3 : (ops2 d).eq ((ops2 d).pow (unpackR d H) D.oh) (ops2 d).one = true := by
    rw [← unpackR_powK (lt16 hoh16), ← unpackR_idF_eq_one]
    exact eq_of_beq hH
  have e4 : (ops2 d).eq ((ops2 d).mul (unpackR d X) (unpackR d Y))
      ((ops2 d).mul (unpackR d Y) (unpackR d X)) = true := commOK_of_commK hXY
  have e5 : (ops2 d).conjOK (unpackR d H) (unpackR d X)
      ((ops2 d).mul ((ops2 d).pow (unpackR d X) D.a) ((ops2 d).pow (unpackR d Y) D.c)) =
        true := by
    rw [← unpackR_powK (lt16 ha16), ← unpackR_powK (lt16 hc16), ← unpackR_mulF]
    exact conjOK_of_conjK hcX
  have e6 : (ops2 d).conjOK (unpackR d H) (unpackR d Y)
      ((ops2 d).mul ((ops2 d).pow (unpackR d X) D.b) ((ops2 d).pow (unpackR d Y) D.d)) =
        true := by
    rw [← unpackR_powK (lt16 hb16), ← unpackR_powK (lt16 hd16), ← unpackR_mulF]
    exact conjOK_of_conjK hcY
  have e7 := normalFormOK2_of_K ht hdist
  simp only [hn, hprog, hrx, hry, hrh, hr0, hoh0, decide_true, e1, e2, e3, e4, e5, e6, e7,
    Bool.and_true]

end CFSG.KC.OpsF2K

end
