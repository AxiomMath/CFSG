module

public import Certificates.Data.Kernel.SporSch.J4S11
public import CFSG.Sporadic.Schreier.J4SElevenData
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Certificates.Kernel.Spor.PCountSound
public import CFSG.Certificates.Kernel.SporSch.J4SBigSound

public section

namespace CFSG.KS.SporSch.J4E.DistPf

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ
open CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

variable {c rm one pad t0 t1 t2 t3 t4 t5 t6 : Nat}

private theorem getElem!_eq_getD'' (C : Array Nat) (j : Nat) : C[j]! = C[j]?.getD 0 := by
  rw [getElem!_def]
  cases C[j]? <;> rfl

private theorem vmul_lt {X : Array Nat} (hX : WfN X) (v : Nat) : vecMulN 112 X v < 2 ^ 112 :=
  vecMulN_lt (fun j hj => by rw [← getElem!_eq_getD'']; exact hX.2 j hj) v

private theorem app_lt {X : Array Nat} (hX : WfN X) :
    ∀ (n v : Nat), v < 2 ^ 112 → O.app X n v < 2 ^ 112
  | 0, v, hv => hv
  | n + 1, v, _ => app_lt hX n _ (vmul_lt hX v)

private theorem appBase_lt (b : Nat) : ∀ (xs : List (Array Nat)), (∀ x ∈ xs, WfN x) →
    ∀ (n v : Nat), v < 2 ^ 112 → O.appBase b xs n v < 2 ^ 112
  | [], _, n, v, hv => hv
  | X :: xs, hxs, n, v, hv =>
    appBase_lt b xs (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) _ _
      (app_lt (hxs X List.mem_cons_self) _ _ hv)

private theorem app_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) {X : Array Nat}
    (hX : WfN X) : ∀ (n v : Nat), O.app X n v = vecPowK rm (encN X) n v
  | 0, v => rfl
  | n + 1, v => by
    have h : vecPowK rm (encN X) (n + 1) v = vecPowK rm (encN X) n (vecJ rm v (encN X)) := rfl
    rw [h, ← vec_enc hK hX v]
    exact app_enc hK hX n _

private theorem appBase_enc (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6) (b : Nat) :
    ∀ (xs : List (Array Nat)), (∀ x ∈ xs, WfN x) → ∀ (n v : Nat),
    O.appBase b xs n v = appK rm b (xs.map encN) n v
  | [], _, n, v => rfl
  | X :: xs, hxs, n, v => by
    have h : appK rm b (encN X :: xs.map encN) n v =
        appK rm b (xs.map encN) (n / b) (vecPowK rm (encN X) (n % b) v) := rfl
    rw [List.map_cons, h, ← app_enc hK (hxs X List.mem_cons_self) (n % b) v]
    exact appBase_enc hK b xs (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) (n / b) _

private theorem vne_iff {u w : Nat} (hu : u < 2 ^ 112) (hw : w < 2 ^ 112) :
    O.vne u w = true ↔ u ≠ w := by
  change ((List.range 112).any fun j => u.testBit j != w.testBit j) = true ↔ u ≠ w
  constructor
  · intro h huw
    subst huw
    simp at h
  · intro h
    by_contra hf
    apply h
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < 112
    · have : ¬ ((List.range 112).any fun j => u.testBit j != w.testBit j) = true := hf
      simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq, not_exists, not_and,
        not_not] at this
      exact this j hj
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))]

private theorem vecsK_eq (rm b : Nat) (xs : List Nat) :
    ∀ N, vecsK rm b xs N = ((List.range N).reverse).map fun n => appK rm b xs n 1
  | 0 => rfl
  | N + 1 => by
    have h : vecsK rm b xs (N + 1) = appK rm b xs N 1 :: vecsK rm b xs N := rfl
    rw [h, vecsK_eq rm b xs N, List.range_succ, List.reverse_append]
    rfl

theorem distinctOK_of_distK (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
    {b N M : Nat} {xs : List (Array Nat)} (hxs : ∀ x ∈ xs, WfN x) (hMN : M ≤ N)
    (h : distK rm b (xs.map encN) N = true) :
    O.distinctOK (Array.ofFn (n := M) fun n => O.appBase b xs n.val (O.unit 0)) = true := by
  have hnd : ((List.range N).map fun n => appK rm b (xs.map encN) n 1).Nodup := by
    have := CFSG.KS.PCnt.nodup_of_distB (L := vecsK rm b (xs.map encN) N) h
    rw [vecsK_eq, List.map_reverse] at this
    exact List.nodup_reverse.1 this
  have hinj : ∀ i < N, ∀ j < N, appK rm b (xs.map encN) i 1 = appK rm b (xs.map encN) j 1 →
      i = j := fun i hi j hj e =>
    List.inj_on_of_nodup_map hnd (List.mem_range.2 hi) (List.mem_range.2 hj) e
  have hu : O.unit 0 < 2 ^ 112 := by
    change 1 <<< 0 < 2 ^ 112
    decide
  have hval : ∀ n, O.appBase b xs n (O.unit 0) = appK rm b (xs.map encN) n 1 := fun n =>
    appBase_enc hK b xs hxs n _
  unfold Ops.distinctOK
  simp only [Array.size_ofFn, List.all_eq_true, List.mem_range]
  intro i hi j hj
  have hi' : (Array.ofFn (n := M) fun n => O.appBase b xs n.val (O.unit 0))[i]! =
      O.appBase b xs i (O.unit 0) := by
    simp [hi]
  have hj' : (Array.ofFn (n := M) fun n => O.appBase b xs n.val (O.unit 0))[j]! =
      O.appBase b xs j (O.unit 0) := by
    simp [show j < M by omega]
  rw [hi', hj']
  rw [vne_iff (appBase_lt b xs hxs _ _ hu) (appBase_lt b xs hxs _ _ hu), hval, hval]
  intro e
  have := hinj i (by omega) j (by omega) e
  omega

variable (hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6)
include hK

theorem distK_sound' {X Y Z : Array Nat} (hX : WfN X) (hY : WfN Y) (hZ : WfN Z)
    (h : distK rm 11 [encN X, encN Y, encN Z] 1331 = true) :
    O.normalFormOK 11 [X, Y, Z] 0 = true := by
  unfold Ops.normalFormOK
  exact distinctOK_of_distK hK (xs := [X, Y, Z]) (M := 11 ^ [X, Y, Z].length) (N := 1331)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> assumption)
    (by simp) h

theorem sixteenK_sound' {U W : Array Nat} (hU : WfN U) (hW : WfN W)
    (h : distK rm 8 [encN U, encN W] 16 = true) : sixteenOK U W = true := by
  unfold sixteenOK
  exact distinctOK_of_distK hK (xs := [U, W]) (M := 16) (N := 16)
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl <;> assumption)
    le_rfl h

end CFSG.KS.SporSch.J4E.DistPf

end
