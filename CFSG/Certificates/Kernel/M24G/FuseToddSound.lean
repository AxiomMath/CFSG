module

public import Certificates.Data.Kernel.M24G.FuseTodd
public import CFSG.Certificates.Kernel.M24G.ToddSound
public import CFSG.Certificates.Kernel.M24G.KzeroSound
public import CFSG.Certificates.Kernel.M24G.DualSound

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem toddAct_eq_actT (t : Array Nat) (ht : ∀ x ∈ t.toList, x < 24) :
    (fun m => Native.toddAct t m) = actT t :=
  duad_toddAct_eq t ht

theorem actT_lt (t : Array Nat) (m : Nat) : actT t m < 2048 := by
  have hcc : ∀ c ∈ Native.ccEColsN, c < 2 ^ 11 := by decide
  unfold actT toddActF
  exact actM_lt _ hcc _

theorem fuseWord_fun : Native.fuseWord = fuseWordF := by
  funext ls w
  unfold Native.fuseWord fuseWordF
  simp only [kzeroMul_eq]

theorem fuseCommGens_eq : Native.fuseCommGens () = fuseCommGensK (Native.kzeroK0List ()) := rfl

theorem orMask_append (b : List Nat) : ∀ a : List Nat, orMask (a ++ b) = orMask a ||| orMask b
  | [] => by simp [orMask]
  | c :: a => by rw [List.cons_append, orMask, orMask, orMask_append b a, Nat.or_assoc]

theorem xorStepM_eq (L : List Nat) (g : Nat) :
    xorStepM (L, orMask L) g =
      ((if L.contains g then L else L ++ L.map (· ^^^ g)),
        orMask (if L.contains g then L else L ++ L.map (· ^^^ g))) := by
  unfold xorStepM
  by_cases hc : L.contains g
  · simp only [testBit_orMask, hc, if_true]
  · simp only [testBit_orMask, hc, Bool.false_eq_true, if_false, orMask_append]

theorem foldl_xorStepM : ∀ (gs L : List Nat), gs.foldl xorStepM (L, orMask L) =
    (gs.foldl (fun L g => if L.contains g then L else L ++ L.map (· ^^^ g)) L,
      orMask (gs.foldl (fun L g => if L.contains g then L else L ++ L.map (· ^^^ g)) L))
  | [], _ => rfl
  | g :: gs, L => by rw [List.foldl_cons, xorStepM_eq, foldl_xorStepM gs, List.foldl_cons]

theorem xorCloseM_eq (gs : List Nat) :
    xorCloseM gs = (Native.fuseXorClose gs, orMask (Native.fuseXorClose gs)) :=
  foldl_xorStepM gs [0]

theorem fuseCommLoop_eq (os gs : List Nat) :
    Native.fuseCommLoop os (Native.fuseXorClose gs) = fuseCommLoopF (badMask os) (xorCloseM gs).2 := by
  unfold Native.fuseCommLoop fuseCommLoopF
  rw [xorCloseM_eq]
  exact all_congr_mem fun m hm => by rw [testBit_badMask os (List.mem_range.1 hm), testBit_orMask]

theorem fuseX0Loop_eq (T : Array Nat) (os : List Nat) (K : List (Array Nat))
    (hT : ∀ x ∈ T.toList, x < 24) : Native.fuseX0Loop T os K = fuseX0LoopF T (badMask os) K := by
  unfold Native.fuseX0Loop fuseX0LoopF
  have e : ((List.range 2048).all fun m => Native.toddOctsKer os (Native.toddAct T m ^^^ m)) =
      (List.range 2048).all fun m => !(badMask os).testBit (actT T m ^^^ m) :=
    all_congr_mem fun m hm => by
      rw [testBit_badMask os (Nat.xor_lt_two_pow (n := 11) (actT_lt T m) (List.mem_range.1 hm)),
        Bool.not_not, ← toddAct_eq_actT T hT]
  simp only [kzeroMul_eq, e]

theorem fusePiBLoop_eq (os : List Nat) : Native.fusePiBLoop os = fusePiBLoopF (badMask os) := by
  unfold Native.fusePiBLoop fusePiBLoopF
  apply all_congr_mem
  intro m hm
  rw [testBit_badMask os (List.mem_range.1 hm), Bool.not_not,
    ← toddAct_eq_actT Native.fusePiBTab (by decide)]

theorem fusePiALoop_eq (os : List Nat) (Ts : List (Array Nat))
    (hT : ∀ T ∈ Ts, ∀ x ∈ T.toList, x < 24) :
    Native.fusePiALoop os Ts = fusePiALoopF (badMask os) Ts := by
  unfold Native.fusePiALoop fusePiALoopF
  have hA := toddAct_eq_actT Native.fusePiATab (by decide)
  have e : ((List.range 2048).all fun m => Native.toddAct Native.fusePiATab m != m ||
        Ts.any fun T => Native.toddOctsKer os (Native.toddAct T m)) =
      (List.range 2048).all fun m => actT Native.fusePiATab m != m ||
        Ts.any fun T => !(badMask os).testBit (actT T m) :=
    all_congr_mem fun m _ => by
      have e2 : (Ts.any fun T => Native.toddOctsKer os (Native.toddAct T m)) =
          Ts.any fun T => !(badMask os).testBit (actT T m) :=
        any_congr_mem fun T hT' => by
          rw [testBit_badMask os (actT_lt T m), Bool.not_not, ← toddAct_eq_actT T (hT T hT')]
      rw [e2, ← hA]
  simp only [kzeroMul_eq, e]

end CFSG.KC.M24G
