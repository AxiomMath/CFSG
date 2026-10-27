module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Co1BMulSound

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Census
open CFSG.KC.Co1F2 (unpackR bind_sound)
open CFSG.KC.F2W (mulRows_unpackR vecMulN_unpackR vmF_lt)

private theorem stepK_eq_cub (d : Nat) : stepK d = CFSG.KC.LocalComp.Cub.stepK d := by
  funext R op
  cases op <;> rfl

private theorem expOK_eq_cub : expOK = CFSG.KC.LocalComp.Cub.expOK := by
  funext op
  cases op <;> rfl

private theorem runK_eq_cub (d A B n : Nat) (prog : List Op) :
    runK d A B n prog =
      prog.foldl (CFSG.KC.LocalComp.Cub.stepK d) (CFSG.KC.LocalComp.Cub.initK d A B n) := by
  unfold runK
  rw [stepK_eq_cub]
  rfl

private theorem regs_get {d A B n : Nat} {csA csB : List Char} {sA sB : String} {prog : List Op}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : sA = String.ofList csA) (hsB : sB = String.ofList csB)
    (hprog : prog.all (Op.lt n) = true) (hexp : prog.all expOK = true) {r : Nat} (hr : r < n) :
    ((ops2 d).run prog ((ops2 d).initRegs ((ops2 d).decode sA) ((ops2 d).decode sB) n))[r]! =
      unpackR d (getR d (runK d A B n prog) r) := by
  have eA : (ops2 d).decode sA = unpackR d A := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sA = _
    rw [hsA]
    exact bind_sound hA
  have eB : (ops2 d).decode sB = unpackR d B := by
    change CFSG.Sporadic.SmallF2.Native.rowsOfPayload d sB = _
    rw [hsB]
    exact bind_sound hB
  rw [eA, eB]
  have hinitlen : (CFSG.KC.LocalComp.Cub.initK d A B n).length = n := by
    simp [CFSG.KC.LocalComp.Cub.initK]
  have hinitsize : ((ops2 d).initRegs (unpackR d A) (unpackR d B) n).size = n := by
    simp [Ops.initRegs]
  have hexp' : prog.all CFSG.KC.LocalComp.Cub.expOK = true := by
    rw [← expOK_eq_cub]
    exact hexp
  have hmap := CFSG.KC.LocalComp.Cub.run_map hinitlen hinitsize
    (CFSG.KC.LocalComp.Cub.map_initK d A B n) hprog hexp'
  have hlen := CFSG.KC.LocalComp.Cub.length_stepK_foldl d n prog _ hinitlen
  have hsize := CFSG.KC.LocalComp.Cub.size_run d n prog _ hinitsize
  rw [runK_eq_cub]
  exact (CFSG.KC.LocalComp.Cub.getR_map hlen hsize hmap hr).symm

private theorem map_regs {d n : Nat} {Rl : List Nat} {Ra : Array (Array Nat)}
    (hreg : ∀ r < n, Ra[r]! = unpackR d (getR d Rl r)) {outs : List Nat}
    (hout : outs.all (decide <| · < n) = true) :
    (outs.map fun r => Ra[r]!) = (outs.map (getR d Rl)).map (unpackR d) := by
  rw [List.map_map]
  refine List.map_congr_left fun r hr => ?_
  exact hreg r (of_decide_eq_true (List.all_eq_true.1 hout r hr))

private theorem unpackR_mulF (d X Y : Nat) :
    unpackR d (mulF d X Y) = (ops2 d).mul (unpackR d X) (unpackR d Y) :=
  (mulRows_unpackR d X Y).symm

private theorem unpackR_idF_eq_one (d : Nat) : unpackR d (idF d) = (ops2 d).one :=
  CFSG.KC.LocalComp.Cub.unpackR_idF d

private theorem unpackR_powK {d X e : Nat} (he : e < 2 ^ 16) :
    unpackR d (powK d X e) = (ops2 d).pow (unpackR d X) e :=
  CFSG.KC.LocalComp.Cub.unpackR_powF16 he

private theorem unpackR_commMK {d r X Y : Nat} (hr : r - 1 < 2 ^ 16) :
    unpackR d (commMK d r X Y) = (ops2 d).commM r (unpackR d X) (unpackR d Y) := by
  unfold commMK Ops.commM
  rw [unpackR_mulF, unpackR_mulF, unpackR_mulF, unpackR_powK hr, unpackR_powK hr]

private theorem eq_of_beq {d X Y : Nat} (h : Nat.beq X Y = true) :
    (ops2 d).eq (unpackR d X) (unpackR d Y) = true :=
  CFSG.KC.LocalComp.Cub.ops2_eq_unpackR h

private theorem commOK_of_commK {d X Y : Nat} (h : commK d X Y = true) :
    (ops2 d).commOK (unpackR d X) (unpackR d Y) = true := by
  unfold commK at h
  unfold Ops.commOK
  rw [← unpackR_mulF, ← unpackR_mulF]
  exact eq_of_beq h

private theorem conjOK_of_conjK {d H X W : Nat} (h : conjK d H X W = true) :
    (ops2 d).conjOK (unpackR d H) (unpackR d X) (unpackR d W) = true := by
  unfold conjK at h
  unfold Ops.conjOK
  rw [← unpackR_mulF, ← unpackR_mulF]
  exact eq_of_beq h

private theorem vmul_unpackR (d X v : Nat) : (ops2 d).vmul v (unpackR d X) = vmF d X v :=
  vecMulN_unpackR d X v

private theorem unit_eq (d k : Nat) : (ops2 d).unit k = CFSG.KLie.CT.pw2 k := rfl

private theorem pw2_lt {d k : Nat} (hk : k < d) : CFSG.KLie.CT.pw2 k < 2 ^ d := by
  rw [show CFSG.KLie.CT.pw2 k = 2 ^ k from Nat.one_shiftLeft k]
  exact Nat.pow_lt_pow_right (by norm_num) hk

private theorem vne_of_beq {d u w : Nat} (hu : u < 2 ^ d) (hw : w < 2 ^ d)
    (h : (!Nat.beq u w) = true) : (ops2 d).vne u w = true := by
  rw [CFSG.KC.LocalComp.Cub.vne_eq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw]
  exact h

private theorem app_unpackR (d X : Nat) : ∀ n v : Nat,
    (ops2 d).app (unpackR d X) n v = appK d X n v
  | 0, _ => rfl
  | n + 1, v => by
    change (ops2 d).app (unpackR d X) n ((ops2 d).vmul v (unpackR d X)) =
      appK d X n (vmF d X v)
    rw [vmul_unpackR]
    exact app_unpackR d X n (vmF d X v)

private theorem appBase_unpackR (d b : Nat) : ∀ (xs : List Nat) (n v : Nat),
    (ops2 d).appBase b (xs.map (unpackR d)) n v = appBaseK d b xs n v
  | [], _, _ => rfl
  | X :: xs, n, v => by
    change (ops2 d).appBase b (xs.map (unpackR d)) (n / b)
        ((ops2 d).app (unpackR d X) (n % b) v) =
      appBaseK d b xs (n / b) (appK d X (n % b) v)
    rw [app_unpackR]
    exact appBase_unpackR d b xs (n / b) (appK d X (n % b) v)

private theorem appK_lt (d X : Nat) : ∀ n v : Nat, v < 2 ^ d → appK d X n v < 2 ^ d
  | 0, _, hv => hv
  | n + 1, v, _ => appK_lt d X n (vmF d X v) (vmF_lt d X v)

private theorem appBaseK_lt (d b : Nat) : ∀ (xs : List Nat) (n v : Nat), v < 2 ^ d →
    appBaseK d b xs n v < 2 ^ d
  | [], _, _, hv => hv
  | X :: xs, n, v, hv => appBaseK_lt d b xs (n / b) (appK d X (n % b) v) (appK_lt d X _ v hv)

private theorem appDigits_eq_appBase {M V : Type} (O : Ops M V) :
    ∀ (xs : List M) (n : Nat) (v : V), O.appDigits xs n v = O.appBase 3 xs n v
  | [], _, _ => rfl
  | X :: xs, n, v => by
    change O.appDigits xs (n / 3) (O.app X (n % 3) v) =
      O.appBase 3 xs (n / 3) (O.app X (n % 3) v)
    exact appDigits_eq_appBase O xs _ _

private theorem any_mono {α : Type} {l : List α} {p q : α → Bool}
    (hpq : ∀ a ∈ l, p a = true → q a = true) (h : l.any p = true) : l.any q = true := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨a, ha, hpq a ha hp⟩

private theorem vne_appBase {d b k : Nat} (hk : k < d) (xs : List Nat) (n : Nat)
    (h : (!Nat.beq (appBaseK d b xs n (CFSG.KLie.CT.pw2 k)) (CFSG.KLie.CT.pw2 k)) = true) :
    (ops2 d).vne ((ops2 d).appBase b (xs.map (unpackR d)) n ((ops2 d).unit k))
      ((ops2 d).unit k) = true := by
  rw [unit_eq, appBase_unpackR]
  exact vne_of_beq (appBaseK_lt d b xs n _ (pw2_lt hk)) (pw2_lt hk) h

private theorem vne_appBase_vmul {d b k : Nat} (hk : k < d) (xs : List Nat) (n T : Nat)
    (h : (!Nat.beq (appBaseK d b xs n (CFSG.KLie.CT.pw2 k))
      (vmF d T (CFSG.KLie.CT.pw2 k))) = true) :
    (ops2 d).vne ((ops2 d).appBase b (xs.map (unpackR d)) n ((ops2 d).unit k))
      ((ops2 d).vmul ((ops2 d).unit k) (unpackR d T)) = true := by
  rw [unit_eq, appBase_unpackR, vmul_unpackR]
  exact vne_of_beq (appBaseK_lt d b xs n _ (pw2_lt hk)) (vmF_lt d T _) h

private theorem commsModOK_of_K {d T : Nat} : ∀ xs : List Nat, commsModK d T xs = true →
    (ops2 d).commsModOK (unpackR d T) (xs.map (unpackR d)) = true
  | [], _ => rfl
  | X :: xs, h => by
    change (xs.all (fun Y => Nat.beq (mulF d X Y) (mulF d Y X) ||
      Nat.beq (mulF d X Y) (mulF d T (mulF d Y X))) && commsModK d T xs) = true at h
    rw [Bool.and_eq_true] at h
    change ((xs.map (unpackR d)).all ((ops2 d).commModOK (unpackR d T) (unpackR d X)) &&
      (ops2 d).commsModOK (unpackR d T) (xs.map (unpackR d))) = true
    rw [Bool.and_eq_true, List.all_map]
    refine ⟨List.all_eq_true.2 fun Y hY => ?_, commsModOK_of_K xs h.2⟩
    have hY := List.all_eq_true.1 h.1 Y hY
    simp only [Bool.or_eq_true] at hY
    simp only [Function.comp_apply, Ops.commModOK, Bool.or_eq_true]
    simp only [← unpackR_mulF]
    rcases hY with hY | hY
    · exact Or.inl (eq_of_beq hY)
    · exact Or.inr (eq_of_beq hY)

private theorem secOK_of_K {d T : Nat} {xs tests : List Nat}
    (htests : ∀ k ∈ tests, k < d)
    (hTT : Nat.beq (mulF d T T) (idF d) = true)
    (hxs : xs.all (fun X => Nat.beq (mulF d X T) (mulF d T X) &&
      (Nat.beq (mulF d X X) (idF d) || Nat.beq (mulF d X X) T)) = true)
    (hcomm : commsModK d T xs = true)
    (hker : ((List.range (2 ^ xs.length - 1)).all fun n =>
      tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (CFSG.KLie.CT.pw2 k))
        (CFSG.KLie.CT.pw2 k)) &&
      tests.any (fun k => !Nat.beq (appBaseK d 2 xs (n + 1) (CFSG.KLie.CT.pw2 k))
        (vmF d T (CFSG.KLie.CT.pw2 k)))) = true) :
    (ops2 d).secOK (unpackR d T) (xs.map (unpackR d)) tests = true := by
  unfold Ops.secOK
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, commsModOK_of_K xs hcomm⟩, ?_⟩
  · rw [← unpackR_mulF, ← unpackR_idF_eq_one]
    exact eq_of_beq hTT
  · rw [List.all_map]
    refine List.all_eq_true.2 fun X hX => ?_
    have h := List.all_eq_true.1 hxs X hX
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    simp only [Function.comp_apply, Ops.inN, Bool.and_eq_true, Bool.or_eq_true]
    simp only [← unpackR_mulF, ← unpackR_idF_eq_one]
    refine ⟨eq_of_beq h.1, ?_⟩
    rcases h.2 with h2 | h2
    · exact Or.inl (eq_of_beq h2)
    · exact Or.inr (eq_of_beq h2)
  · unfold Ops.kerModOK
    rw [List.length_map]
    refine List.all_eq_true.2 fun n hn => ?_
    have h := List.all_eq_true.1 hker n hn
    rw [Bool.and_eq_true] at h
    unfold Ops.outsideN
    rw [Bool.and_eq_true]
    exact ⟨any_mono (fun k hk hp => vne_appBase (htests k hk) xs (n + 1) hp) h.1,
      any_mono (fun k hk hp => vne_appBase_vmul (htests k hk) xs (n + 1) T hp) h.2⟩

theorem secCheck_of_K {d A B : Nat} {csA csB : List Char} {D : SecData}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : secK d A B D = true) : (ops2 d).secCheck D = true := by
  simp only [secK, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hout, htR, htests, hTT, hxs, hcomm, hker⟩ := h
  have hreg : ∀ r < D.nregs, ((ops2 d).run D.prog ((ops2 d).initRegs ((ops2 d).decode D.seedA)
      ((ops2 d).decode D.seedB) D.nregs))[r]! =
        unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  have htk : ∀ k ∈ D.tests, k < d := fun k hk =>
    of_decide_eq_true (List.all_eq_true.1 htests k hk)
  unfold Ops.secCheck
  dsimp only
  rw [hreg _ htR, map_regs hreg hout]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨hn, hprog, hout, htR, secOK_of_K htk hTT hxs hcomm hker⟩

private theorem commsOK_of_K {d : Nat} : ∀ xs : List Nat, commsK d xs = true →
    (ops2 d).commsOK (xs.map (unpackR d)) = true
  | [], _ => rfl
  | X :: xs, h => by
    change (xs.all (commK d X) && commsK d xs) = true at h
    rw [Bool.and_eq_true] at h
    change ((xs.map (unpackR d)).all ((ops2 d).commOK (unpackR d X)) &&
      (ops2 d).commsOK (xs.map (unpackR d))) = true
    rw [Bool.and_eq_true, List.all_map]
    refine ⟨List.all_eq_true.2 fun Y hY => ?_, commsOK_of_K xs h.2⟩
    simp only [Function.comp_apply]
    exact commOK_of_commK (List.all_eq_true.1 h.1 Y hY)

private theorem elemOK_of_K {d : Nat} {xs tests : List Nat}
    (htests : ∀ k ∈ tests, k < d)
    (hcube : xs.all (fun X => Nat.beq (mulF d (mulF d X X) X) (idF d)) = true)
    (hcomms : commsK d xs = true)
    (hker : ((List.range (3 ^ xs.length - 1)).all fun n =>
      tests.any fun k => !Nat.beq (appBaseK d 3 xs (n + 1) (CFSG.KLie.CT.pw2 k))
        (CFSG.KLie.CT.pw2 k)) = true) :
    (ops2 d).elemOK (xs.map (unpackR d)) tests = true := by
  unfold Ops.elemOK
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, commsOK_of_K xs hcomms⟩, ?_⟩
  · rw [List.all_map]
    refine List.all_eq_true.2 fun X hX => ?_
    simp only [Function.comp_apply, Ops.cubeOK]
    simp only [← unpackR_mulF, ← unpackR_idF_eq_one]
    exact eq_of_beq (List.all_eq_true.1 hcube X hX)
  · unfold Ops.kerOK
    rw [List.length_map]
    refine List.all_eq_true.2 fun n hn => ?_
    refine any_mono (fun k hk hp => ?_) (List.all_eq_true.1 hker n hn)
    unfold Ops.moved
    rw [appDigits_eq_appBase]
    exact vne_appBase (htests k hk) xs (n + 1) hp

theorem w4Check_of_K {d A B : Nat} {csA csB : List Char} {D : W4Data}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.base.seedA = String.ofList csA) (hsB : D.base.seedB = String.ofList csB)
    (h : w4K d A B D.base D.inv = true) : W4Data.check (ops2 d) D = true := by
  simp only [w4K, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hout, hinv, htests, hcube, hcomms, hker, hTT, hmove,
    hcommT⟩ := h
  have hreg : ∀ r < D.base.nregs, ((ops2 d).run D.base.prog ((ops2 d).initRegs
      ((ops2 d).decode D.base.seedA) ((ops2 d).decode D.base.seedB) D.base.nregs))[r]! =
        unpackR d (getR d (runK d A B D.base.nregs D.base.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  have htk : ∀ k ∈ D.base.tests, k < d := fun k hk =>
    of_decide_eq_true (List.all_eq_true.1 htests k hk)
  unfold W4Data.check
  dsimp only
  rw [hreg _ hinv, map_regs hreg hout]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hprog, hout, hinv, elemOK_of_K htk hcube hcomms hker, ?_, ?_, ?_⟩
  · rw [← unpackR_mulF, ← unpackR_idF_eq_one]
    exact eq_of_beq hTT
  · refine any_mono (fun k hk hp => ?_) hmove
    rw [unit_eq, vmul_unpackR]
    exact vne_of_beq (vmF_lt d _ _) (pw2_lt (htk k hk)) hp
  · refine List.all_eq_true.2 fun r hr => ?_
    have hr' : r < D.base.nregs := of_decide_eq_true (List.all_eq_true.1 hout r hr)
    rw [hreg r hr']
    exact commOK_of_commK (List.all_eq_true.1 hcommT r hr)

private theorem normOK_of_K {d n : Nat} {N : Cub2NormData} {Rl : List Nat}
    {Ra : Array (Array Nat)} (hreg : ∀ r < n, Ra[r]! = unpackR d (getR d Rl r)) {X Y Z : Nat}
    (h : normK d N n Rl X Y Z = true) :
    (ops2 d).normOK N n Ra (unpackR d X) (unpackR d Y) (unpackR d Z) = true := by
  simp only [normK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hrh, hoh, hsmall, hH, hcX, hcY⟩ := h
  have hb : ∀ x ∈ [N.oh, N.a, N.b, N.c, N.d, N.k, N.l], x < 2 ^ 16 := fun x hx =>
    lt_of_lt_of_le (of_decide_eq_true (List.all_eq_true.1 hsmall x hx)) (by norm_num)
  unfold Ops.normOK
  rw [hreg _ hrh]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hrh, hoh, ?_, ?_, ?_⟩
  · rw [← unpackR_powK (hb N.oh (by simp)), ← unpackR_idF_eq_one]
    exact eq_of_beq hH
  · rw [← unpackR_powK (hb N.a (by simp)), ← unpackR_powK (hb N.b (by simp)),
      ← unpackR_powK (hb N.k (by simp)), ← unpackR_mulF, ← unpackR_mulF]
    exact conjOK_of_conjK hcX
  · rw [← unpackR_powK (hb N.c (by simp)), ← unpackR_powK (hb N.d (by simp)),
      ← unpackR_powK (hb N.l (by simp)), ← unpackR_mulF, ← unpackR_mulF]
    exact conjOK_of_conjK hcY

theorem cub2Check_of_K {d A B : Nat} {csA csB : List Char} {D : Cub2Data}
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true)
    (hsA : D.seedA = String.ofList csA) (hsB : D.seedB = String.ofList csB)
    (h : cub2K d A B D = true) : (ops2 d).cub2Check D = true := by
  simp only [cub2K, seedsOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨-, -, -, hexp, hn, hprog, hrx, hry, hr0, hr16, ht, hXr, hYr, hZt, hZX, hZY, hN1,
    hN2⟩ := h
  have hr16' : D.r < 2 ^ 16 := lt_of_lt_of_le hr16 (by norm_num)
  have hrm1 : D.r - 1 < 2 ^ 16 := by omega
  have hreg : ∀ r < D.nregs, ((ops2 d).run D.prog ((ops2 d).initRegs ((ops2 d).decode D.seedA)
      ((ops2 d).decode D.seedB) D.nregs))[r]! =
        unpackR d (getR d (runK d A B D.nregs D.prog) r) :=
    fun r hr => regs_get hA hB hsA hsB hprog hexp hr
  unfold Ops.cub2Check Ops.regsOf
  dsimp only
  rw [hreg _ hrx, hreg _ hry, ← unpackR_commMK hrm1]
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨hn, hprog, hrx, hry, hr0, ?_, ?_, ?_, ?_, ?_, normOK_of_K hreg hN1,
    normOK_of_K hreg hN2⟩
  · rw [← unpackR_powK hr16', ← unpackR_idF_eq_one]
    exact eq_of_beq hXr
  · rw [← unpackR_powK hr16', ← unpackR_idF_eq_one]
    exact eq_of_beq hYr
  · rw [unit_eq, vmul_unpackR]
    exact vne_of_beq (vmF_lt d _ _) (pw2_lt ht) hZt
  · rw [← unpackR_mulF, ← unpackR_mulF]
    exact eq_of_beq hZX
  · rw [← unpackR_mulF, ← unpackR_mulF]
    exact eq_of_beq hZY

end CFSG.KC.OpsF2K

end
