module

public import Certificates.Data.Kernel.LocalQT.Pipe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
import CFSG.Certificates.Kernel.LocalQTPipeEdge
import CFSG.Certificates.Kernel.LocalQTPipeCoset

public section

namespace CFSG.KC.LQT.PP

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm

theorem slpOKK_spec (prog : List (Nat × Nat)) (m : Nat) (h : slpOKK prog m = true) :
    slpValidAux prog m = true := by
  induction prog generalizing m with
  | nil => simp [slpValidAux]
  | cons p rest ih =>
    have h' : CFSG.KC.Ord.andB (CFSG.KC.Ord.andB (Nat.blt p.1 m) (Nat.blt p.2 m)) (slpOKK rest (Nat.succ m)) = true := h
    have e : ∀ a b : Bool, CFSG.KC.Ord.andB a b = (a && b) := by intro a b; cases a <;> cases b <;> rfl
    simp only [e, Bool.and_eq_true, Nat.blt_eq] at h'
    simp only [slpValidAux, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h'.1.1, h'.1.2⟩, ih (m + 1) h'.2⟩

theorem tree_sound (N : Nat) (ps gs : Array (Array Nat))
    (h : treeK N (chunksK ps) (chunksK gs) = true) :
    treeValid N (Array.flatten ps) (Array.flatten gs) := by
  exact PPB.tree_sound N ps gs h

theorem inv_sound {n w : Nat} (hw : n ≤ 2 ^ w) (a b ai bi : Array (Array Nat))
    (h : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true) :
    invValid n (Array.flatten a) (Array.flatten b) (Array.flatten ai) (Array.flatten bi) := by
  exact PPB.inv_sound hw a b ai bi h

theorem asz_sound (N : Nat) (a b : Array (Array Nat)) (h : aszK N (chunksK a) (chunksK b) = true) :
    aszOK N (Array.flatten a) (Array.flatten b) := by
  exact PPB.asz_sound N a b h

theorem xs_sound (N : Nat) (xs : Array (List Nat)) (h : xsK N xs.toList = true) : xsOK N xs := by
  exact PPB.xs_sound N xs h

theorem enum_sound {n w : Nat} (hw : n ≤ 2 ^ w) (a b : Array (Array Nat)) (prog qp : List (Nat × Nat))
    (k fuel d : Nat) (RL : List Nat)
    (h : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true) :
    qpOK n (slpTabsA (Array.flatten a) (Array.flatten b) prog) qp ∧
    BaseEnumOK n (List.range n)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
      (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!)
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.1
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).2.2 ∧
    (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!)
        fuel).1.size = 2 ^ k := by
  exact PPE.enum_sound hw a b prog qp k fuel d RL h

theorem edge_sound {n w W N : Nat} (hw : n ≤ 2 ^ w) (hW : N ≤ 2 ^ W)
    (a b ai bi Aa Ab ps gs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (k fuel d : Nat)
    (RL : List Nat) (RF : Nat → Nat) (AK BK PK GK K L : Nat)
    (hinv : invK n w (chunksK a) (chunksK b) (chunksK ai) (chunksK bi) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hat : tabL N (chunksK Aa) = true) (hbt : tabL N (chunksK Ab) = true)
    (hen : enumK n w (chunksK a) (chunksK b) prog qp k fuel d RL = true)
    (hAK : Nat.beq (codeK W (chunksK Aa)) AK = true) (hBK : Nat.beq (codeK W (chunksK Ab)) BK = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PK = true) (hGK : Nat.beq (codeK W (chunksK gs)) GK = true)
    (hKL : K * L = N)
    (he : ∀ c < K, edgeChunk n w W N (codeK w (chunksK a)) (codeK w (chunksK b)) AK BK PK GK RF
      (treeOf RL) (c * L) L = true) :
    edgeOK n N (ptsOf (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!))
      (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1
      (keyMap n (bfsEnumB n (List.range n)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.1]!)
        (qp.map fun p => (slpTabsA (Array.flatten a) (Array.flatten b) prog)[p.2]!) fuel).1)
      (Array.flatten a) (Array.flatten b) (Array.flatten Aa) (Array.flatten Ab)
      (treeTabs n N (Array.flatten a) (Array.flatten b) (Array.flatten ps) (Array.flatten gs))
      (treeInvTabs n N (Array.flatten ai) (Array.flatten bi) (Array.flatten ps)
        (Array.flatten gs)) = true := by
  exact PPEd.edge_sound hw hW a b ai bi Aa Ab ps gs prog qp k fuel d RL RF AK BK PK GK K L hinv htree
    hpt hgt hat hbt hen hAK hBK hPK hGK hKL he

theorem coset_sound {N W : Nat} (hW : N ≤ 2 ^ W) (hN : 0 < N)
    (Aa Ab ps gs rs : Array (Array Nat)) (prog qp : List (Nat × Nat)) (xs : Array (List Nat))
    (TF MF : Nat → Nat) (SL ML REPS OML BM : List Nat) (BWL PWL : List (List Nat))
    (PRK GNK RPK RIK QPK QGK DPK h₁ h₂ KS KM KR LR KB KP : Nat)
    (hA : permK N (chunksK Aa) = true) (hB : permK N (chunksK Ab) = true)
    (h0 : Nat.beq (codeK W (chunksK Aa)) (TF 0) = true)
    (h1 : Nat.beq (codeK W (chunksK Ab)) (TF 1) = true)
    (htree : treeK N (chunksK ps) (chunksK gs) = true)
    (hpt : tabL N (chunksK ps) = true) (hgt : tabL N (chunksK gs) = true)
    (hrt : tabL N (chunksK rs) = true)
    (hPK : Nat.beq (codeK W (chunksK ps)) PRK = true)
    (hGK : Nat.beq (codeK W (chunksK gs)) GNK = true)
    (hRK : Nat.beq (codeK W (chunksK rs)) RPK = true)
    (hso : slpOKK prog 2 = true) (hsn : slpNeedK prog SL = true)
    (hq : allA qp (fun p => anyL SL (Nat.beq p.1)) = true)
    (hKS : lenA SL = KS) (hs : ∀ c < KS, slpChk N W TF prog (getK SL c) = true)
    (hid : idK N W (MF 0) = true) (hM : needP W PRK ML = true)
    (hKM : lenA ML = KM) (hm : ∀ c < KM, omChk N W TF MF PRK GNK (getK ML c) = true)
    (hRM : allL REPS (fun x => CFSG.KC.Ord.orB (Nat.beq x 0) (anyL ML (Nat.beq x))) = true)
    (hXM : allA xs.toList (fun l => allL l fun x => CFSG.KC.Ord.orB (Nat.beq x 0) (anyL ML (Nat.beq x))) =
      true)
    (hrs : repsSumK N REPS OML = true) (hKR : KR * LR = N)
    (hr : ∀ c < KR, repsChunk N W (qpK TF qp) RPK RIK QPK QGK DPK REPS OML (c * LR) LR = true)
    (hKB : xs.size = KB) (hBL : lenA BM = KB)
    (hb : ∀ h < KB, blockK N W (qpK TF qp) MF RPK REPS BM BWL xs.toList h = true)
    (hKP : KB * lenA REPS = KP)
    (hp : ∀ i < KP, pairK N W (qpK TF qp) MF RPK REPS BM PWL xs.toList i = true)
    (hsh : shapeK N BM h₁ h₂ = true) :
    blocksClosed (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs) ∧
      repsOK (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten rs) (repList N (Array.flatten rs))
        (repOrbs (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (repList N (Array.flatten rs))) ∧
      closureOK (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
        (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs)
        (repList N (Array.flatten rs)) ∧
      shapeOK N
        (blocksOf (qp.map fun p => (slpTabsA (Array.flatten Aa) (Array.flatten Ab) prog)[p.1]!) N
          (Array.flatten Aa) (Array.flatten Ab) (Array.flatten ps) (Array.flatten gs) xs) := by
  exact PPC.coset_sound hW hN Aa Ab ps gs rs prog qp xs TF MF SL ML REPS OML BM BWL PWL PRK GNK RPK
    RIK QPK QGK DPK h₁ h₂ KS KM KR LR KB KP hA hB h0 h1 htree hpt hgt hrt hPK hGK hRK hso hsn hq hKS hs
    hid hM hKM hm hRM hXM hrs hKR hr hKB hBL hb hKP hp hsh

end CFSG.KC.LQT.PP

end
