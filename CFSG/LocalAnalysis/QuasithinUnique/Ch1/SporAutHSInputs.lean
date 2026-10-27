module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Schreier.PairHSCert

public noncomputable section

namespace CFSG.QuasithinUnique.Ch1.SporAutHS
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Blueprint

@[expose] def s0Hex : String := include_str "SporAutHSData.txt"

@[expose] def s0Arr (j : ℕ) : Array ℕ := hexTable 4 3850 (3850 * j) s0Hex

@[expose] def s0Strong : Array (Array ℕ) :=
  #[hsStrongArrs[0]!, s0Arr 0, s0Arr 1, s0Arr 2]

@[expose] def s0BaseFin : List (Fin 3850) := [0]

@[expose] def s0BaseArr : Array ℕ := (s0BaseFin.map Fin.val).toArray

@[expose] def s0Words : Array (List ℤ) := #[[], [], [], []]

@[expose] def s0Chain : RawSchreierDatum 3850 :=
  RawSchreierDatum.ofArrays 3850 (by decide) s0Strong 4 (by simp [s0Strong]) s0BaseFin
    (by decide) s0Words

@[expose] def hsLtr (k : ℕ) : Equiv.Perm (Fin 3850) :=
  if k < 4 then permOfArr 3850 s0Strong[k]! else hsGen 1

@[expose] def wordElt (w : List ℕ) : Equiv.Perm (Fin 3850) := (w.map hsLtr).prod

@[expose] def bWord : List ℕ := [4, 4, 0, 4, 4, 4, 0, 4, 4]

@[expose] def yWord : List ℕ := [1, 1, 2, 3, 2, 2, 2]

@[expose] def l1Word : List ℕ := [1, 1, 2, 3, 2, 3]

@[expose] def l2Word : List ℕ := [3, 1]

@[expose] def t0Word : List ℕ := [3, 1, 2]

@[expose] def t1Word : List ℕ := [1, 1, 3, 3]

@[expose] def t2Word : List ℕ := [0, 2, 2, 2, 1, 2]

end CFSG.QuasithinUnique.Ch1.SporAutHS
