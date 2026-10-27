module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM24Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporBFS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs
open scoped Pointwise
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

abbrev X24 : Type := ↥NativeSporadic.M24

@[expose] def enc (x : X24) : ℕ := encPerm x.1

@[expose] def hkey (x : X24) : ℕ := enc x % 2305843009213693951

@[expose] def tabX (x : X24) : X24 := ⟨tab x.1, by rw [tab_eq]; exact x.2⟩

@[expose] def evalW {G : Type*} [Group G] (S : List G) : List ℤ → G
  | [] => 1
  | z :: w =>
    (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * evalW S w

@[expose] def genX (w : List ℤ) : X24 := tabX (evalW [m24a, m24b] w)

@[expose] def s0gen : List X24 := s0Words.map genX

@[expose] def S0X : List X24 := closureListH tabX hkey s0gen 40

@[expose] def A1X : List X24 :=
  S0X.filter fun x => s0gen.all fun s => enc (s * x) == enc (x * s)

@[expose] def Z2X : List X24 :=
  S0X.filter fun y => s0gen.all fun s => (A1X.map enc).contains (enc (y * s * y⁻¹ * s⁻¹))

@[expose] def A2X : List X24 := S0X.filter fun x => Z2X.all fun y => enc (y * x) == enc (x * y)

@[expose] def a2gen : List X24 := S0X.filter fun x => (a2Perms.map encPerm).contains (enc x)

@[expose] def A2cl : List X24 := closureListH tabX hkey a2gen 40

@[expose] def t1X : X24 := genX (tWords.getD 0 [])

@[expose] def t3X : X24 := genX (tWords.getD 1 [])

@[expose] def k1gen : List X24 := s0gen ++ [t1X]

@[expose] def K1X : List X24 := closureListH tabX hkey k1gen 60

@[expose] def zX : X24 := (A1X.filter fun x => enc x != enc 1).headD 1

@[expose] def gensC : List (ConjAct X24) := [ConjAct.toConjAct m24a, ConjAct.toConjAct m24b]

@[expose] def classRes : List X24 × List ℕ × List ℕ := bfsOrbit tabX hkey gensC zX 20000

@[expose] def orbL (A : List X24) (i : Fin 24) : Finset (Fin 24) :=
  (A.map fun a => a.1 i).toFinset

@[expose] def trio : Finset (Finset (Fin 24)) := ((List.finRange 24).map (orbL A2X)).toFinset

@[expose] def maskF (B : Finset (Fin 24)) : ℕ := ∑ i ∈ B, 2 ^ i.val

@[expose] def encTrio (τ : Finset (Finset (Fin 24))) : List ℕ := (τ.image maskF).sort (· ≤ ·)

@[expose] def encTrioN (τ : Finset (Finset (Fin 24))) : ℕ :=
  (encTrio τ).foldl (fun acc m => acc * 2 ^ 24 + m) 0

@[expose] def gensA : List X24 := [m24a, m24b]

@[expose] def trioRes : List (Finset (Finset (Fin 24))) × List ℕ × List ℕ :=
  bfsOrbit id encTrio gensA trio 10000

@[expose] def tgen : List X24 := s0gen ++ [t3X]

@[expose] def T0X : List X24 := closureListH tabX hkey tgen 60

@[expose] def t2X : X24 := (T0X.filter fun x => enc x == encPerm (t2Perm.headD 1)).headD 1

@[expose] def k2gen : List X24 := s0gen ++ [t2X]

@[expose] def K2X : List X24 := closureListH tabX hkey k2gen 60

@[expose] def T0N : List X24 := T0X.filter (nrmTestGens enc (A2X.map enc) a2gen)

@[expose] def q1gen : List X24 := S0X.filter fun x => (q1Perms.map encPerm).contains (enc x)

@[expose] def Q1X : List X24 := closureListH tabX hkey q1gen 40

end CFSG.QuasithinUnique.Vol2Native.L239.M24Pairs
