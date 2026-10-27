module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporM12Data
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHash
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

abbrev X12 : Type := ↥NativeSporadic.M12

@[expose] def enc (x : X12) : List ℕ := (List.finRange 12).map fun i => (x.1 i).val

@[expose] def tabX (x : X12) : X12 := ⟨tab x.1, by rw [tab_eq]; exact x.2⟩

@[expose] def evalW {G : Type*} [Group G] (S : List G) : List ℤ → G
  | [] => 1
  | z :: w =>
    (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) * evalW S w

@[expose] def genX (w : List ℤ) : X12 := tabX (evalW [m12a, m12b] w)

@[expose] def s0gen : List X12 := s0Words.map genX

@[expose] def S0X : List X12 := closureList tabX enc s0gen 6

@[expose] def A1X : List X12 := S0X.filter fun x => S0X.all fun s => s * x == x * s

@[expose] def A2X : List X12 :=
  S0X.filter fun x => S0X.all fun s => S0X.all fun t =>
    (s * t * s⁻¹ * t⁻¹) * x == x * (s * t * s⁻¹ * t⁻¹)

@[expose] def nrmTest (A : List X12) (EA : List (List ℕ)) (pre : List X12) (g : X12) : Bool :=
  pre.all (fun a => decide (enc (g * a * g⁻¹) ∈ EA)) &&
    A.all (fun a => decide (enc (g * a * g⁻¹) ∈ EA) && decide (enc (g⁻¹ * a * g) ∈ EA))

@[expose] def encP (g : Equiv.Perm (Fin 12)) : List ℕ := (List.finRange 12).map fun i => (g i).val

@[expose] def nrmTestP (A : List X12) (EA : List (List ℕ)) (pre : List X12)
    (g : Equiv.Perm (Fin 12)) : Bool :=
  pre.all (fun a => decide (encP (g * a.1 * g⁻¹) ∈ EA)) &&
    A.all (fun a => decide (encP (g * a.1 * g⁻¹) ∈ EA) && decide (encP (g⁻¹ * a.1 * g) ∈ EA))

@[expose] def K1X : List X12 :=
  closureList tabX enc (s0gen ++ [genX (tWords.getD 0 [])]) 6

@[expose] def K2X : List X12 :=
  closureList tabX enc (s0gen ++ [genX (tWords.getD 1 [])]) 6

@[expose] def Q1X : List X12 := closureList tabX enc (q1Words.map genX) 5

@[expose] def Q2X : List X12 := closureList tabX enc (q2Words.map genX) 7

end CFSG.QuasithinUnique.Vol2Native.L239.M12Pairs
