module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TData

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint

@[expose] def m24Bas (ws : List (List Int)) : List S24 := ws.map (evalN NativeSporadic.M24 m24rg)

@[expose] def m24Elt (B : List S24) (n : ℕ) : S24 :=
  (List.range 6).foldl (fun acc k => if n.testBit k then acc * B.getD k 1 else acc) 1

@[expose] def m24Lst (B : List S24) : List S24 := (List.range 64).map (m24Elt B)

@[expose] def m24E1B : List S24 := m24Bas m24E1Bw

@[expose] def m24E2B : List S24 := m24Bas m24E2Bw

@[expose] def m24E1l : List S24 := m24Lst m24E1B

@[expose] def m24E2l : List S24 := m24Lst m24E2B

@[expose] def m24Cj (w : List Int) : S24 := evalN NativeSporadic.M24 [m24a, m24b] w

@[expose] def m24Gens18 (B : List S24) (g₂ g₃ : S24) : List S24 :=
  B ++ B.map (fun x => g₂ * x * g₂⁻¹) ++ B.map (fun x => g₃ * x * g₃⁻¹)

@[expose] def slpLetter {G : Type*} [Group G] (regs : List G) (z : Int) : G :=
  if z = 0 then 1 else if 0 < z then regs.getD (z.toNat - 1) 1
    else (regs.getD ((-z).toNat - 1) 1)⁻¹

@[expose] def slpEval {G : Type*} [Group G] (norm : G → G) (gens : List G)
    (prog : List (Int × Int)) : List G :=
  prog.foldl (fun regs pq => regs ++ [norm (slpLetter regs pq.1 * slpLetter regs pq.2)]) gens

@[expose] def AdjData (B : List S24) (g : S24) (p : ℕ × ℕ) : Prop :=
  p.1 < 64 ∧ p.2 < 64 ∧ m24Elt B p.1 ≠ 1 ∧ m24Elt B p.2 ≠ 1 ∧ m24Elt B p.1 ≠ m24Elt B p.2 ∧
    g⁻¹ * m24Elt B p.1 * g ∈ m24Lst B ∧ g⁻¹ * m24Elt B p.2 * g ∈ m24Lst B

instance (B : List S24) (g : S24) (p : ℕ × ℕ) : Decidable (AdjData B g p) := by
  unfold AdjData
  infer_instance

end CFSG.QuasithinUnique.Setup.X1
