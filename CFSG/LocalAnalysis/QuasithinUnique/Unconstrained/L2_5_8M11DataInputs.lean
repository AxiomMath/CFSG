module

public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Schreier.Enumeration

public section

namespace CFSG.QuasithinUnique.Unc25M11
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu

@[expose] def pw (l : List ℕ) : Equiv.Perm (Fin 11) :=
  tab ((l.map fun i => if i = 0 then m11gA else m11gB).prod)

@[expose] def sa : Equiv.Perm (Fin 11) := pw [0, 1, 1, 0, 1, 0, 1, 1]

@[expose] def sb : Equiv.Perm (Fin 11) := pw [0]

@[expose] def P0L : List (Equiv.Perm (Fin 11)) :=
  (List.range 8).flatMap fun i => (List.range 2).map fun j => tab (sa ^ i * sb ^ j)

@[expose] def invsP0 : List (Equiv.Perm (Fin 11)) := P0L.filter fun x => decide (x ≠ 1 ∧ x * x = 1)

@[expose] def NormProp (g : Equiv.Perm (Fin 11)) : Prop :=
  g * sa * g⁻¹ ∈ P0L → g * sb * g⁻¹ ∈ P0L → g ∈ P0L

instance (g : Equiv.Perm (Fin 11)) : Decidable (NormProp g) := by
  unfold NormProp
  infer_instance

@[expose] def centB (g : Equiv.Perm (Fin 11)) : Bool :=
  invsP0.all fun t => invsP0.all fun s =>
    decide (g * t = t * g → g * s = s * g → t ≠ s → t * s = s * t →
      g = 1 ∨ g = t ∨ g = s ∨ g = t * s)

end CFSG.QuasithinUnique.Unc25M11
