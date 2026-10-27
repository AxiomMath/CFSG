module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.BenderSuzuki

open Matrix

universe u

@[expose] def IsStronglyEmbeddedOrder {X : Type u} [Group X] (M : Subgroup X) : Prop :=
  M ≠ ⊤ ∧ Even (Nat.card M) ∧
    ∀ g ∉ M, Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup X)))

abbrev PSL2Model (n : ℕ) := CFSG.Theory.Comparator.PSL2Model n

abbrev SzGenerators (n : ℕ) : Set (Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1))) :=
  CFSG.Theory.Comparator.SzGenerators n

noncomputable abbrev SzModel (n : ℕ) : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))) :=
  CFSG.Theory.Comparator.SzModel n

noncomputable abbrev PSU3Model (n : ℕ) :
    Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * n))) :=
  CFSG.Theory.Comparator.PSU3Model n

inductive IsBenderGroup (G : Type u) [Group G] : Prop
  | isPSL2 (n : ℕ) (_ : 2 ≤ n) (e : G ≃* PSL2Model n)
  | isSuzuki (n : ℕ) (_ : 1 ≤ n) (e : G ≃* SzModel n)
  | isPSU3 (n : ℕ) (_ : 2 ≤ n) (e : G ≃* PSU3Model n)

end CFSG.BenderSuzuki
