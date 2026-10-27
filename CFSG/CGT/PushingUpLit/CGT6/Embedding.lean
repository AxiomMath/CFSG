module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS6.Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne
open CFSG.Assembly (KProper InCatalog)
open CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Hol

variable (V : Type) [CommGroup V]

abbrev Hol : Type := SemidirectProduct V (MulAut V) (MonoidHom.id (MulAut V))

variable {V}

instance [Finite V] : Finite (Hol V) :=
  Finite.of_equiv (V × MulAut V) SemidirectProduct.equivProd.symm

@[expose] def yuHol (Y : Subgroup (MulAut V)) : Subgroup (Hol V) where
  carrier := {x | x.left ∈ commV Y ∧ x.right ∈ Y}
  one_mem' := ⟨one_mem _, one_mem _⟩
  mul_mem' := by
    rintro ⟨a, α⟩ ⟨b, β⟩ ⟨ha, hα⟩ ⟨hb, hβ⟩
    refine ⟨?_, Y.mul_mem hα hβ⟩
    exact mul_mem ha (G6.apply_mem_commV (fun x hx => by
      have := Y.mul_mem (Y.mul_mem hα hx) (Y.inv_mem hα)
      exact this) hb)
  inv_mem' := by
    rintro ⟨a, α⟩ ⟨ha, hα⟩
    refine ⟨?_, Y.inv_mem hα⟩
    have h1 : α⁻¹ a⁻¹ ∈ commV Y := G6.apply_mem_commV (fun x hx => by
      have := Y.mul_mem (Y.mul_mem (Y.inv_mem hα) hx) hα
      simpa using this) (inv_mem ha)
    exact h1

end Hol

end CFSG.CGT.PushingUpLit.CGT6
