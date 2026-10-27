module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinFam

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk95_l4 : ∀ p f : ℕ, p.Prime → p ≠ 2 → 1 ≤ f → p ^ f % 8 ≠ 1 →
    Ivk95Empty (fun X _ => LieModel X .PSL 4 p f) := fun _ _ hp hp2 _ _ =>
  ivk95l_empty_psl (Or.inl rfl) ((hp.odd_of_ne_two hp2).pow)

end CFSG.GH74.GLS.IVK.Proofs2
