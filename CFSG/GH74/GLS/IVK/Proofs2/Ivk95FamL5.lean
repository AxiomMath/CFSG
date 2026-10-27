module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95LinFam

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG.Blueprint

theorem ivk95_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk95Empty (fun X _ => LieModel X .PSL 5 p f) := fun _ _ _ _ hmod =>
  ivk95l_empty_psl (Or.inr rfl) (Nat.odd_iff.2 (by omega))

end CFSG.GH74.GLS.IVK.Proofs2
