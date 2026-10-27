module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WPGL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WTransport

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank

theorem ivk93w_l5 : ∀ p f : ℕ, p.Prime → 1 ≤ f → p ^ f % 4 = 3 →
    Ivk93WEmpty (fun X _ => LieModel X .PSL 5 p f) := by
  intro p f hp hf hmod J _ _ hJ x q B h _
  obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hJ
  have hodd : Odd (Nat.card F) := by rw [hF]; exact Nat.odd_iff.mpr (by omega)
  have : Finite (StatedProj (StatedSL 5 F)) := Finite.of_equiv _ e.toEquiv
  exact (h.of_equiv e).false_of_psl_four_five hodd (Or.inr rfl)

end CFSG.GH74.GLS.IVK.Proofs2
